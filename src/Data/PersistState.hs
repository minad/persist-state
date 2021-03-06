{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.PersistState (

    -- * The Persist class
      Persist(..)

    -- * Endianness
    , HostEndian
    , BigEndian(..)
    , LittleEndian(..)

    -- * Serialization
    , encode
    , decode

    -- * The Get type
    , Get
    , GetState
    , stateGet
    , setStateGet
    , modifyStateGet
    , runGet
    , ensure
    , skip
    , getBytes
    , getByteString
    , remaining
    , eof
    , getHE
    , getLE
    , getBE

    -- * The Put type
    , Put
    , PutState
    , statePut
    , setStatePut
    , modifyStatePut
    , runPut
    , evalPut
    , grow
    , putByteString
    , putHE
    , putLE
    , putBE
) where

import GHC.IO
import GHC.Prim
import GHC.Int
import GHC.Float
import GHC.Word
import GHC.Ptr
import Control.Monad
import Data.Bits
import Data.ByteString (ByteString)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.PersistState.Internal
import Data.Proxy
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Text (Text)
import Foreign (withForeignPtr)
import GHC.Base (unsafeChr, ord)
import GHC.Exts (IsList(..))
import GHC.Generics
import GHC.Real (Ratio(..))
import GHC.TypeLits
import Numeric.Natural
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Short as S
import qualified Data.Monoid as M
import qualified Data.Text.Encoding as TE
import qualified Data.Tree as T

#include "MachDeps.h"

putHE :: Persist s (HostEndian a) => a -> Put s ()
getHE :: Persist s (HostEndian a) => Get s a
{-# INLINE putHE #-}
{-# INLINE getHE #-}

#ifdef WORDS_BIGENDIAN
type HostEndian = BigEndian
getHE = getBE
putHE = putBE
#else
type HostEndian = LittleEndian
getHE = getLE
putHE = putLE
#endif

#ifndef UNALIGNED_MEMORY
#  error Aligned memory access is not implemented currently
#endif

#if WORD_SIZE_IN_BITS < 32
#  error 32 bit architectures are unsupported currently
#endif

#ifdef WORDS_BIGENDIAN
#  error Big endian is unsupported currently
#endif

castLE16, castLE32, castLE64, castBE16, castBE32, castBE64 :: Word# -> Word#
castLE16 x = x
castLE32 x = x
castLE64 x = x
castBE16 x = narrow16Word# (byteSwap16# x)
castBE32 x = narrow32Word# (byteSwap32# x)
castBE64 x = byteSwap64# x
{-# INLINE castLE16 #-}
{-# INLINE castLE32 #-}
{-# INLINE castLE64 #-}
{-# INLINE castBE16 #-}
{-# INLINE castBE32 #-}
{-# INLINE castBE64 #-}

poke8, poke16LE, poke32LE, poke64LE,
  poke16BE, poke32BE, poke64BE :: Addr# -> Word# -> State# RealWorld -> State# RealWorld
poke8 p = writeWord8OffAddr# p 0#
poke16LE p x = writeWord16OffAddr# p 0# (castLE16 x)
poke32LE p x = writeWord32OffAddr# p 0# (castLE32 x)
poke64LE p x = writeWord64OffAddr# p 0# (castLE64 x)
poke16BE p x = writeWord16OffAddr# p 0# (castBE16 x)
poke32BE p x = writeWord32OffAddr# p 0# (castBE32 x)
poke64BE p x = writeWord64OffAddr# p 0# (castBE64 x)
{-# INLINE poke16LE #-}
{-# INLINE poke32LE #-}
{-# INLINE poke64LE #-}
{-# INLINE poke16BE #-}
{-# INLINE poke32BE #-}
{-# INLINE poke64BE #-}

peek8, peek16LE, peek32LE, peek16BE, peek32BE, peek64LE, peek64BE :: Addr# -> Word#
peek8 p = indexWord8OffAddr# p 0#
peek16LE p = castLE16 (indexWord16OffAddr# p 0#)
peek32LE p = castLE32 (indexWord32OffAddr# p 0#)
peek64LE p = castLE64 (indexWord64OffAddr# p 0#)
peek16BE p = castBE16 (indexWord16OffAddr# p 0#)
peek32BE p = castBE32 (indexWord32OffAddr# p 0#)
peek64BE p = castBE64 (indexWord64OffAddr# p 0#)
{-# INLINE peek8 #-}
{-# INLINE peek16LE #-}
{-# INLINE peek32LE #-}
{-# INLINE peek64LE #-}
{-# INLINE peek16BE #-}
{-# INLINE peek32BE #-}
{-# INLINE peek64BE #-}

newtype BigEndian a = BigEndian { unBE :: a }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

newtype LittleEndian a = LittleEndian { unLE :: a }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

class Persist s t where
  -- | Encode a value in the Put monad.
  put :: t -> Put s ()
  -- | Decode a value in the Get monad
  get :: Get s t

  default put :: (Generic t, GPersistPut s (Rep t)) => t -> Put s ()
  put = gput . from

  default get :: (Generic t, GPersistGet s (Rep t)) => Get s t
  get = to <$!> gget

-- | Encode a value using binary serialization to a strict ByteString.
encode :: forall s a. Persist s a => PutState s -> a -> ByteString
encode s x = runPut (put @s x) s

-- | Decode a value from a strict ByteString, reconstructing the original
-- structure.
decode :: forall s a. Persist s a => GetState s -> ByteString -> Either String a
decode = runGet (get @s)

putLE :: Persist s (LittleEndian a) => a -> Put s ()
putLE = put . LittleEndian
{-# INLINE putLE #-}

putBE :: Persist s (BigEndian a) => a -> Put s ()
putBE = put . BigEndian
{-# INLINE putBE #-}

getLE :: Persist s (LittleEndian a) => Get s a
getLE = unLE <$!> get
{-# INLINE getLE #-}

getBE :: Persist s (BigEndian a) => Get s a
getBE = unBE <$!> get
{-# INLINE getBE #-}

unsafePut8 :: Integral a => a -> Put s ()
unsafePut8 x | (W8# x') <- fromIntegral x = Put $ \_ p q s w ->
                 (# poke8 p x' w, p `plusAddr#` 1#, q, s, () #)
{-# INLINE unsafePut8 #-}

unsafePut16LE :: Integral a => a -> Put s ()
unsafePut16LE x | (W16# x') <- fromIntegral x = Put $ \_ p q s w ->
                 (# poke16LE p x' w, p `plusAddr#` 2#, q, s, () #)
{-# INLINE unsafePut16LE #-}

unsafePut32LE :: Integral a => a -> Put s ()
unsafePut32LE x | (W32# x') <- fromIntegral x = Put $ \_ p q s w ->
                 (# poke32LE p x' w, p `plusAddr#` 4#, q, s, () #)
{-# INLINE unsafePut32LE #-}

unsafePut64LE :: Integral a => a -> Put s ()
unsafePut64LE x | (W64# x') <- fromIntegral x = Put $ \_ p q s w ->
                 (# poke64LE p x' w, p `plusAddr#` 8#, q, s, () #)
{-# INLINE unsafePut64LE #-}

unsafePut16BE :: Integral a => a -> Put s ()
unsafePut16BE x | (W16# x') <- fromIntegral x = Put $ \_ p q s w ->
                 (# poke16BE p x' w, p `plusAddr#` 2#, q, s, () #)
{-# INLINE unsafePut16BE #-}

unsafePut32BE :: Integral a => a -> Put s ()
unsafePut32BE x | (W32# x') <- fromIntegral x = Put $ \_ p q s w ->
                 (# poke32BE p x' w, p `plusAddr#` 4#, q, s, () #)
{-# INLINE unsafePut32BE #-}

unsafePut64BE :: Integral a => a -> Put s ()
unsafePut64BE x | (W64# x') <- fromIntegral x = Put $ \_ p q s w ->
                 (# poke64BE p x' w, p `plusAddr#` 8#, q, s, () #)
{-# INLINE unsafePut64BE #-}

unsafeGet8 :: Num a => Get s a
unsafeGet8 = Get $ \_ p s -> case peek8 p of
  x -> (# p `plusAddr#` 1#, s, fromIntegral (W8# x) #)
{-# INLINE unsafeGet8 #-}

unsafeGet16LE :: Num a => Get s a
unsafeGet16LE = Get $ \_ p s -> case peek16LE p of
  x -> (# p `plusAddr#` 2#, s, fromIntegral (W16# x) #)
{-# INLINE unsafeGet16LE #-}

unsafeGet32LE :: Num a => Get s a
unsafeGet32LE = Get $ \_ p s -> case peek32LE p of
  x -> (# p `plusAddr#` 4#, s, fromIntegral (W32# x) #)
{-# INLINE unsafeGet32LE #-}

unsafeGet64LE :: Num a => Get s a
unsafeGet64LE = Get $ \_ p s -> case peek64LE p of
  x -> (# p `plusAddr#` 8#, s, fromIntegral (W64# x) #)
{-# INLINE unsafeGet64LE #-}

unsafeGet16BE :: Num a => Get s a
unsafeGet16BE = Get $ \_ p s -> case peek16BE p of
  x -> (# p `plusAddr#` 2#, s, fromIntegral (W16# x) #)
{-# INLINE unsafeGet16BE #-}

unsafeGet32BE :: Num a => Get s a
unsafeGet32BE = Get $ \_ p s -> case peek32BE p of
  x -> (# p `plusAddr#` 4#, s, fromIntegral (W32# x) #)
{-# INLINE unsafeGet32BE #-}

unsafeGet64BE :: Num a => Get s a
unsafeGet64BE = Get $ \_ p s -> case peek64BE p of
  x -> (# p `plusAddr#` 8#, s, fromIntegral (W64# x) #)
{-# INLINE unsafeGet64BE #-}

reinterpretWord64AsDouble :: Word64 -> Get s Double
reinterpretWord64AsDouble (W64# x) = Get $ \e p s ->
  case writeWord64OffAddr# (geReinterpretCast e) 0# x realWorld# of
    w -> case readDoubleOffAddr# (geReinterpretCast e) 0# w of
      (# _, d #) -> (# p, s, D# d #)
{-# INLINE reinterpretWord64AsDouble #-}

reinterpretWord32AsFloat :: Word32 -> Get s Float
reinterpretWord32AsFloat (W32# x) = Get $ \e p s ->
  case writeWord32OffAddr# (geReinterpretCast e) 0# x realWorld# of
    w -> case readFloatOffAddr# (geReinterpretCast e) 0# w of
      (# _, d #) -> (# p, s, F# d #)
{-# INLINE reinterpretWord32AsFloat #-}

reinterpretDoubleAsWord64 :: Double -> Put s Word64
reinterpretDoubleAsWord64 (D# x) = Put $ \e p q s w ->
  case writeDoubleOffAddr# (peReinterpretCast e) 0# x w of
    w' -> case readWord64OffAddr# (peReinterpretCast e) 0# w' of
      (# w'', d #) -> (# w'', p, q, s, W64# d #)
{-# INLINE reinterpretDoubleAsWord64 #-}

reinterpretFloatAsWord32 :: Float -> Put s Word32
reinterpretFloatAsWord32 (F# x) = Put $ \e p q s w ->
  case writeFloatOffAddr# (peReinterpretCast e) 0# x w of
    w' -> case readWord32OffAddr# (peReinterpretCast e) 0# w' of
      (# w'', d #) -> (# w'', p, q, s, W32# d #)
{-# INLINE reinterpretFloatAsWord32 #-}

-- The () type need never be written to disk: values of singleton type
-- can be reconstructed from the type alone
instance Persist s () where
  put () = pure ()
  {-# INLINE put #-}
  get = pure ()
  {-# INLINE get #-}

instance Persist s Word8 where
  put x = do
    grow 1
    unsafePut8 x
  {-# INLINE put #-}

  get = do
    ensure 1
    unsafeGet8
  {-# INLINE get #-}

instance Persist s (LittleEndian Word16) where
  put x = do
    grow 2
    unsafePut16LE $ unLE x
  {-# INLINE put #-}

  get = do
    ensure 2
    LittleEndian <$!> unsafeGet16LE
  {-# INLINE get #-}

instance Persist s (BigEndian Word16) where
  put x = do
    grow 2
    unsafePut16BE $ unBE x
  {-# INLINE put #-}

  get = do
    ensure 2
    BigEndian <$!> unsafeGet16BE
  {-# INLINE get #-}

putLEB128 :: (Bits a, Integral a) => Int -> a -> Put s ()
putLEB128 n x = do grow n; go n x
  where go !1 !b = unsafePut8 b
        go !i !b = do
          let !b' = b `unsafeShiftR` 7
          if b' == 0 then
            unsafePut8 b
          else do
            unsafePut8 ((b .&. 0x7F) .|. 0x80)
            go (i - 1) b'
{-# INLINE putLEB128 #-}

getLEB128 :: forall a s. Integral a => Int -> Get s a
getLEB128 !n = fromIntegral @Word64 @a <$!> go n
  where go !1 = do
          ensure 1
          unsafeGet8
        go !i = do
          ensure 1
          b <- unsafeGet8
          if b .&. 0x80 == 0 then
            pure b
          else do
            h <- go (i - 1)
            pure $ (h `unsafeShiftL` 7) .|. (b .&. 0x7F)
{-# INLINE getLEB128 #-}

instance Persist s Word16 where
  put = putLEB128 3
  {-# INLINE put #-}
  get = getLEB128 3
  {-# INLINE get #-}

instance Persist s (LittleEndian Word32) where
  put x = do
    grow 4
    unsafePut32LE $ unLE x
  {-# INLINE put #-}

  get = do
    ensure 4
    LittleEndian <$!> unsafeGet32LE
  {-# INLINE get #-}

instance Persist s (BigEndian Word32) where
  put x = do
    grow 4
    unsafePut32BE $ unBE x
  {-# INLINE put #-}

  get = do
    ensure 4
    BigEndian <$!> unsafeGet32BE
  {-# INLINE get #-}

instance Persist s Word32 where
  put = putLEB128 5
  {-# INLINE put #-}
  get = getLEB128 5
  {-# INLINE get #-}

instance Persist s (LittleEndian Word64) where
  put x = do
    grow 8
    unsafePut64LE $ unLE x
  {-# INLINE put #-}

  get = do
    ensure 8
    LittleEndian <$!> unsafeGet64LE
  {-# INLINE get #-}

instance Persist s (BigEndian Word64) where
  put x = do
    grow 8
    unsafePut64BE $ unBE x
  {-# INLINE put #-}

  get = do
    ensure 8
    BigEndian <$!> unsafeGet64BE
  {-# INLINE get #-}

instance Persist s Word64 where
  put = putLEB128 10
  {-# INLINE put #-}
  get = getLEB128 10
  {-# INLINE get #-}

instance Persist s Int8 where
  put = put @s @Word8 . fromIntegral
  {-# INLINE put #-}
  get = fromIntegral <$!> get @s @Word8
  {-# INLINE get #-}

instance Persist s (LittleEndian Int16) where
  put = put . fmap (fromIntegral @_ @Word16)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word16) <$!> get
  {-# INLINE get #-}

instance Persist s (BigEndian Int16) where
  put = put . fmap (fromIntegral @_ @Word16)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word16) <$!> get
  {-# INLINE get #-}

instance Persist s Int16 where
  put = put . fromIntegral @_ @Word16
  {-# INLINE put #-}
  get = fromIntegral @Word16 <$!> get
  {-# INLINE get #-}

instance Persist s (LittleEndian Int32) where
  put = put . fmap (fromIntegral @_ @Word32)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word32) <$!> get
  {-# INLINE get #-}

instance Persist s (BigEndian Int32) where
  put = put . fmap (fromIntegral @_ @Word32)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word32) <$!> get
  {-# INLINE get #-}

instance Persist s Int32 where
  put = put . fromIntegral @_ @Word32
  {-# INLINE put #-}
  get = fromIntegral @Word32 <$!> get
  {-# INLINE get #-}

instance Persist s (LittleEndian Int64) where
  put = put . fmap (fromIntegral @_ @Word64)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word64) <$!> get
  {-# INLINE get #-}

instance Persist s (BigEndian Int64) where
  put = put . fmap (fromIntegral @_ @Word64)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word64) <$!> get
  {-# INLINE get #-}

instance Persist s Int64 where
  put = put . fromIntegral @_ @Word64
  {-# INLINE put #-}
  get = fromIntegral @Word64 <$!> get
  {-# INLINE get #-}

instance Persist s (LittleEndian Double) where
  put x = reinterpretDoubleAsWord64 (unLE x) >>= putLE
  {-# INLINE put #-}
  get = getLE >>= fmap LittleEndian . reinterpretWord64AsDouble
  {-# INLINE get #-}

instance Persist s (BigEndian Double) where
  put x = reinterpretDoubleAsWord64 (unBE x) >>= putBE
  {-# INLINE put #-}
  get = getBE >>= fmap BigEndian . reinterpretWord64AsDouble
  {-# INLINE get #-}

instance Persist s Double where
  put = putLE
  {-# INLINE put #-}
  get = getLE
  {-# INLINE get #-}

instance Persist s (LittleEndian Float) where
  put x = reinterpretFloatAsWord32 (unLE x) >>= putLE
  {-# INLINE put #-}
  get = getLE >>= fmap LittleEndian . reinterpretWord32AsFloat
  {-# INLINE get #-}

instance Persist s (BigEndian Float) where
  put x = reinterpretFloatAsWord32 (unBE x) >>= putBE
  {-# INLINE put #-}
  get = getBE >>= fmap BigEndian . reinterpretWord32AsFloat
  {-# INLINE get #-}

instance Persist s Float where
  put = putLE
  {-# INLINE put #-}
  get = getLE
  {-# INLINE get #-}

instance Persist s (LittleEndian Word) where
  put = put . fmap (fromIntegral @_ @Word64)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word64) <$!> get
  {-# INLINE get #-}

instance Persist s (BigEndian Word) where
  put = put . fmap (fromIntegral @_ @Word64)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Word64) <$!> get
  {-# INLINE get #-}

instance Persist s Word where
  put = put . fromIntegral @_ @Word64
  {-# INLINE put #-}
  get = fromIntegral @Word64 <$!> get
  {-# INLINE get #-}

instance Persist s (LittleEndian Int) where
  put = put . fmap (fromIntegral @_ @Int64)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Int64) <$!> get
  {-# INLINE get #-}

instance Persist s (BigEndian Int) where
  put = put . fmap (fromIntegral @_ @Int64)
  {-# INLINE put #-}
  get = fmap (fromIntegral @Int64) <$!> get
  {-# INLINE get #-}

instance Persist s Int where
  put = put . fromIntegral @_ @Int64
  {-# INLINE put #-}
  get = fromIntegral @Int64 <$!> get
  {-# INLINE get #-}

instance Persist s Integer where
  put n = do
    put $ n < 0
    put $ unroll $ abs n

  get = do
    neg <- get
    val <- roll <$!> get
    pure $! if neg then negate val else val

unroll :: (Integral a, Bits a) => a -> [Word8]
unroll = unfoldr step
  where step 0 = Nothing
        step i = Just (fromIntegral i, i `unsafeShiftR` 8)

roll :: (Integral a, Bits a) => [Word8] -> a
roll = foldr unstep 0
  where unstep b a = a `unsafeShiftL` 8 .|. fromIntegral b

instance Persist s a => Persist s (Ratio a) where
  put (n :% d) = put n *> put d
  {-# INLINE put #-}

  get = (:%) <$!> get <*> get
  {-# INLINE get #-}

instance Persist s Natural where
  put = put . unroll
  get = roll <$!> get

-- Char is serialized as UTF-8
instance Persist s Char where
  put a | c <= 0x7f     = put (fromIntegral c :: Word8)
        | c <= 0x7ff    = do put (0xc0 .|. y)
                             put (0x80 .|. z)
        | c <= 0xffff   = do put (0xe0 .|. x)
                             put (0x80 .|. y)
                             put (0x80 .|. z)
        | c <= 0x10ffff = do put (0xf0 .|. w)
                             put (0x80 .|. x)
                             put (0x80 .|. y)
                             put (0x80 .|. z)
        | otherwise = error "Not a valid Unicode code point"
    where
      c = ord a
      z, y, x, w :: Word8
      z = fromIntegral (c                 .&. 0x3f)
      y = fromIntegral (unsafeShiftR c 6  .&. 0x3f)
      x = fromIntegral (unsafeShiftR c 12 .&. 0x3f)
      w = fromIntegral (unsafeShiftR c 18 .&. 0x7)
  {-# INLINE put #-}

  get = do
    let byte = fromIntegral <$!> get @s @Word8
        shiftL6 = flip unsafeShiftL 6
    w <- byte
    r <- if | w < 0x80  -> pure w
            | w < 0xe0  -> do
                x <- xor 0x80 <$!> byte
                pure $ x .|. shiftL6 (xor 0xc0 w)
            | w < 0xf0  -> do
                x <- xor 0x80 <$!> byte
                y <- xor 0x80 <$!> byte
                pure $ y .|. shiftL6 (x .|. shiftL6
                                       (xor 0xe0 w))
            | otherwise -> do
                x <- xor 0x80 <$!> byte
                y <- xor 0x80 <$!> byte
                z <- xor 0x80 <$!> byte
                pure $ z .|. shiftL6 (y .|. shiftL6
                                       (x .|. shiftL6 (xor 0xf0 w)))
    if r <= 0x10FFFF then
      pure $ unsafeChr r
    else
      failGet CharException "Invalid character"
  {-# INLINE get #-}

instance Persist s Text where
  put = put . TE.encodeUtf8
  {-# INLINE put #-}
  get = do
    n <- get
    TE.decodeUtf8 <$!> getBytes n
  {-# INLINE get #-}

instance Persist s Bool
instance Persist s Ordering
instance Persist s a => Persist s (Maybe a)
instance Persist s e => Persist s (T.Tree e)
instance (Persist s a, Persist s b) => Persist s (Either a b)
instance (Persist s a, Persist s b) => Persist s (a,b)
instance (Persist s a, Persist s b, Persist s c) => Persist s (a,b,c)
instance (Persist s a, Persist s b, Persist s c, Persist s d)
        => Persist s (a,b,c,d)
instance (Persist s a, Persist s b, Persist s c, Persist s d, Persist s e)
        => Persist s (a,b,c,d,e)
instance (Persist s a, Persist s b, Persist s c, Persist s d, Persist s e
         , Persist s f)
        => Persist s (a,b,c,d,e,f)
instance (Persist s a, Persist s b, Persist s c, Persist s d, Persist s e
         , Persist s f, Persist s h)
        => Persist s (a,b,c,d,e,f,h)
instance Persist s a => Persist s (M.Dual a)
instance Persist s M.All
instance Persist s M.Any
instance Persist s a => Persist s (M.Sum a)
instance Persist s a => Persist s (M.Product a)
instance Persist s a => Persist s (M.First a)
instance Persist s a => Persist s (M.Last a)

-- | Persist a list in the following format:
--   Word64 (little endian format)
--   element 1
--   ...
--   element n
instance Persist s a => Persist s [a] where
    put l = do
      put $ length l
      mapM_ put l
    {-# INLINE put #-}

    get = go [] =<< get @s @Word64
      where go as 0 = pure $! reverse as
            go as i = do x <- get
                         x `seq` go (x:as) (i - 1)
    {-# INLINE get #-}

instance Persist s ByteString where
  put s = do
    put $ B.length s
    putByteString s
  get = get >>= getByteString

instance Persist s L.ByteString where
  put = put . L.toStrict
  get = L.fromStrict <$!> get

instance Persist s S.ShortByteString where
  -- TODO optimize
  put = put . S.fromShort
  get = S.toShort <$!> get

instance (Ord a, Persist s a) => Persist s (Set a) where
  put = put . toList
  {-# INLINE put #-}
  get = fromList <$!> get
  {-# INLINE get #-}

instance (Ord k, Persist s k, Persist s e) => Persist s (Map k e) where
  put = put . toList
  {-# INLINE put #-}
  get = fromList <$!> get
  {-# INLINE get #-}

instance Persist s IntSet where
  put = put . toList
  get = fromList <$!> get

instance Persist s e => Persist s (NonEmpty e) where
  put = put . toList
  {-# INLINE put #-}
  get = fromList <$!> get
  {-# INLINE get #-}

instance Persist s e => Persist s (IntMap e) where
  put = put . toList
  {-# INLINE put #-}
  get = fromList <$!> get
  {-# INLINE get #-}

instance Persist s e => Persist s (Seq e) where
  put = put . toList
  {-# INLINE put #-}
  get = fromList <$!> get
  {-# INLINE get #-}

type family SumArity (a :: * -> *) :: Nat where
  SumArity (C1 c a) = 1
  SumArity (x :+: y) = SumArity x + SumArity y

class GPersistPut s f where
  gput :: f a -> Put s ()

class GPersistGet s f where
  gget :: Get s (f a)

instance GPersistPut s f => GPersistPut s (M1 i c f) where
  gput = gput . unM1
  {-# INLINE gput #-}

instance GPersistGet s f => GPersistGet s (M1 i c f) where
  gget = fmap M1 gget
  {-# INLINE gget #-}

instance Persist s a => GPersistPut s (K1 i a) where
  gput = put . unK1
  {-# INLINE gput #-}

instance Persist s a => GPersistGet s (K1 i a) where
  gget = fmap K1 get
  {-# INLINE gget #-}

instance GPersistPut s U1 where
  gput _ = pure ()
  {-# INLINE gput #-}

instance GPersistGet s U1 where
  gget = pure U1
  {-# INLINE gget #-}

instance GPersistPut s V1 where
  gput x = case x of {}
  {-# INLINE gput #-}

instance GPersistGet s V1 where
  gget = undefined
  {-# INLINE gget #-}

instance (GPersistPut s a, GPersistPut s b) => GPersistPut s (a :*: b) where
  gput (a :*: b) = gput a *> gput b
  {-# INLINE gput #-}

instance (GPersistGet s a, GPersistGet s b) => GPersistGet s (a :*: b) where
  gget = (:*:) <$!> gget <*> gget
  {-# INLINE gget #-}

instance (SumArity (a :+: b) <= 255, GPersistPutSum s 0 (a :+: b)) => GPersistPut s (a :+: b) where
  gput x = gputSum x (Proxy :: Proxy 0)
  {-# INLINE gput #-}

instance (SumArity (a :+: b) <= 255, GPersistGetSum s 0 (a :+: b)) => GPersistGet s (a :+: b) where
  gget = do
    tag <- get
    ggetSum tag (Proxy :: Proxy 0)
  {-# INLINE gget #-}

class KnownNat n => GPersistPutSum s (n :: Nat) (f :: * -> *) where
  gputSum :: f p -> Proxy n -> Put s ()

class KnownNat n => GPersistGetSum s (n :: Nat) (f :: * -> *) where
  ggetSum :: Word8 -> Proxy n -> Get s (f p)

instance (GPersistPutSum s n a, GPersistPutSum s (n + SumArity a) b, KnownNat n)
         => GPersistPutSum s n (a :+: b) where
  gputSum (L1 l) _ = gputSum l (Proxy :: Proxy n)
  gputSum (R1 r) _ = gputSum r (Proxy :: Proxy (n + SumArity a))
  {-# INLINE gputSum #-}

instance (GPersistGetSum s n a, GPersistGetSum s (n + SumArity a) b, KnownNat n)
         => GPersistGetSum s n (a :+: b) where
  ggetSum tag proxyL
    | tag < sizeL = L1 <$!> ggetSum tag proxyL
    | otherwise = R1 <$!> ggetSum tag (Proxy :: Proxy (n + SumArity a))
    where
      sizeL = fromInteger (natVal (Proxy :: Proxy (n + SumArity a)))
  {-# INLINE ggetSum #-}

instance (GPersistPut s a, KnownNat n) => GPersistPutSum s n (C1 c a) where
  gputSum x _ = do
    put (fromInteger (natVal (Proxy :: Proxy n)) :: Word8)
    gput x
  {-# INLINE gputSum #-}

instance (GPersistGet s a, KnownNat n) => GPersistGetSum s n (C1 c a) where
  ggetSum tag _
    | tag == cur = gget
    | tag > cur = fail "Sum tag invalid"
    | otherwise = fail "Implementation error"
    where
      cur = fromInteger (natVal (Proxy :: Proxy n))
  {-# INLINE ggetSum #-}

-- | Ensure that @n@ bytes are available. Fails if fewer than @n@ bytes are available.
ensure :: Int -> Get s ()
ensure n
  | n < 0 = failGet LengthException "ensure: negative length"
  | otherwise = do
      m <- remaining
      when (m < n) $ failGet LengthException "Not enough bytes available"
{-# INLINE ensure #-}

-- | Skip ahead @n@ bytes. Fails if fewer than @n@ bytes are available.
skip :: Int -> Get s ()
skip n@(I# n') = do
  ensure n
  Get $ \_ p s -> (# p `plusAddr#` n', s, () #)
{-# INLINE skip #-}

-- | Get the number of remaining unparsed bytes.  Useful for checking whether
-- all input has been consumed.
remaining :: Get s Int
remaining = Get $ \e p s -> (# p, s, I# (geEnd e `minusAddr#` p) #)
{-# INLINE remaining #-}

-- -- | Succeed if end of input reached.
eof :: Get s ()
eof = do
  n <- remaining
  when (n /= 0) $ failGet EOFException "Expected end of file"
{-# INLINE eof #-}

-- | Pull @n@ bytes from the input, as a strict ByteString.
getBytes :: Int -> Get s ByteString
getBytes n@(I# n') = do
  ensure n
  Get $ \e p s -> (# p `plusAddr#` n', s, B.PS (geBuf e) (I# (p `minusAddr#` geBegin e)) n #)
{-# INLINE getBytes #-}

-- | An efficient 'get' method for strict ByteStrings. Fails if fewer
-- than @n@ bytes are left in the input. This function creates a fresh
-- copy of the underlying bytes.
getByteString :: Int -> Get s ByteString
getByteString n = B.copy <$!> getBytes n
{-# INLINE getByteString #-}

runPut :: Put s a -> PutState s -> ByteString
runPut s = snd . evalPut s
{-# INLINE runPut #-}

putByteString :: ByteString -> Put s ()
putByteString !(B.PS b o n@(I# n')) = do
  grow n
  Put $ \_ p q s w ->
    let IO m = withForeignPtr b $ \b' -> B.memcpy (Ptr p) (b' `plusPtr` o) n
    in case m w of
      (# w', _ #) -> (# w', p `plusAddr#` n', q, s, () #)
{-# INLINE putByteString #-}

modifyStateGet :: (GetState s -> GetState s) -> Get s ()
modifyStateGet f = do
  s <- stateGet
  setStateGet (f s)
{-# INLINE modifyStateGet #-}

modifyStatePut :: (PutState s -> PutState s) -> Put s ()
modifyStatePut f = do
  s <- statePut
  setStatePut (f s)
{-# INLINE modifyStatePut #-}
