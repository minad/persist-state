{-# LANGUAGE AllowAmbiguousTypes #-}
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
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}

module Data.PersistState.Internal (
    -- * The Get type
    Get(..)
    , GetState
    , GetEnv(..)
    , GetException(..)
    , offset
    , failGet
    , stateGet
    , setStateGet
    , runGet

    -- * The Put type
    , Put(..)
    , PutState
    , PutEnv(..)
    , Chunk(..)
    , evalPut
    , grow
    , statePut
    , setStatePut
) where

import GHC.Prim
import GHC.Ptr
import GHC.IO
import GHC.Exts
import Control.Exception
import Control.Monad
import Data.ByteString (ByteString)
import Data.Foldable (foldlM, foldl')
import Data.IORef
import Data.List.NonEmpty (NonEmpty(..))
import Data.Word
import Foreign (ForeignPtr, withForeignPtr, mallocBytes, free, allocaBytes)
import qualified Control.Monad.Fail as Fail
import qualified Data.ByteString.Internal as B

#include "MachDeps.h"

type family GetState s

-- TODO remove
data Tup b c = Tup Addr# Addr# !b !c

-- TODO remove
fixup :: IO (Tup a b) -> State# RealWorld -> (# State# RealWorld, Addr#, Addr#, a, b #)
fixup (IO m) w = case m w of
  (# w', Tup a b c d #) -> (# w', a, b, c, d #)

data GetEnv s = GetEnv
  { geBuf   :: !(ForeignPtr Word8)
  , geBegin :: Addr#
  , geEnd   :: Addr#
  , geReinterpretCast :: Addr#
  }

newtype Get s a = Get
  { unGet :: GetEnv s -> Addr# -> GetState s -> (# Addr#, GetState s, a #)
  }

instance Functor (Get s) where
  fmap f m = Get $ \e p s -> case unGet m e p s of
    (# p', s', x #) -> (# p', s', f x #)
  {-# INLINE fmap #-}

instance Applicative (Get s) where
  pure a = Get $ \_ p s -> (# p, s, a #)
  {-# INLINE pure #-}

  f <*> a = Get $ \e p s ->
    case unGet f e p s of
      (# p', s', f' #) ->
        case unGet a e p' s' of
          (# p'', s'', a'' #) -> (# p'', s'', f' a'' #)
  {-# INLINE (<*>) #-}

  m1 *> m2 = do
    void m1
    m2
  {-# INLINE (*>) #-}

instance Monad (Get s) where
  m >>= f = Get $ \e p s -> case unGet m e p s of
    (# p', s', x #) -> unGet (f x) e p' s'
  {-# INLINE (>>=) #-}

#if !MIN_VERSION_base(4,11,0)
  fail = Fail.fail
  {-# INLINE fail #-}
#endif

data GetException
  = LengthException Int String
  | CharException Int String
  | EOFException Int String
  | GenericGetException Int String
  deriving (Eq, Show)

instance Exception GetException

instance Fail.MonadFail (Get s) where
  fail msg = failGet GenericGetException ("Failed reading: " <> msg)
  {-# INLINE fail #-}

offset :: Get s Int
offset = Get $ \e p s -> (# p, s, I# (p `minusAddr#` geBegin e) #)
{-# INLINE offset #-}

failGet :: (Int -> String -> GetException) -> String -> Get s a
failGet ctor msg = do
  off <- offset
  Get $ \_ _ _ -> raise# (toException (ctor off msg))

stateGet :: Get s (GetState s)
stateGet = Get $ \_ p s -> (# p, s, s #)
{-# INLINE stateGet #-}

statePut :: Put s (PutState s)
statePut = Put $ \_ p q s w -> (# w, p, q, s, s #)
{-# INLINE statePut #-}

setStateGet :: GetState s -> Get s ()
setStateGet s = Get $ \_ p _ -> (# p, s, () #)
{-# INLINE setStateGet #-}

setStatePut :: PutState s -> Put s ()
setStatePut s = Put $ \_ p q _ w -> (# w, p, q, s, () #)
{-# INLINE setStatePut #-}

-- | Run the Get monad applies a 'get'-based parser on the input ByteString
runGet :: Get s a -> GetState s -> ByteString -> Either String a
runGet m g s = unsafePerformIO $ catch (Right <$!> run) handler
  where handler (x :: GetException) = pure $ Left $ displayException x
        run = withForeignPtr buf $ \(Ptr p) -> allocaBytes 8 $ \(Ptr t) -> do
          let env = GetEnv { geBuf = buf, geBegin = p, geEnd = p `plusAddr#` (pos +# len), geReinterpretCast = t }
          case unGet m env (p `plusAddr#` pos) g of
            (# _, _, r #) -> pure r
        !(B.PS buf (I# pos) (I# len)) = s
{-# NOINLINE runGet #-}

data Chunk = Chunk
  { chkBegin :: Addr#
  , chkEnd   :: Addr#
  }

type family PutState s

data PutEnv s = PutEnv
  { peChks :: !(IORef (NonEmpty Chunk))
  , peReinterpretCast :: Addr#
  }

newtype Put s a = Put
  { unPut :: PutEnv s -> Addr# -> Addr# -> PutState s
          -> State# RealWorld -> (# State# RealWorld, Addr#, Addr#, PutState s, a #) }

instance Functor (Put s) where
  fmap f m = Put $ \e p q s w -> case unPut m e p q s w of
    (# w', p', q', s', x #) -> (# w', p', q', s', f x #)
  {-# INLINE fmap #-}

instance Applicative (Put s) where
  pure a = Put $ \_ p q s w -> (# w, p, q, s, a #)
  {-# INLINE pure #-}

  f <*> a = Put $ \e p q s w -> case unPut f e p q s w of
    (# w', p', q', s', f' #) -> case unPut a e p' q' s' w' of
      (# w'', p'', q'', s'', a' #) -> (# w'', p'', q'', s'', f' a' #)
  {-# INLINE (<*>) #-}

  m1 *> m2 = do
    void m1
    m2
  {-# INLINE (*>) #-}

instance Monad (Put s) where
  m >>= f = Put $ \e p q s w -> case unPut m e p q s w of
    (# w', p', q', s', x #) -> unPut (f x) e p' q' s' w'
  {-# INLINE (>>=) #-}

minChunkSize :: Int
minChunkSize = 0x10000
{-# INLINE minChunkSize #-}

newChunk :: Int -> IO Chunk
newChunk size = do
  let !n@(I# n') = max size minChunkSize
  Ptr p <- mallocBytes n
  pure $! Chunk p (p `plusAddr#` n')
{-# INLINE newChunk #-}

-- | Ensure that @n@ bytes can be written.
grow :: Int -> Put s ()
grow !n@(I# n')
  | n < 0 = error "grow: negative length"
  | otherwise = Put $ \e p q s -> fixup $ do
      if isTrue# (q `minusAddr#` p >=# n') then
        pure $! Tup p q s ()
      else
        doGrow e p s n
{-# INLINE grow #-}

doGrow :: PutEnv s -> Addr# -> PutState s -> Int -> IO (Tup (PutState s) ())
doGrow e p s n = do
  k <- newChunk n
  modifyIORef' (peChks e) $ \case
    (c:|cs) -> k :| c { chkEnd = p } : cs
  pure $! Tup (chkBegin k) (chkEnd k) s ()
{-# NOINLINE doGrow #-}

chunksLength :: [Chunk] -> Int
chunksLength = foldl' (\s c -> s + I# (chkEnd c `minusAddr#` chkBegin c)) 0
{-# INLINE chunksLength #-}

catChunks :: [Chunk] -> IO ByteString
catChunks chks = B.create (chunksLength chks) $ \p ->
  void $ foldlM (\q c -> do
                    let n = I# (chkEnd c `minusAddr#` chkBegin c)
                    B.memcpy q (Ptr (chkBegin c)) n
                    free $ Ptr (chkBegin c)
                    pure (q `plusPtr` n)) p $ reverse chks
{-# INLINE catChunks #-}

evalPutIO :: Put s a -> PutState s -> IO (a, ByteString)
evalPutIO p ps = do
  k <- newChunk 0
  chks <- newIORef (k:|[])
  Tup p' _q' _ps' r <- allocaBytes 8 $ \(Ptr t) ->
    IO $ \w -> case unPut p PutEnv { peChks = chks, peReinterpretCast = t } (chkBegin k) (chkEnd k) ps w of
                 (# w', p', q', ps', r #) -> (# w', Tup p' q' ps' r #)
  cs <- readIORef chks
  s <- case cs of
    (x:|xs) -> catChunks $ x { chkEnd = p' } : xs
  pure (r, s)

evalPut :: Put s a -> PutState s -> (a, ByteString)
evalPut s e = unsafePerformIO $ evalPutIO s e
{-# NOINLINE evalPut #-}
