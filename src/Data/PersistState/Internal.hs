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
{-# LANGUAGE UndecidableInstances #-}

module Data.PersistState.Internal (
    Tup(..)
    , ptrToAddr

    -- * The Get type
    , Get(..)
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
import Control.Exception
import Control.Monad
import Data.ByteString (ByteString)
import Data.Foldable (foldlM)
import Data.IORef
import Data.List.NonEmpty (NonEmpty(..))
import Data.Word
import Foreign (ForeignPtr, Ptr, plusPtr, minusPtr,
                withForeignPtr, mallocBytes, free, allocaBytes)
import System.IO.Unsafe
import qualified Control.Monad.Fail as Fail
import qualified Data.ByteString.Internal as B

#include "MachDeps.h"

data Tup b c = Tup Addr# !b !c

type family GetState s

-- TODO remove
ptrToAddr :: Ptr a -> Addr#
ptrToAddr (Ptr a) = a

data GetEnv s = GetEnv
  { geBuf   :: !(ForeignPtr Word8)
  , geBegin :: Addr#
  , geEnd   :: Addr#
  , geTmp   :: Addr#
  }

newtype Get s a = Get
  { unGet :: GetEnv s -> Addr# -> GetState s -> IO (Tup (GetState s) a)
  }

instance Functor (Get s) where
  fmap f m = Get $ \e p s -> do
    Tup p' s' x <- unGet m e p s
    pure $! Tup p' s' (f x)
  {-# INLINE fmap #-}

instance Applicative (Get s) where
  pure a = Get $ \_ p s -> pure $! Tup p s a
  {-# INLINE pure #-}

  f <*> a = Get $ \e p s -> do
    Tup p' s' f' <- unGet f e p s
    Tup p'' s'' a'' <- unGet a e p' s'
    pure $! Tup p'' s'' (f' a'')
  {-# INLINE (<*>) #-}

  m1 *> m2 = do
    void m1
    m2
  {-# INLINE (*>) #-}

instance Monad (Get s) where
  m >>= f = Get $ \e p s -> do
    Tup p' s' x <- unGet m e p s
    unGet (f x) e p' s'
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
offset = Get $ \e p s -> pure $! Tup p s (Ptr p `minusPtr` Ptr (geBegin e))
{-# INLINE offset #-}

failGet :: (Int -> String -> GetException) -> String -> Get s a
failGet ctor msg = do
  off <- offset
  Get $ \_ _ _ -> throwIO (ctor off msg)

stateGet :: Get s (GetState s)
stateGet = Get $ \_ p s -> pure $! Tup p s s
{-# INLINE stateGet #-}

statePut :: Put s (PutState s)
statePut = Put $ \_ p s -> pure $! Tup p s s
{-# INLINE statePut #-}

setStateGet :: GetState s -> Get s ()
setStateGet s = Get $ \_ p _ -> pure $! Tup p s ()
{-# INLINE setStateGet #-}

setStatePut :: PutState s -> Put s ()
setStatePut s = Put $ \_ p _ -> pure $! Tup p s ()
{-# INLINE setStatePut #-}

runGetIO :: Get s a -> GetState s -> ByteString -> IO a
runGetIO m g s = run
  where run = withForeignPtr buf $ \p -> allocaBytes 8 $ \t -> do
          let env = GetEnv { geBuf = buf, geBegin = ptrToAddr p, geEnd = ptrToAddr (p `plusPtr` (pos + len)), geTmp = ptrToAddr t }
          Tup _ _ r <- unGet m env (ptrToAddr (p `plusPtr` pos)) g
          pure r
        (B.PS buf pos len) = s

-- | Run the Get monad applies a 'get'-based parser on the input ByteString
runGet :: Get s a -> GetState s -> ByteString -> Either String a
runGet m g s = unsafePerformIO $ catch (Right <$!> (runGetIO m g s)) handler
  where handler (x :: GetException) = pure $ Left $ displayException x
{-# NOINLINE runGet #-}

data Chunk = Chunk
  { chkBegin :: Addr#
  , chkEnd   :: Addr#
  }

type family PutState s

data PutEnv s = PutEnv
  { peChks :: !(IORef (NonEmpty Chunk))
  , peEnd  :: !(IORef (Ptr Word8))
  , peTmp  :: Addr#
  }

newtype Put s a = Put
  { unPut :: PutEnv s -> Addr# -> PutState s -> IO (Tup (PutState s) a) }

instance Functor (Put s) where
  fmap f m = Put $ \e p s -> do
    Tup p' s' x <- unPut m e p s
    pure $! Tup p' s' (f x)
  {-# INLINE fmap #-}

instance Applicative (Put s) where
  pure a = Put $ \_ p s -> pure $! Tup p s a
  {-# INLINE pure #-}

  f <*> a = Put $ \e p s -> do
    Tup p' s' f' <- unPut f e p s
    Tup p'' s'' a' <- unPut a e p' s'
    pure $! Tup p'' s'' (f' a')
  {-# INLINE (<*>) #-}

  m1 *> m2 = do
    void m1
    m2
  {-# INLINE (*>) #-}

instance Monad (Put s) where
  m >>= f = Put $ \e p s -> do
    Tup p' s' x <- unPut m e p s
    unPut (f x) e p' s'
  {-# INLINE (>>=) #-}

minChunkSize :: Int
minChunkSize = 0x10000
{-# INLINE minChunkSize #-}

newChunk :: Int -> IO Chunk
newChunk size = do
  let n = max size minChunkSize
  p <- mallocBytes n
  pure $! Chunk (ptrToAddr p) (ptrToAddr (p `plusPtr` n))
{-# INLINE newChunk #-}

-- | Ensure that @n@ bytes can be written.
grow :: Int -> Put s ()
grow n
  | n < 0 = error "grow: negative length"
  | otherwise = Put $ \e p s -> do
      end <- readIORef (peEnd e)
      if end `minusPtr` (Ptr p) >= n then
        pure $! Tup p s ()
      else
        doGrow e p s n
{-# INLINE grow #-}

doGrow :: PutEnv s -> Addr# -> PutState s -> Int -> IO (Tup (PutState s) ())
doGrow e p s n = do
  k <- newChunk n
  modifyIORef' (peChks e) $ \case
    (c:|cs) -> k :| c { chkEnd = p } : cs
  writeIORef (peEnd e) (Ptr (chkEnd k))
  pure $! Tup (chkBegin k) s ()
{-# NOINLINE doGrow #-}

chunksLength :: [Chunk] -> Int
chunksLength = foldr (\c s -> s + Ptr (chkEnd c) `minusPtr` Ptr (chkBegin c)) 0
{-# INLINE chunksLength #-}

catChunks :: [Chunk] -> IO ByteString
catChunks chks = B.create (chunksLength chks) $ \p ->
  void $ foldlM (\q c -> do
                    let n = Ptr (chkEnd c) `minusPtr` Ptr (chkBegin c)
                    B.memcpy q (Ptr (chkBegin c)) n
                    free $ Ptr (chkBegin c)
                    pure (q `plusPtr` n)) p $ reverse chks
{-# INLINE catChunks #-}

evalPutIO :: Put s a -> PutState s -> IO (a, ByteString)
evalPutIO p ps = do
  k <- newChunk 0
  chks <- newIORef (k:|[])
  end <- newIORef (Ptr (chkEnd k))
  Tup p' _ps' r <- allocaBytes 8 $ \t ->
    unPut p PutEnv { peChks = chks, peEnd = end, peTmp = ptrToAddr t } (chkBegin k) ps
  cs <- readIORef chks
  s <- case cs of
    (x:|xs) -> catChunks $ x { chkEnd = p' } : xs
  pure (r, s)

evalPut :: Put s a -> PutState s -> (a, ByteString)
evalPut s e = unsafePerformIO $ evalPutIO s e
{-# NOINLINE evalPut #-}
