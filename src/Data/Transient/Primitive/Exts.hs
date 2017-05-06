{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE Unsafe #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Transient.Primitive.Exts
  (
  -- * MutVar Primitives
    sameMutVar
  , casMutVar
  -- * Array Primitives
  , sizeOfArray
  , sizeOfMutableArray
  , casArray
  -- * ByteArray Primitives
  , sizeOfByteArray
  , sizeOfMutableByteArray
  , casIntArray
  , atomicReadIntArray
  , atomicWriteIntArray
  , fetchAddIntArray
  , fetchSubIntArray
  , fetchAndIntArray
  , fetchNandIntArray
  , fetchOrIntArray
  , fetchXorIntArray
  -- * Prefetching
  , prefetchByteArray0
  , prefetchByteArray1
  , prefetchByteArray2
  , prefetchByteArray3
  , prefetchMutableByteArray0
  , prefetchMutableByteArray1
  , prefetchMutableByteArray2
  , prefetchMutableByteArray3
  , prefetchValue0
  , prefetchValue1
  , prefetchValue2
  , prefetchValue3
  ) where

import Control.Applicative
import Control.DeepSeq
import Control.Lens
import Control.Monad.ST
import Control.Monad.Primitive
import Data.Primitive.Array
import Data.Primitive.ByteArray
import Data.Primitive.MutVar
import GHC.Exts

--------------------------------------------------------------------------------
-- * MutVar Primitives
--------------------------------------------------------------------------------

casMutVar :: PrimMonad m => MutVar (PrimState m) a -> a -> a -> m (Int, a)
casMutVar (MutVar m) a b = primitive $ \s -> case casMutVar# m a b s of
  (# s', i, r #) -> (# s', (I# i, r) #)

sameMutVar :: MutVar s a -> MutVar s a -> Bool
sameMutVar (MutVar a) (MutVar b) = isTrue# (sameMutVar# a b)

--------------------------------------------------------------------------------
-- * Array Primitives
--------------------------------------------------------------------------------

sizeOfArray :: Array a -> Int
sizeOfArray (Array m) = I# (sizeofArray# m)

sizeOfMutableArray :: MutableArray s a -> Int
sizeOfMutableArray (MutableArray m) = I# (sizeofMutableArray# m)

casArray :: PrimMonad m => MutableArray (PrimState m) a -> Int -> a -> a -> m (Int, a)
casArray (MutableArray m) (I# i) x y = primitive $ \s -> case casArray# m i x y s of
  (# s', i', z #) -> (# s', (I# i', z) #)

--------------------------------------------------------------------------------
-- * ByteArray Primitives
--------------------------------------------------------------------------------

sizeOfByteArray :: ByteArray -> Int
sizeOfByteArray (ByteArray m) = I# (sizeofByteArray# m)

sizeOfMutableByteArray :: MutableByteArray s -> Int
sizeOfMutableByteArray (MutableByteArray m) = I# (sizeofMutableByteArray# m)

casIntArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> Int -> m Int
casIntArray (MutableByteArray m) (I# i) (I# x) (I# y) = primitive $ \s -> case casIntArray# m i x y s of
  (# s', i' #) -> (# s', I# i' #)

atomicReadIntArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> m Int
atomicReadIntArray (MutableByteArray m) (I# i) = primitive $ \s -> case atomicReadIntArray# m i s of
  (# s', i' #) -> (# s', I# i' #)

atomicWriteIntArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> m ()
atomicWriteIntArray (MutableByteArray m) (I# i) (I# j) = primitive_ $ \s -> atomicWriteIntArray# m i j s

fetchAddIntArray  :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> m Int
fetchAddIntArray (MutableByteArray m) (I# i) (I# j) = primitive $ \s -> case fetchAddIntArray# m i j s of
  (# s', k #) -> (# s', I# k #)

fetchSubIntArray  :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> m Int
fetchSubIntArray (MutableByteArray m) (I# i) (I# j) = primitive $ \s -> case fetchSubIntArray# m i j s of
  (# s', k #) -> (# s', I# k #)

fetchAndIntArray  :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> m Int
fetchAndIntArray (MutableByteArray m) (I# i) (I# j) = primitive $ \s -> case fetchAndIntArray# m i j s of
  (# s', k #) -> (# s', I# k #)

fetchNandIntArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> m Int
fetchNandIntArray (MutableByteArray m) (I# i) (I# j) = primitive $ \s -> case fetchNandIntArray# m i j s of
  (# s', k #) -> (# s', I# k #)

fetchOrIntArray   :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> m Int
fetchOrIntArray (MutableByteArray m) (I# i) (I# j) = primitive $ \s -> case fetchOrIntArray# m i j s of
  (# s', k #) -> (# s', I# k #)

fetchXorIntArray  :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Int -> m Int
fetchXorIntArray (MutableByteArray m) (I# i) (I# j) = primitive $ \s -> case fetchXorIntArray# m i j s of
  (# s', k #) -> (# s', I# k #)

--------------------------------------------------------------------------------
-- * Prefetching
--------------------------------------------------------------------------------

prefetchByteArray0, prefetchByteArray1, prefetchByteArray2, prefetchByteArray3 :: PrimMonad m => ByteArray -> Int -> m ()
prefetchByteArray0 (ByteArray m) (I# i) = primitive_ $ \s -> prefetchByteArray0# m i s
prefetchByteArray1 (ByteArray m) (I# i) = primitive_ $ \s -> prefetchByteArray1# m i s
prefetchByteArray2 (ByteArray m) (I# i) = primitive_ $ \s -> prefetchByteArray2# m i s
prefetchByteArray3 (ByteArray m) (I# i) = primitive_ $ \s -> prefetchByteArray3# m i s

prefetchMutableByteArray0, prefetchMutableByteArray1, prefetchMutableByteArray2, prefetchMutableByteArray3 :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> m ()
prefetchMutableByteArray0 (MutableByteArray m) (I# i) = primitive_ $ \s -> prefetchMutableByteArray0# m i s
prefetchMutableByteArray1 (MutableByteArray m) (I# i) = primitive_ $ \s -> prefetchMutableByteArray1# m i s
prefetchMutableByteArray2 (MutableByteArray m) (I# i) = primitive_ $ \s -> prefetchMutableByteArray2# m i s
prefetchMutableByteArray3 (MutableByteArray m) (I# i) = primitive_ $ \s -> prefetchMutableByteArray3# m i s

prefetchValue0, prefetchValue1, prefetchValue2, prefetchValue3 :: PrimMonad m => a -> m ()
prefetchValue0 a = primitive_ $ \s -> prefetchValue0# a s
prefetchValue1 a = primitive_ $ \s -> prefetchValue1# a s
prefetchValue2 a = primitive_ $ \s -> prefetchValue2# a s
prefetchValue3 a = primitive_ $ \s -> prefetchValue3# a s

--------------------------------------------------------------------------------
-- * Missing Array instances
--------------------------------------------------------------------------------

instance NFData a => NFData (Array a) where
  rnf a0 = go a0 (length a0) 0 where
    go !a !n !i
      | i >= n = ()
      | otherwise = rnf (indexArray a i) `seq` go a n (i+1)
  {-# INLINE rnf #-}

-- lens machinery

type instance Index (Array a) = Int
type instance IxValue (Array a) = a

instance Ixed (Array a) where
  ix i f m
    | 0 <= i && i < n = go <$> f (indexArray m i)
    | otherwise = pure m
    where
      n = sizeOfArray m
      go a = runST $ do
        o <- newArray n undefined
        copyArray o 0 m 0 n
        writeArray o i a
        unsafeFreezeArray o

instance AsEmpty (Array a) where
  _Empty = nearly empty null

instance Cons (Array a) (Array b) a b where
  _Cons = prism hither yon where
    hither (a,m) | n <- sizeOfArray m = runST $ do
      o <- newArray (n + 1) a
      copyArray o 1 m 0 n
      unsafeFreezeArray o
    yon m
      | n <- sizeOfArray m
      , n > 0 = Right
        ( indexArray m 0
        , runST $ do
          o <- newArray (n - 1) undefined
          copyArray o 0 m 1 (n - 1)
          unsafeFreezeArray o
        )
      | otherwise = Left empty

instance Snoc (Array a) (Array b) a b where
  _Snoc = prism hither yon where
    hither (m,a) | n <- sizeOfArray m = runST $ do
      o <- newArray (n + 1) a
      copyArray o 0 m 0 n
      unsafeFreezeArray o
    yon m
      | n <- sizeOfArray m
      , n > 0 = Right
        ( runST $ do
          o <- newArray (n - 1) undefined
          copyArray o 0 m 0 (n - 1)
          unsafeFreezeArray o
        , indexArray m 0
        )
      | otherwise = Left empty


--------------------------------------------------------------------------------
-- * Missing ByteArray instances
--------------------------------------------------------------------------------

instance Monoid ByteArray where
  mempty = runST $ newByteArray 0 >>= unsafeFreezeByteArray
  {-# NOINLINE mempty #-}
  mappend m n = runST $ do
    o <- newByteArray (lm + ln)
    copyByteArray o 0 m 0 lm
    copyByteArray o lm n 0 ln
    unsafeFreezeByteArray o
    where lm = sizeOfByteArray m
          ln = sizeOfByteArray n
  {-# INLINE mappend #-}

-- * lens

instance AsEmpty ByteArray where
  _Empty = nearly mempty $ \s -> sizeOfByteArray s == 0

--------------------------------------------------------------------------------
-- * Missing MutableByteArray instances
--------------------------------------------------------------------------------

instance Eq (MutableByteArray s) where
  (==) = sameMutableByteArray

