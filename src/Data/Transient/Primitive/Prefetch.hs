{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE Unsafe #-}
module Data.Transient.Primitive.Prefetch
  ( prefetchByteArray0
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
  , prefetchPrimRef0
  , prefetchPrimRef1
  , prefetchPrimRef2
  , prefetchPrimRef3
  , prefetchFrozenPrimRef0
  , prefetchFrozenPrimRef1
  , prefetchFrozenPrimRef2
  , prefetchFrozenPrimRef3
  ) where

import GHC.Prim
import GHC.Types
import Control.Monad.Primitive
import Data.Primitive
import Data.Transient.Primitive.PrimRef

prefetchByteArray0, prefetchByteArray1, prefetchByteArray2, prefetchByteArray3 :: PrimMonad m => ByteArray -> Int -> m ()
prefetchByteArray0 (ByteArray m) (I# i) = primitive $ \s -> case prefetchByteArray0# m i s of s' -> (# s', () #)
prefetchByteArray1 (ByteArray m) (I# i) = primitive $ \s -> case prefetchByteArray1# m i s of s' -> (# s', () #)
prefetchByteArray2 (ByteArray m) (I# i) = primitive $ \s -> case prefetchByteArray2# m i s of s' -> (# s', () #)
prefetchByteArray3 (ByteArray m) (I# i) = primitive $ \s -> case prefetchByteArray3# m i s of s' -> (# s', () #)

prefetchMutableByteArray0, prefetchMutableByteArray1, prefetchMutableByteArray2, prefetchMutableByteArray3 :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> m ()
prefetchMutableByteArray0 (MutableByteArray m) (I# i) = primitive $ \s -> case prefetchMutableByteArray0# m i s of s' -> (# s', () #)
prefetchMutableByteArray1 (MutableByteArray m) (I# i) = primitive $ \s -> case prefetchMutableByteArray1# m i s of s' -> (# s', () #)
prefetchMutableByteArray2 (MutableByteArray m) (I# i) = primitive $ \s -> case prefetchMutableByteArray2# m i s of s' -> (# s', () #)
prefetchMutableByteArray3 (MutableByteArray m) (I# i) = primitive $ \s -> case prefetchMutableByteArray3# m i s of s' -> (# s', () #)

prefetchValue0, prefetchValue1, prefetchValue2, prefetchValue3 :: PrimMonad m => a -> m ()
prefetchValue0 a = primitive $ \s -> case prefetchValue0# a s of s' -> (# s', () #)
prefetchValue1 a = primitive $ \s -> case prefetchValue1# a s of s' -> (# s', () #)
prefetchValue2 a = primitive $ \s -> case prefetchValue2# a s of s' -> (# s', () #)
prefetchValue3 a = primitive $ \s -> case prefetchValue3# a s of s' -> (# s', () #)

prefetchPrimRef0, prefetchPrimRef1, prefetchPrimRef2, prefetchPrimRef3 :: PrimMonad m => PrimRef (PrimState m) a -> m ()
prefetchPrimRef0 (PrimRef m) = prefetchMutableByteArray0 m 0
prefetchPrimRef1 (PrimRef m) = prefetchMutableByteArray1 m 0
prefetchPrimRef2 (PrimRef m) = prefetchMutableByteArray2 m 0
prefetchPrimRef3 (PrimRef m) = prefetchMutableByteArray3 m 0

prefetchFrozenPrimRef0, prefetchFrozenPrimRef1, prefetchFrozenPrimRef2, prefetchFrozenPrimRef3 :: PrimMonad m => FrozenPrimRef a -> m ()
prefetchFrozenPrimRef0 (FrozenPrimRef m) = prefetchByteArray0 m 0
prefetchFrozenPrimRef1 (FrozenPrimRef m) = prefetchByteArray1 m 0
prefetchFrozenPrimRef2 (FrozenPrimRef m) = prefetchByteArray2 m 0
prefetchFrozenPrimRef3 (FrozenPrimRef m) = prefetchByteArray3 m 0
