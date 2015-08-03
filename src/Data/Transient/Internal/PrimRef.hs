{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RoleAnnotations #-}

module Data.Transient.Internal.PrimRef
  ( 
  -- * Primitive References
    PrimRef
  , newPrimRef
  , newPinnedPrimRef
  , newAlignedPinnedPrimRef
  , readPrimRef
  , writePrimRef
  , primRefContents
  -- * Frozen Primitive References
  , FrozenPrimRef
  , unsafeFreezePrimRef
  , unsafeThawPrimRef
  , indexFrozenPrimRef
  , frozenPrimRefContents
  ) where

import Control.Monad.Primitive
import Data.Primitive
import Data.Primitive.ByteArray
import GHC.Prim

--------------------------------------------------------------------------------
-- * Primitive References
--------------------------------------------------------------------------------

newtype PrimRef s a = PrimRef (MutableByteArray s)

type role PrimRef nominal nominal

-- | Create a primitive reference.
newPrimRef :: (PrimMonad m, Prim a) => a -> m (PrimRef (PrimState m) a)
newPrimRef a = do
  m <- newByteArray (sizeOf a)
  writeByteArray m 0 a
  return (PrimRef m)
{-# INLINE newPrimRef #-}

-- | Create a pinned primitive reference.
newPinnedPrimRef :: (PrimMonad m, Prim a) => a -> m (PrimRef (PrimState m) a)
newPinnedPrimRef a = do
  m <- newPinnedByteArray (sizeOf a)
  writeByteArray m 0 a
  return (PrimRef m)
{-# INLINE newPinnedPrimRef #-}

-- | Create a pinned primitive reference with the appropriate alignment for its contents.
newAlignedPinnedPrimRef :: (PrimMonad m, Prim a) => a -> m (PrimRef (PrimState m) a)
newAlignedPinnedPrimRef a = do
  m <- newAlignedPinnedByteArray (sizeOf a) (alignment a)
  writeByteArray m 0 a
  return (PrimRef m)
{-# INLINE newAlignedPinnedPrimRef #-}

-- | Read a primitive value from the reference
readPrimRef :: (PrimMonad m, Prim a) => PrimRef (PrimState m) a -> m a
readPrimRef (PrimRef m) = readByteArray m 0
{-# INLINE readPrimRef #-}

-- | Write a primitive value to the reference
writePrimRef :: (PrimMonad m, Prim a) => PrimRef (PrimState m) a -> a -> m ()
writePrimRef (PrimRef m) a = writeByteArray m 0 a
{-# INLINE writePrimRef #-}

instance Eq (PrimRef s a) where
  PrimRef m == PrimRef n = sameMutableByteArray m n
  {-# INLINE (==) #-}

-- | Yield a pointer to the PrimRef's data. This operation is only safe on pinned byte arrays allocated by
-- 'newPinnedPrimRef' or 'newAlignedPinnedPrimRef'.
primRefContents :: PrimRef s a -> Addr
primRefContents (PrimRef m) = mutableByteArrayContents m
{-# INLINE primRefContents #-}

--------------------------------------------------------------------------------
-- * Frozen Primitive References
--------------------------------------------------------------------------------

-- | Convert a mutable 'PrimRef' to an immutable one without copying. The reference should not be modified after the conversion.
unsafeFreezePrimRef :: PrimMonad m => PrimRef (PrimState m) a -> m (FrozenPrimRef a)
unsafeFreezePrimRef (PrimRef m) = FrozenPrimRef <$> unsafeFreezeByteArray m
{-# INLINE unsafeFreezePrimRef #-}

newtype FrozenPrimRef a = FrozenPrimRef ByteArray

type role FrozenPrimRef nominal

-- | Read the stored primitive value from the frozen reference.
indexFrozenPrimRef :: Prim a => FrozenPrimRef a -> a
indexFrozenPrimRef (FrozenPrimRef ba) = indexByteArray ba 0
{-# INLINE indexFrozenPrimRef #-}

-- | Convert an immutable primitive reference to a mutable one without copying. The original reference should not be used after the conversion.
unsafeThawPrimRef :: PrimMonad m => FrozenPrimRef a -> m (PrimRef (PrimState m) a)
unsafeThawPrimRef (FrozenPrimRef m) = PrimRef <$> unsafeThawByteArray m
{-# INLINE unsafeThawPrimRef #-}

-- | Yield a pointer to the PrimRef's data. This operation is only safe on pinned byte arrays allocated by
-- 'newPinnedPrimRef' or 'newPinnedAlignedPrimRef' and then subsequently frozen.
frozenPrimRefContents :: FrozenPrimRef a -> Addr
frozenPrimRefContents (FrozenPrimRef m) = byteArrayContents m
{-# INLINE frozenPrimRefContents #-}
