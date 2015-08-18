{-# LANGUAGE Unsafe #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE ForeignFunctionInterface #-}
module Data.Transient.Primitive.Unsafe
  ( unsafeCheckMutableArray
  , unsafeCheckSmallMutableArray
  , unsafeIndexMutableArray
  , unsafeIndexMutableArrayM
  , unsafeIndexSmallMutableArray
  , unsafeIndexSmallMutableArrayM
  -- * Custom foreign primitives
  , unsafeCheckMutableArray#
  , unsafeCheckSmallMutableArray#
  ) where

import Control.Monad.Primitive
import Data.Primitive.Array
import Data.Transient.Primitive.SmallArray
import GHC.Exts
import Unsafe.Coerce

foreign import prim "checkMutableArrayzh"      unsafeCheckMutableArray#      :: MutableArray# s a -> State# s -> (# State# s, Int# #) 
foreign import prim "checkSmallMutableArrayzh" unsafeCheckSmallMutableArray# :: SmallMutableArray# s a -> State# s -> (# State# s, Int# #)

-- | This returns 'True' if the 'MutableArray' is unfrozen and can still be mutated.
unsafeCheckMutableArray :: PrimMonad m => MutableArray (PrimState m) a -> m Bool
unsafeCheckMutableArray (MutableArray m) = primitive $ \s -> case unsafeCheckMutableArray# m s of
  (# s', i #) -> (# s', isTrue# i #)

-- | This returns 'True' if the 'SmallMutableArray' is unfrozen and can still be mutated.
unsafeCheckSmallMutableArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> m Bool
unsafeCheckSmallMutableArray (SmallMutableArray m) = primitive $ \s -> case unsafeCheckSmallMutableArray# m s of
  (# s', i #) -> (# s', isTrue# i #)

unsafeIndexMutableArray :: MutableArray s a -> Int -> a
unsafeIndexMutableArray = unsafeCoerce indexArray
{-# INLINE unsafeIndexMutableArray #-}

unsafeIndexMutableArrayM :: forall m s a. Monad m => MutableArray s a -> Int -> m a
unsafeIndexMutableArrayM = unsafeCoerce (indexArrayM :: Array a -> Int -> m a)
{-# INLINE unsafeIndexMutableArrayM #-}

unsafeIndexSmallMutableArray :: SmallMutableArray s a -> Int -> a
unsafeIndexSmallMutableArray = unsafeCoerce indexSmallArray
{-# INLINE unsafeIndexSmallMutableArray #-}

unsafeIndexSmallMutableArrayM :: forall m s a. Monad m => SmallMutableArray s a -> Int -> m a
unsafeIndexSmallMutableArrayM = unsafeCoerce (indexSmallArrayM :: SmallArray a -> Int -> m a)
{-# INLINE unsafeIndexSmallMutableArrayM #-}
