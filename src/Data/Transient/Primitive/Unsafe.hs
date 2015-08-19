{-# LANGUAGE CPP #-}
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
  -- * Custom foreign primitives
  , unsafeCheckMutableArray#
  , unsafeCheckSmallMutableArray#
  ) where

import Control.Monad.Primitive
import Data.Primitive.Array
import Data.Transient.Primitive.SmallArray
import GHC.Exts

#ifndef HLINT
foreign import prim "checkMutableArrayzh"      unsafeCheckMutableArray#      :: MutableArray# s a -> State# s -> (# State# s, Int# #) 
foreign import prim "checkSmallMutableArrayzh" unsafeCheckSmallMutableArray# :: SmallMutableArray# s a -> State# s -> (# State# s, Int# #)
#endif

-- | This returns 'True' if the 'MutableArray' is unfrozen and can still be mutated.
unsafeCheckMutableArray :: PrimMonad m => MutableArray (PrimState m) a -> m Bool
unsafeCheckMutableArray (MutableArray m) = primitive $ \s -> case unsafeCheckMutableArray# m s of
  (# s', i #) -> (# s', isTrue# i #)

-- | This returns 'True' if the 'SmallMutableArray' is unfrozen and can still be mutated.
unsafeCheckSmallMutableArray :: PrimMonad m => SmallMutableArray (PrimState m) a -> m Bool
unsafeCheckSmallMutableArray (SmallMutableArray m) = primitive $ \s -> case unsafeCheckSmallMutableArray# m s of
  (# s', i #) -> (# s', isTrue# i #)
