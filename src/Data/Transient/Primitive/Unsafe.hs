{-# LANGUAGE Unsafe #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE ForeignFunctionInterface #-}
module Data.Transient.Primitive.Unsafe
  ( checkMutableArray#
  , checkSmallMutableArray#
  ) where

import GHC.Prim

-- check if this mutable array is actually still mutable internally.
foreign import prim "checkMutableArrayzh"      checkMutableArray#      :: MutableArray# s a -> State# s -> (# State# s, Int# #) 
foreign import prim "checkSmallMutableArrayzh" checkSmallMutableArray# :: SmallMutableArray# s a -> State# s -> (# State# s, Int# #)
