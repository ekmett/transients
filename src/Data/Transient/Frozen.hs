{-# LANGUAGE TypeFamilies, RankNTypes, KindSignatures, PolyKinds #-}
module Data.Transient.Frozen 
  ( Frozen(..)
  , modify, query
  ) where

import Control.Monad.Primitive
import Control.Monad.ST

class Frozen (t :: k -> *) where
  data Transient t :: * -> k -> *

  -- | /O(1)/. amortized conversion from a mutable structure to an immutable one
  freeze :: PrimMonad m => Transient t (PrimState m) a -> m (t a)

  -- | /O(1)/. worst-case conversion from an immutable structure to a mutable one
  thaw :: t a -> Transient t s a

-- | /O(1) + modification time/. to modify an immutable structure with mutable operations.
--
-- The transient passed to this function is considered frozen
modify :: Frozen t => (forall s. Transient t s a -> ST s (Transient t s b)) -> t a -> t b
modify f s = runST $ do
  x <- f (thaw s) 
  freeze x
{-# INLINE modify #-}

-- | /O(1) + query time/. Query a mutable structure with queries designed for an immutable structure.
--
-- This does _not_ destroy the transient, although, it does mean subsequent actions need to copy-on-write from scratch.
--
-- After @query f wm@, @wm@ is considered frozen and may be reused.

query  :: (PrimMonad m, Frozen t) => (t a -> r) -> Transient t (PrimState m) a -> m r
query f s = f <$> freeze s
{-# INLINE query #-}
