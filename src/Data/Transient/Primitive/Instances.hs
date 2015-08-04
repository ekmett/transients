{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Transient.Primitive.Instances
  () where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.Foldable as Foldable
import Data.Function (on)
import Data.Primitive
import Data.Primitive.MachDeps
import GHC.Exts
import Text.Read

unI# :: Int -> Int#
unI# (I# x) = x

instance Prim (Ptr a) where
  sizeOf# _ = unI# sIZEOF_PTR
  alignment# _ = unI# aLIGNMENT_PTR
  indexByteArray# arr i = Ptr (indexAddrArray# arr i)
  readByteArray# arr i s = case readAddrArray# arr i s of
    (# s', a #) -> (# s', Ptr a #)
  writeByteArray# arr i (Ptr a) s = writeAddrArray# arr i a s
  setByteArray# arr i n (Ptr a) s = case unsafeCoerce# (internal (setAddrArray# arr i n a)) s of
    (# s', _ #) -> s'
  indexOffAddr# addr i = Ptr (indexAddrOffAddr# addr i)
  readOffAddr# addr i s = case readAddrOffAddr# addr i s of
    (# s', a #) -> (# s', Ptr a #)
  writeOffAddr# addr i (Ptr a) s = writeAddrOffAddr# addr i a s
  setOffAddr# addr i n (Ptr a) s = case unsafeCoerce# (internal (setAddrOffAddr# addr i n a)) s of
    (# s', _ #) -> s'

foreign import ccall unsafe "primitive-memops.h hsprimitive_memset_Ptr"
  setAddrArray# :: MutableByteArray# s -> Int# -> Int# -> Addr# -> IO ()

foreign import ccall unsafe "primitive-memops.h hsprimitive_memset_Ptr"
  setAddrOffAddr# :: Addr# -> Int# -> Int# -> Addr# -> IO ()

--------------------------------------------------------------------------------
-- * Missing Array instances
--------------------------------------------------------------------------------

instance Functor Array where
  fmap f !i = runST $ do
    let n = length i
    o <- newArray n undefined
    let go !k
          | k == n = return ()
          | otherwise = do
            a <- indexArrayM i k
            writeArray o k (f a)
            go (k+1)
    go 0
    unsafeFreezeArray o

instance Foldable Array where
  foldr f z arr = go 0 where
    n = length arr
    go !k
      | k == n    = z
      | otherwise = f (indexArray arr k) (go (k+1))

  foldl f z arr = go (length arr - 1) where
    go !k
      | k < 0 = z
      | otherwise = f (go (k-1)) (indexArray arr k)

  foldr' f z arr = go 0 where
    n = length arr
    go !k
      | k == n    = z
      | r <- indexArray arr k = r `seq` f r (go (k+1))

  foldl' f z arr = go (length arr - 1) where
    go !k
      | k < 0 = z
      | r <- indexArray arr k = r `seq` f (go (k-1)) r

  length (Array ary) = I# (sizeofArray# ary)
  {-# INLINE length #-}

instance Traversable Array where
  traverse f a = fromListN (length a) <$> traverse f (Foldable.toList a)

instance Applicative Array where
  pure a = runST $ newArray 1 a >>= unsafeFreezeArray
  (m :: Array (a -> b)) <*> (n :: Array a) = runST $ do
      o <- newArray (lm * ln) undefined
      outer o 0 0
    where 
      lm = length m
      ln = length n
      outer :: MutableArray s b -> Int -> Int -> ST s (Array b)
      outer o !i p
        | i < lm = do
            f <- indexArrayM m i
            inner o i 0 f p
        | otherwise = unsafeFreezeArray o
      inner :: MutableArray s b -> Int -> Int -> (a -> b) -> Int -> ST s (Array b)
      inner o i !j f !p
        | j < ln = do
            x <- indexArrayM n j
            writeArray o p (f x)
            inner o i (j + 1) f (p + 1)
        | otherwise = outer o (i + 1) p

instance Monad Array where
  return = pure
  (>>) = (*>)
  m >>= f = foldMap f m

instance MonadPlus Array where
  mzero = empty 
  mplus = (<|>)

instance Alternative Array where
  empty = runST $ newArray 0 undefined >>= unsafeFreezeArray
  m@(Array pm) <|> n@(Array pn) = runST $ case length m of
     lm@(I# ilm) -> case length n of 
       ln@(I# iln) -> do
         o@(MutableArray po) <- newArray (lm + ln) undefined
         primitive_ $ \s -> case copyArray# pm 0# po 0# ilm s of
           s' -> copyArray# pn 0# po ilm iln s'
         unsafeFreezeArray o

instance Monoid (Array a) where
  mempty = empty
  mappend = (<|>)
    
instance Eq a => Eq (Array a) where
  (==) = (==) `on` Foldable.toList

instance Ord a => Ord (Array a) where
  compare = compare `on` Foldable.toList

instance Show a => Show (Array a) where
  showsPrec d arr = showParen (d > 10) $ 
    showString "fromList " . showsPrec 11 (Foldable.toList arr)

instance Read a => Read (Array a) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    m <- step readPrec
    return (fromList m)

instance IsList (Array a) where
  type Item (Array a) = a
  fromList = undefined -- TODO
  fromListN = undefined -- TODO
  toList = Foldable.toList

--------------------------------------------------------------------------------
-- * Missing MutableArray instances
--------------------------------------------------------------------------------

instance Eq (MutableArray s a) where
  (==) = sameMutableArray

--------------------------------------------------------------------------------
-- * Missing MutableByteArray instances
--------------------------------------------------------------------------------

instance Eq (MutableByteArray s) where
  (==) = sameMutableByteArray
