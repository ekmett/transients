{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# OPTIONS_GHC -Wall -funbox-strict-fields -fno-warn-orphans -fno-warn-type-defaults -O2 #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
module Main where

import Control.DeepSeq
import Control.Exception (evaluate)
import Criterion.Main
import Criterion.Types
import Data.Transient.WordMap as D
import Data.Foldable
import Data.Maybe (fromMaybe)
import Data.Word
import Prelude hiding (lookup, length, foldr)
import qualified Data.IntMap as M
import qualified Fingered as F
import qualified Data.HashMap.Lazy as H
import GHC.Exts as E

main :: IO ()
main = do
    evaluate $ rnf [denseM, sparseM, sparseM']
    evaluate $ rnf [denseW, sparseW, sparseW']
    evaluate $ rnf [denseH, sparseH, sparseH']
    evaluate $ rnf [denseF, sparseF, sparseF']
    evaluate $ rnf [elems,  sElems,  sElemsSearch]
    evaluate $ rnf [keys,   sKeys, sKeysSearch]
    evaluate $ rnf [values, sValues]
    evaluate $ rnf [welems,  wsElems,  wsElemsSearch]
    evaluate $ rnf [wkeys,   wsKeys, wsKeysSearch]
    evaluate $ rnf [wvalues, wsValues]
    defaultMainWith (defaultConfig { timeLimit = 1 })
        [ bgroup "lookup"
            [ bgroup "present"
                [ bench "IntMap"  $ whnf (\m -> foldl' (\n k -> fromMaybe n (M.lookup k m)) 0 keys) denseM
                , bench "WordMap" $ whnf (\m -> foldl' (\n k -> fromMaybe n (D.lookup k m)) 0 wkeys) denseW
                , bench "Fingered" $ whnf (\m -> foldl' (\n k -> fromMaybe n (F.lookup k m)) 0 wkeys) denseF
                , bench "HashMap" $ whnf (\m -> foldl' (\n k -> fromMaybe n (H.lookup k m)) 0 wkeys) denseH
                ]
            , bgroup "absent"
                [ bench "IntMap"  $ whnf (\m -> foldl' (\n k -> fromMaybe n (M.lookup k m)) 0 sKeysSearch) sparseM
                , bench "WordMap" $ whnf (\m -> foldl' (\n k -> fromMaybe n (D.lookup k m)) 0 wsKeysSearch) sparseW
                , bench "Fingered" $ whnf (\m -> foldl' (\n k -> fromMaybe n (F.lookup k m)) 0 wsKeysSearch) sparseF
                , bench "HashMap" $ whnf (\m -> foldl' (\n k -> fromMaybe n (H.lookup k m)) 0 wsKeysSearch) sparseH
                ]
            ]
        , bgroup "insert"
            [ bgroup "present"
                [ bench "IntMap"  $ whnf (\m0 -> foldl' (\m (k, v) -> M.insert k v m) m0 elems) denseM
                , bench "WordMap" $ whnf (\m0 -> foldl' (\m (k, v) -> D.insert k v m) m0 welems) denseW
                , bench "Fingered" $ whnf (\m0 -> foldl' (\m (k, v) -> F.insert k v m) m0 welems) denseF
                , bench "HashMap" $ whnf (\m0 -> foldl' (\m (k, v) -> H.insert k v m) m0 welems) denseH
                , bench "WordMap+1" $ whnf (\m0 -> foldl' (\m (k, v) -> D.insert k (v+1) m) m0 welems) denseW
                , bench "Fingered+1" $ whnf (\m0 -> foldl' (\m (k, v) -> F.insert k (v+1) m) m0 welems) denseF
                , bench "HashMap+1" $ whnf (\m0 -> foldl' (\m (k, v) -> H.insert k (v+1) m) m0 welems) denseH
                ]
            , bgroup "absent"
                [ bench "IntMap" $ whnf (\m0 -> foldl' (\m (k, v) -> M.insert k v m) m0 sElemsSearch) sparseM
                , bench "WordMap" $ whnf (\m0 -> foldl' (\m (k, v) -> D.insert k v m) m0 wsElemsSearch) sparseW
                , bench "Fingered" $ whnf (\m0 -> foldl' (\m (k, v) -> F.insert k v m) m0 wsElemsSearch) sparseF
                , bench "HashMap" $ whnf (\m0 -> foldl' (\m (k, v) -> H.insert k v m) m0 wsElemsSearch) sparseH
                ]
            ]
        ]
  where
    denseM = M.fromAscList elems :: M.IntMap Int
    denseW = fromList welems :: D.WordMap Word64
    denseF = E.fromList welems :: F.WordMap Word64
    denseH = H.fromList welems :: H.HashMap Word64 Word64
    sparseM = M.fromAscList sElems :: M.IntMap Int
    sparseW = fromList wsElems :: D.WordMap Word64
    sparseF = E.fromList wsElems :: F.WordMap Word64
    sparseH = H.fromList wsElems :: H.HashMap Word64 Word64
    sparseM' = M.fromAscList sElemsSearch :: M.IntMap Int
    sparseW' = fromList wsElemsSearch :: D.WordMap Word64
    sparseF' = E.fromList wsElemsSearch :: F.WordMap Word64
    sparseH' = H.fromList wsElemsSearch :: H.HashMap Word64 Word64

    elems = zip keys values
    keys = [1..2^12]
    values = [1..2^12]
    sElems = zip sKeys sValues
    sElemsSearch = zip sKeysSearch sValues
    sKeys = [1,3..2^12]
    sKeysSearch = [2,4..2^12]
    sValues = [1,3..2^12]

    welems = zip wkeys wvalues
    wkeys = [1..2^12]
    wvalues = [1..2^12]
    wsElems = zip wsKeys wsValues
    wsElemsSearch = zip wsKeysSearch wsValues
    wsKeys = [1,3..2^12]
    wsKeysSearch = [2,4..2^12]
    wsValues = [1,3..2^12]
