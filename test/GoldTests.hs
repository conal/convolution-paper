{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-binds -Wno-unused-imports #-}

module Main where

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap

-- TODO: try strict variants also

import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

-- import Data.MemoTrie

import Semi
-- import Language
-- import Decomp
import RegExp
import LTrie

main :: IO ()
main = do
  defaultMain basicTests

basicTests :: TestTree
basicTests = testGroup "Various representations"
  [ testGroup "" []
  , tests @(RegExp ((->) Char)) @Bool "FunRegExp"
  , tests @(RegExp (Map  Char)) @Bool "MapRegExp"
  , tests @(LTrie  ((->) Char)) @Bool "FunTrie"
  , tests @(LTrie  (Map  Char)) @Bool "MapTrie"
  , tests @(LTrie  CharMap) @Bool "IMapTrie"
  ]

-- TODO: some tests with s other than Bool.

-- tests' :: forall x. Semiring x => String -> TestTree
-- tests' = undefined

tests :: forall f b.
  ( HasSingle f b, Key f ~ String, StarSemiring (f b), Semiring b, Show b )
  => String -> TestTree
tests group = testGroup group
  [ testGroup "" []

  , gold "as-eps"                $ as ! ""
  , gold "as-a"                  $ as ! "a"
  , gold "ass-eps"               $ ass ! ""
  , groupNot ["Pred","F"] $
    gold "ass-a"                 $ ass ! "a"

  , gold "pp-pi"                 $ pp ! "pi"
  , gold "pp-pig"                $ pp ! "pig"
  , gold "pp-pig"                $ pp ! "pig"
  , gold "pp-pink"               $ pp ! "pink"
  , gold "pp-ping"               $ pp ! "ping"

  , gold "pps-q"                 $ pps ! "q"
  , gold "pps-pig"               $ pps ! "pig"
  , gold "pps-pigpig"            $ pps ! "pigpig"
  , gold "pps-pigping"           $ pps ! "pigping"
  , gold "pps-pinkpigpinkpigpig" $ pps ! "pinkpigpinkpigpig"

  -- These recursive examples are challenging.
  , groupNot ["MapRegExp"] $
    testGroup "anbn"
    [ gold "anbn-eps"              $ anbn ! ""
    , gold "anbn-ab"               $ anbn ! "ab"
    , gold "anbn-ba"               $ anbn ! "ba"
    , gold "anbn-aabb"             $ anbn ! "aabb"
    , gold "anbn-aacbb"            $ anbn ! "aacbb"
    , gold "anbn-aaabbb"           $ anbn ! "aaabbb"
    , gold "anbn-aaabbbb"          $ anbn ! "aaabbbb"
    ]

  ]
 where
   sing = single @f @b
   a = sing "a"
   b = sing "b"
   as = star a
   ass = star as
   pink = sing "pink"
   pig = sing "pig"
   pp = pink <+> pig
   pps   = star pp
   anbn  = one <+> (a <.> anbn <.> b)
   groupNot :: [String] -> TestTree -> TestTree
   groupNot gs | group `elem` gs = const (testGroup "" [])
               | otherwise       = id
   gold :: Show z => String -> z -> TestTree
   gold nm = -- TODO: make directory if missing 
             goldenVsString nm
                ("test/gold/" <> nm <> ".txt")
             . pure . pack . show

-- I'd like to use definitions from Examples. How to establish the types?

-- -- Orphan
-- instance Indexable ((:->:) Char) b where
--   type Key ((:->:) Char) = Char
--   (!) = untrie

-- instance HasSingle ((:->:) Char) b where

-- TODO: generalize to other Integral or Enum types and add to Semi
newtype CharMap b = CharMap (IntMap b) deriving Functor

instance Additive b => Indexable CharMap b where
  type Key CharMap = Char
  CharMap m ! a = IntMap.findWithDefault zero (fromEnum a) m

instance Additive b => HasSingle CharMap b where a +-> b = CharMap (IntMap.singleton (fromEnum a) b)

instance Additive b => Additive (CharMap b) where
  zero = CharMap IntMap.empty
  CharMap u <+> CharMap v = CharMap (IntMap.unionWith (<+>) u v)

instance Additive b => DetectableZero (CharMap b) where isZero (CharMap m) = IntMap.null m
