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

import Data.Map (Map)

import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

-- import qualified Set as S
-- import qualified Fun as F

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
  , tests @(LTrie  ((->) Char)) @Bool "FunTrie"
  , tests @(RegExp (Map Char)) @Bool "MapRegExp"
  , tests @(LTrie  (Map Char)) @Bool "MapTrie"

  ]

-- Idea: use a single output directory instead of many, for comparison across
-- representations.

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
                ("test/gold/" <> group <> "/" <> nm <> ".txt")
             . pure . pack . show

-- I'd like to use definitions from Examples. How to establish the types?
