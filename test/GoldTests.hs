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

import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

-- import qualified Set as S
-- import qualified Fun as F

import Semi
import Language
import Decomp
import RegExp
import LTrie

main :: IO ()
main = do
  defaultMain basicTests

basicTests :: TestTree
basicTests = testGroup "Various representations"
  [ testGroup "" []
  -- , tests @(S.Pred String      ) "Pred"
  -- , tests @(S.Decomp  Char     ) "SetDecomp"
  -- , tests @(S.RegExp  Char     ) "SetRegExp"
  -- , tests @(S.Trie    Char     ) "SetTrie"
  -- , tests @(Bool F.<-- String  ) "F"
  -- , tests @(Convo (Decomp  Char Bool)) "FunDecomp"
  -- , tests @(Convo (RegExp  Char Bool)) "FunRegExp"
  , tests @(Convo (LTrie    Char Bool)) "FunTrie"
  ]

-- TODO: some tests with s other than Bool.

-- tests' :: forall x. Semiring x => String -> TestTree
-- tests' = undefined

tests :: forall x b.
  ( HasSingle String b x, Indexable String b x
  , StarSemiring x, Show x, Semiring b, Show b )
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
  -- OptimizeRegexp in Set.hs causes these recursive examples to diverge.
  , gold "anbn-eps"              $ anbn ! ""
  , gold "anbn-ab"               $ anbn ! "ab"
  , gold "anbn-ba"               $ anbn ! "ba"
  , gold "anbn-aabb"             $ anbn ! "aabb"
  , gold "anbn-aacbb"            $ anbn ! "aacbb"
  , gold "anbn-aaabbb"           $ anbn ! "aaabbb"
  , gold "anbn-aaabbbb"          $ anbn ! "aaabbbb"

  ]
 where
   sing :: String -> x
   sing = single
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
