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
import Data.Semiring

import qualified Set as S
import qualified Fun as F

import Language

main :: IO ()
main = do
  defaultMain basicTests

basicTests :: TestTree
basicTests = testGroup "Various representations"
  [ testGroup "" []
  , tests @(S.Pred String      ) "Pred"
  , tests @(S.Decomp  Char     ) "SetDecomp"
  , tests @(S.RegExp  Char     ) "SetRegExp"
  , tests @(S.Trie    Char     ) "SetTrie"
  , tests @(Bool F.<-- String  ) "F"
  , tests @(F.Decomp  Char Bool) "FunDecomp"
  , tests @(F.RegExp  Char Bool) "FunRegExp"
  , tests @(F.Trie    Char Bool) "FunTrie"
  ]

-- I don't think these ones can work:
-- 
--   , tests @(S.L String)    "List"
--   , tests @(S.Pred String) "Pred"


-- TODO: some tests with s other than Bool.

tests :: forall x h s.
  ( StarSemiring x, HS x Char s, Decomposable x h s
  , Indexable (h x) Char x, Show x, Semiring s, Show s )
  => String -> TestTree
tests group = testGroup group
  [ testGroup "" []

  , gold "as-eps"                $ accept as ""
  , gold "as-a"                  $ accept as "a"
  , gold "ass-eps"               $ accept ass ""
  , groupNot ["Pred","F"] $
    gold "ass-a"                 $ accept ass "a"

  , gold "pp-pi"                 $ app "pi"
  , gold "pp-pig"                $ app "pig"
  , gold "pp-pig"                $ app "pig"
  , gold "pp-pink"               $ app "pink"
  , gold "pp-ping"               $ app "ping"

  , gold "pps-q"                 $ apps "q"
  , gold "pps-pig"               $ apps "pig"
  , gold "pps-pigpig"            $ apps "pigpig"
  , gold "pps-pigping"           $ apps "pigping"
  , gold "pps-pinkpigpinkpigpig" $ apps "pinkpigpinkpigpig"

  -- These recursive examples are challenging.
  -- OptimizeRegexp in Set.hs causes these recursive examples to diverge.
  , gold "anbn-eps"              $ ranbn ""
  , gold "anbn-ab"               $ ranbn "ab"
  , gold "anbn-ba"               $ ranbn "ba"
  , gold "anbn-aabb"             $ ranbn "aabb"
  , gold "anbn-aacbb"            $ ranbn "aacbb"
  , gold "anbn-aaabbb"           $ ranbn "aaabbb"
  , gold "anbn-aaabbbb"          $ ranbn "aaabbbb"

  ]
 where
   sing = single @x
   a = sing "a"
   b = sing "b"
   as = star a
   ass = star as
   pink = sing "pink"
   pig = sing "pig"
   pp = pink <+> pig
   pps   = star pp
   app   = accept pp
   apps  = accept pps
   anbn  = one <+> (a <.> anbn <.> b)
   ranbn = accept anbn
   groupNot gs | group `elem` gs = const (testGroup "" [])
               | otherwise       = id
   gold :: Show a => String -> a -> TestTree
   gold nm = -- TODO: make directory if missing 
             goldenVsString nm
                ("test/gold/" <> group <> "/" <> nm <> ".txt")
             . pure . pack . show
