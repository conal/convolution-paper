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
  -- TODO: lists!

  , tests @(S.RegExp  Char) "SetRegExp"
  , tests @(F.RegExp  Char Bool) "FunRegExp"
  , tests @(S.Decomp  Char) "SetDecomp"
  , tests @(F.Decomp  Char Bool) "FunDecomp"
  , tests @(S.Trie    Char) "SetTrie"
  , tests @(F.Trie    Char Bool) "FunTrie"
  ]

-- TODO: some tests with s other than Bool.

tests :: forall z h s.
  ( StarSemiring z, HasSingle z String s, Decomposable z h s
  , Indexable (h z) Char z, Show z, Semiring s, Show s )
  => String -> TestTree
tests group = testGroup group
  [ testGroup "" []

  , gold "a"                            $ a
  , gold "pig"                          $ pig
  , gold "pink-or-pig"                  $ pp
  , gold "derivs-pp-q"                  $ derivs pp "q"
  , gold "derivs-pp-pi"                 $ derivs pp "pi"
  , gold "derivs-pp-pig"                $ derivs pp "pig"

  , gold "accept-as-eps"                $ accept as ""
  , gold "accept-as-a"                  $ accept as "a"
  , gold "accept-ass-eps"               $ accept ass ""
  , gold "accept-ass-a"                 $ accept ass "a"

  , gold "accept-pp-pi"                 $ app "pi"
  , gold "accept-pp-pig"                $ app "pig"
  , gold "accept-pp-pig"                $ app "pig"
  , gold "accept-pp-pink"               $ app "pink"
  , gold "accept-pp-ping"               $ app "ping"

  , gold "accept-pps-q"                 $ apps "q"
  , gold "accept-pps-pig"               $ apps "pig"
  , gold "accept-pps-pigpig"            $ apps "pigpig"
  , gold "accept-pps-pigping"           $ apps "pigping"
  , gold "accept-pps-pinkpigpinkpigpig" $ apps "pinkpigpinkpigpig"

  -- These recursive examples are challenging.
  -- OptimizeRegexp in Set.hs causes these recursive examples to diverge.
  , gold "accept-anbn-eps"              $ ranbn ""
  , gold "accept-anbn-ab"               $ ranbn "ab"
  , gold "accept-anbn-ba"               $ ranbn "ba"
  , gold "accept-anbn-aabb"             $ ranbn "aabb"
  , gold "accept-anbn-aacbb"            $ ranbn "aacbb"
  , gold "accept-anbn-aaabbb"           $ ranbn "aaabbb"
  , gold "accept-anbn-aaabbbb"          $ ranbn "aaabbbb"

  ]
 where
   sing = single @z
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
   gold :: Show a => String -> a -> TestTree
   gold nm = -- TODO: make directory if missing 
             goldenVsString nm
                ("test/gold/" <> group <> "/" <> nm <> ".txt")
             . pure . pack . show
