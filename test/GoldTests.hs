{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall -Wno-unused-binds #-}

module Main where

import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import Code

main :: IO ()
main = do
  defaultMain basicTests

gold :: Show a => String -> a -> TestTree
gold nm = goldenVsString "basic"
             ("test/gold/" <> nm <> ".txt")
          . pure . pack . show

basicTests :: TestTree
basicTests = testGroup "various representations"
  [ testGroup "" []
  -- , testGroup "RegExp" [ tests @(RegExp Char) ]
  -- , testGroup "LTrie"  [ tests @(LTrie Char Bool) ]

  , gold "a" $ a
  , gold "b" $ b
  , gold "aOrb" $ aOrb
  , gold "ab" $ ab
  , gold "der-a-a" $ deriv 'a' a
  , gold "der-ab-a" $ deriv 'a' ab

  , gold "a-star-a"  $ accept ac "a"
  , gold "a-star-aa" $ accept ac "aa"

  , gold "a-star"    $ trim $ ac
  , gold "aOrb-star" $ trim $ closure aOrb
  , gold "ab-star"   $ trim $ closure ab

  , gold "a-star-aaa"      $ accept ac "aaa"
  , gold "a-star-aab"      $ accept ac "aab"
  , gold "aOrb-star-aabba" $ accept (closure aOrb) "aabba"
  , gold "aOrb-star-abab"  $ accept (closure aOrb) "abab"
  , gold "aOrb-star-abac"  $ accept (closure aOrb) "abac"
  , gold "ab-star-abab"    $ accept (closure ab) "abab"
  , gold "ab-star-aabb"    $ accept (closure ab) "aabb"

  ]
 where
  trim = trimLT @Char 7
  a = single @(LT Char) "a"
  b = single @(LT Char) "b"
  aOrb = a <+> b
  ab = a <.> b
  ac = closure a

tests :: forall z. Language z Char => TestTree
tests = testGroup "basic tests"
  [ testGroup "" []
#if 0
  , gold "a"                            $ a
  , gold "pig"                          $ pig
  , gold "pink-or-pig"                  $ pp
  , gold "derivs-pp-q"                  $ deriv 'q' pp
  , gold "derivs-pp-pi"                 $ derivs "pi" pp
  , gold "derivs-pp-pig"                $ derivs "pig" pp
#endif
  -- , gold "accept-pp-pi"                 $ app "pi"
  -- , gold "accept-pp-pig"                $ app "pig"
  -- , gold "accept-pp-pig"                $ app "pig"
  -- , gold "accept-pp-pink"               $ app "pink"
  -- , gold "accept-pp-ping"               $ app "ping"

  -- , gold "accept-pps-q"               $ apps "q"

  -- , gold "accept-pps-pig"               $ apps "pig"
  -- , gold "accept-pps-pigpig"            $ apps "pigpig"
  -- , gold "accept-pps-pigping"           $ apps "pigping"
  -- , gold "accept-pps-pinkpigpinkpigpig" $ apps "pinkpigpinkpigpig"
#if 1
  -- OptimizeRegexp in Code.hs causes these recursive examples to diverge.
  , gold "accept-anbn-eps"              $ ranbn ""
  , gold "accept-anbn-ab"               $ ranbn "ab"
  , gold "accept-anbn-ba"               $ ranbn "ba"
  , gold "accept-anbn-aabb"             $ ranbn "aabb"
  , gold "accept-anbn-aacbb"            $ ranbn "aacbb"
  , gold "accept-anbn-aaabbb"           $ ranbn "aaabbb"
  , gold "accept-anbn-aaabbbb"          $ ranbn "aaabbbb"
  -- , gold "pink-and-pig"              $ pink `intersectB` pig
#endif
  ]
 where
   sing = single @z
   a = sing "a"
   b = sing "b"
   pink = sing "pink"
   pig = sing "pig"
   pp = pink <+> pig
   pps   = closure pp
   app   = accept pp
   apps  = accept pps
   anbn  = one <+> (a <.> anbn <.> b)
   ranbn = accept anbn
