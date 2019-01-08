{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-binds #-}

module Main where

import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import Semiring
import Set

main :: IO ()
main = do
  defaultMain basicTests

basicTests :: TestTree
basicTests = testGroup "Various representations"
  [ testGroup "" []
  , tests @(RegExp  Char) "RegExp"
  , tests @(Decomp  Char) "Decomp"
  , tests @(DecompM Char) "DecompM"
  ]

tests :: forall z s. (Language z Char s, Show z, Show s) => String -> TestTree
tests group = testGroup group
  [ testGroup "" []

  , gold "a"                            $ a
  , gold "pig"                          $ pig
  , gold "pink-or-pig"                  $ pp
  , gold "derivs-pp-q"                  $ deriv 'q' pp
  , gold "derivs-pp-pi"                 $ derivs "pi" pp
  , gold "derivs-pp-pig"                $ derivs "pig" pp

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
   pink = sing "pink"
   pig = sing "pig"
   pp = pink <+> pig
   pps   = closure pp
   app   = accept pp
   apps  = accept pps
   anbn  = one <+> (a <.> anbn <.> b)
   ranbn = accept anbn
   gold :: Show a => String -> a -> TestTree
   gold nm = goldenVsString "basic"
                ("test/gold/" <> group <> "/" <> nm <> ".txt")
             . pure . pack . show
