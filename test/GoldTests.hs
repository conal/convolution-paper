'{-# LANGUAGE CPP #-}'
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
basicTests = testGroup "basic tests"
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
  , gold "accept-pps-pig"               $ apps "pig"
  , gold "accept-pps-pigpig"            $ apps "pigpig"
  , gold "accept-pps-pigping"           $ apps "pigping"
  , gold "accept-pps-pinkpigpinkpigpig" $ apps "pinkpigpinkpigpig"
#if 1
  -- OptimizeRegexp in Code.hs causes these recursive examples to wedge.
  , gold "accept-anbn-eps"              $ ranbn ""
  , gold "accept-anbn-ab"               $ ranbn "ab"
  , gold "accept-anbn-ba"               $ ranbn "ba"
  , gold "accept-anbn-aabb"             $ ranbn "aabb"
  , gold "accept-anbn-aacbb"            $ ranbn "aacbb"
  , gold "accept-anbn-aaabbb"           $ ranbn "aaabbb"
  , gold "accept-anbn-aaabbbb"          $ ranbn "aaabbbb"
#endif
  -- , gold "pink-and-pig"              $ pink `intersectB` pig
  ]
 where
   pp = pinkOrPig
   app   = acceptD pp
   pps   = closure pp
   apps  = acceptD pps
   anbn  = one <+> (single "a" <.> anbn <.> single "b") :: Match
   ranbn = acceptD anbn

type Match = RegExp Char

a :: Match
a = single "a"

pink :: Match
pink = single "pink"

pig :: Match
pig = single "pig"

pinkOrPig :: Match
pinkOrPig = pink <+> pig
