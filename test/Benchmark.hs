{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Benchmarks

module Main where

import Control.DeepSeq (NFData)
import Data.Map (Map)
import Criterion.Main
import Criterion.Types (Config(..),Verbosity(..))

import Misc (cats)
import Semi
import RegExp
import LTrie

import Examples

config :: Config
config = defaultConfig
  {
    reportFile = Just "crunch.html"  -- for example
  , timeLimit  = 1  -- 5
  -- , verbosity  = Quiet  -- Normal
  }

main :: IO ()
main = defaultMainWith config
  [ bgroup "" []

  , matchers @((->) String       )      @Bool "Function"

  , bgroup "RegExp"
    [ matchers @(RegExp ((->) Char)   ) @Bool "Function"
    -- , matchers @(RegExp (M.Map  Char)) @Bool "Map"
    ]

  , bgroup "Trie"
    [ bgroup "" []
    -- , matchers @(LTrie  ((->) Char)  ) @Bool "Function"
    , matchers @(LTrie  (Map Char)) @Bool "Map"
    , matchers @(LTrie  CharMap   ) @Bool "IntMap"
    ]
  ]

bg :: Benchmark
bg = bgroup "" []

matchers :: forall f b. (HasSingle f b, Key f ~ String, StarSemiring (f b), StarSemiring b, NFData b)
         => String -> Benchmark
matchers group =
  bgroup group
    [ bg

    , bgroup "letters"
       [ bg
       , bgroup "" []
       , bench "asdf-50"  $ star letter # cats 50  "asdf"
       ]

    , bgroup "dyck"
      [ bg
      , bench "1" $ dyck # "[]"
      , bench "2" $ dyck # "[[]]"
      , bench "3" $ dyck # "[[a]]"
      , bench "4" $ dyck # "[[]][]"
      ]

    , bgroup "anbn"
      [ bg
      , bench "anbn-eps"     $ anbn # ""
      , bench "anbn-ab"      $ anbn # "ab"
      , bench "anbn-ba"      $ anbn # "ba"
      , bench "anbn-aabb"    $ anbn # "aabb"
      , bench "anbn-aacbb"   $ anbn # "aacbb"
      , bench "anbn-aaabbb"  $ anbn # "aaabbb"
      , bench "anbn-aaabbbb" $ anbn # "aaabbbb"
      ]
    ]
 where
   infixl 2 #
   (#) :: f b -> String -> Benchmarkable
   x # s = nf (x !) s
