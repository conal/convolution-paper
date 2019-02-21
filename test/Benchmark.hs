{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Benchmarks

module Main where

import Control.DeepSeq (NFData)
import qualified Data.Map.Lazy   as LM
import qualified Data.Map.Strict as SM
import Criterion.Main

import Misc (cats)
import Semi
import RegExp
import LTrie

import Examples

config :: Config
config = defaultConfig {
               reportFile = "crunch.html"  -- for example
           }

main :: IO ()
main = defaultMainWith 
  [ bgroup "" []

  , matchers @((->) String       )      @Bool "Function"

  , bgroup "RegExp"
    [ matchers @(RegExp ((->) Char)   ) @Bool "Function"
    -- , matchers @(RegExp (LM.Map  Char)) @Bool "LazyMap"
    -- , matchers @(RegExp (SM.Map  Char)) @Bool "StrictMap"
    ]

  , bgroup "Trie"
    [ matchers @(LTrie  ((->) Char)   ) @Bool "Function"
    , matchers @(LTrie  (LM.Map  Char)) @Bool "LazyMap"
    , matchers @(LTrie  (SM.Map  Char)) @Bool "StrictMap"
    ]
  ]

matchers :: forall f b. (HasSingle f b, Key f ~ String, StarSemiring (f b), StarSemiring b, NFData b)
         => String -> Benchmark
matchers group =
  bgroup group
    [ bgroup "letters"
       [ bgroup "" []
       -- , bench "asdf-50"  $ star letter # cats 50  "asdf"
       , bgroup "dyck"
         [ bench "a" $ dyck # "[]"
         , bench "b" $ dyck # "[[]]"
         , bench "c" $ dyck # "[[a]]"
         , bench "d" $ dyck # "[[]][]"
         ]
       ]
    ]
 where
   infixl 2 #
   (#) :: f b -> String -> Benchmarkable
   x # s = nf (x !) s
