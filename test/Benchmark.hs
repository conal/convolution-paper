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

main :: IO ()
main = do 

  group "letters" (star letter)
    [ ("asdf", cats 5 "asdf") ]

  group "dyck" dyck
    [ ("1", "[]")
    , ("2", "[[]]")
    , ("3", "[[a]]")
    , ("4", "[[]][]")
    ]

  group "anbn" anbn
    [ ("eps"     , "")
    , ("ab"      , "ab")
    , ("ba"      , "ba")
    , ("aabb"    , "aabb")
    , ("aacbb"   , "aacbb")
    , ("aaabbb"  , "aaabbb")
    , ("aaabbbb" , "aaabbbb")
    ]


type Ok f b = (HasSingle f b, StarSemiring (f b), StarSemiring b, NFData b, Key f ~ String)

group :: String -> (forall f b. Ok f b => f b) -> [(String,String)] -> IO ()
group groupName example dats =
  do putStrLn ("Group " ++ show groupName)
     defaultMainWith config (dat <$> dats)
 where
   config = defaultConfig
     { reportFile = Just ("test/Benchmarks/" ++ groupName ++ ".html")
     , timeLimit  = 1 -- 5
     }
   dat :: (String,String) -> Benchmark
   dat (dname,str) =
     bgroup dname
       [ style @(LTrie  ((->) Char)) @Bool "Function"
       , style @(LTrie  (Map  Char)) @Bool "Map"
       , style @(LTrie  CharMap    ) @Bool "IntMap"
       ]
    where
      style :: forall f b. Ok f b => String -> Benchmark
      style s = bench s (nf (example @f @b !) str)
