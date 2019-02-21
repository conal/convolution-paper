{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Benchmarks

module Main where

import Control.DeepSeq (NFData)
import Data.Map (Map)
import System.Directory (createDirectoryIfMissing)
import Criterion.Main
import Criterion.Types (Config(..),Verbosity(..))

import Misc (cats)
import Semi
import RegExp
import LTrie

import Examples

main :: IO ()
main = do
  putChar '\n'
  createDirectoryIfMissing True outDir

  group "letters" (star letter) []
    [ ("asdf-50", cats 50 "asdf") ]

  group "dyck" dyck ["RegExp Map","RegExp IntMap"] $
    dups [ "[]","[[]]","[[a]]","[[]][]" ]

  group "anbn" anbn ["RegExp Map","RegExp IntMap"] $
    [ ("eps"     , "") ]
    ++ dups ["ab","ba","aabb","aacbb","aaabbb","aaabbbb"]

 where
   dups = map (\ a -> (a,a))

outDir :: FilePath
outDir = "test/Benchmarks"

type Ok f b = (HasSingle f b, StarSemiring (f b), StarSemiring b, NFData b, Key f ~ String)

group :: String -> (forall f b. Ok f b => f b) -> [String] -> [(String,String)] -> IO ()
group groupName example omit dats =
  do putStrLn ("# Group " ++ show groupName ++ "\n")
     defaultMainWith config (dat <$> dats)
 where
   config = defaultConfig
     { reportFile = Just (outDir ++ "/" ++ groupName ++ ".html")
     , timeLimit  = 1 -- 5
     }
   dat :: (String,String) -> Benchmark
   dat (dname,str) =
     bgroup dname
       [ bgroup "" []

       , style @(LTrie  ((->) Char)) @Bool "LTrie/Function"
       , style @(LTrie  (Map  Char)) @Bool "LTrie/Map"
       , style @(LTrie  CharMap    ) @Bool "LTrie/IntMap"

       -- , style @(RegExp ((->) Char)) @Bool "RegExp/Function"
       -- , style @(RegExp (Map  Char)) @Bool "RegExp/Map"
       -- , style @(RegExp CharMap    ) @Bool "RegExp/IntMap"

       ]
    where
      style :: forall f b. Ok f b => String -> Benchmark
      style s | s `elem` omit = bgroup "" []
              | otherwise     = bench s (nf (example @f @b !) str)

-- TODO: Generate the style name from the type via TypeRep.

