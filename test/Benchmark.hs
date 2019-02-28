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
import Cofree

import Examples

main :: IO ()
main = do
  putChar '\n'
  createDirectoryIfMissing True outDir

  group "star-a" (star (single "a")) []
    [ ("a100", replicate 100 'a') ]

  -- -- group "starR-a" (starR (single "a")) [] [("a50", replicate 50 'a')]
  -- -- group "starL-a" (starL (single "a")) [] [("a50", replicate 50 'a')]

  -- group "letters" (star letter) []
  --   [ ("asdf-50", cats 50 "asdf") ]

  -- group "fish" (star letter <.> single "fish" <.> star letter) [] $
  --   []
  --   ++ [("100", take 100 (cycle az) ++ "fish" ++ take 100 (cycle az))]

  -- group "asas" (star (single "a") <.> star (single "a")) [] $
  --   []
  --   -- ++ lit <$> [ "aabbb", "aabbba", "aaaa" , "bb" ]
  --   ++ [("a100b100",replicate 100 'a' ++ replicate 100 'a')]
  --   ++ [("a100cb100",replicate 100 'a' ++ "c" ++ replicate 100 'a')]

  -- group "asbs" (star (single "a") <.> star (single "b")) [] $
  --   []
  --   -- ++ lit <$> [ "aabbb", "aabbba", "aaaa" , "bb" ]
  --   ++ [("a100b100",replicate 100 'a' ++ replicate 100 'b')]
  --   ++ [("a100cb100",replicate 100 'a' ++ "c" ++ replicate 100 'b')]

  -- group "asbas" (star (single "a") <.> single "b" <.> star (single "a")) [] $
  --   []
  --   -- ++ lit <$> [ "aabaaa", "aabba", "aaaa" , "bb" ]
  --   ++ [("a30ba30",replicate 30 'a' ++ "b" ++ replicate 30 'a')]

  -- -- With O = N, the dyck examples don't work for RegExp:Function, while anbn
  -- -- is okay.
  -- group "dyck" dyck ["RegExp:Function","RegExp:Map","RegExp:IntMap"] $
  --   lit <$> [ "[]","[[]]","[[a]]","[[]][]" ]

  -- group "anbn" anbn ["RegExp:Map","RegExp:IntMap"] $
  --   []
  --   ++ map lit ["","ab","aacbb","aaabbb","aaabbbb"]
  --   ++ [("30",replicate 30 'a' ++ replicate 30 'b')]

lit :: String -> (String,String)
lit str = (show str,str)

outDir :: FilePath
outDir = "test/Benchmarks"

type Ok x b = (HasSingle String b x, StarSemiring x, StarSemiring b, NFData b)

group :: String -> (forall x b. Ok x b => x) -> [String] -> [(String,String)] -> IO ()
group groupName example omit dats =
  do putStrLn ("# Group " ++ show groupName ++ "\n\n```\n")
     defaultMainWith config (dat <$> dats)
     putStrLn "```\n"
 where
   config = defaultConfig
     { reportFile = Just (outDir ++ "/" ++ groupName ++ ".html")
     , timeLimit  = 5 -- 1
     -- , timeLimit = 0, resamples = 1
     }
   dat :: (String,String) -> Benchmark
   dat (dname,str) =
     bgroup dname
       [ bgroup "" []

       , style @(RegExp ((->)   Char) O) "RegExp:Function"
       , style @(RegExp (Map    Char) O) "RegExp:Map"
       -- , style @(RegExp CharMap       O) "RegExp:IntMap"

       , style @(Cofree  ((->)   Char) O) "Cofree:Function"
       , style @(Cofree  (Map    Char) O) "Cofree:Map"
       -- , style @(Cofree  CharMap       O) "Cofree:IntMap"

       ]
    where
      style :: forall x b. Ok x b => String -> Benchmark
      style s | s `elem` omit = bgroup "" []
              | otherwise     = bench s (nf (example @x @b !) str)

type O = Bool -- N

-- TODO: Generate the style name from the type via TypeRep.

az :: String
az = ['a'..'z']
