{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Benchmarks

module Main where

import Control.DeepSeq (NFData)
import Data.Map (Map)
-- import Data.MemoTrie ((:->:))
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

  group "star-a" (star (single "a")) [] [lit "a"]

  -- group "starR-a" (starR (single "a")) [] [("a50", replicate 50 'a')]

  -- group "starL-a" (starL (single "a")) [] [("a50", replicate 50 'a')]

  group "letters" (star letter) []
    [ ("asdf-50", cats 50 "asdf") ]

  group "dyck" dyck ["RegExp:Map","RegExp:IntMap"] $
    lit <$> [ "[]","[[]]","[[a]]","[[]][]" ]

  group "anbn" anbn ["RegExp:Map","RegExp:IntMap"] $
    []
    ++ map lit ["","ab","aacbb","aaabbb","aaabbbb"]
    ++ [("30",replicate 30 'a' ++ replicate 30 'b')]

lit :: String -> (String,String)
lit str = (str,show str)

outDir :: FilePath
outDir = "test/Benchmarks"

type Ok x b = (HasSingle String b x, StarSemiring x, StarSemiring b, NFData b)

group :: String -> (forall x b. Ok x b => x) -> [String] -> [(String,String)] -> IO ()
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

       , style @(RegExp ((->)   Char) Bool) "RegExp:Function"
       , style @(RegExp (Map    Char) Bool) "RegExp:Map"
       , style @(RegExp CharMap       Bool) "RegExp:IntMap"
       -- , style @(RegExp ((:->:) Char) Bool) "RegExp:Memo"

       , style @(LTrie  ((->)   Char) Bool) "LTrie:Function"
       , style @(LTrie  (Map    Char) Bool) "LTrie:Map"
       , style @(LTrie  CharMap       Bool) "LTrie:IntMap"
       -- , style @(LTrie  ((:->:) Char) Bool) "LTrie:Memo"

       ]
    where
      style :: forall x b. Ok x b => String -> Benchmark
      style s | s `elem` omit = bgroup "" []
              | otherwise     = bench s (nf (example @x @b !) str)

-- TODO: Generate the style name from the type via TypeRep.


-- For starL, nothing terminates.
