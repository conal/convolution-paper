{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Benchmarks

module Main where

import Control.DeepSeq (NFData)
import Data.Map (Map)
import Data.MemoTrie ((:->:))
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

  -- group "star-a" (star (single "a")) [] [dup "a"]

  -- group "starR-a" (starR (single "a")) [] [("a50", replicate 50 'a')]

  -- group "starL-a" (starL (single "a")) [] [("a50", replicate 50 'a')]

  -- group "letters" (star letter) []
  --   [ ("asdf-50", cats 50 "asdf") ]

  -- group "dyck" dyck ["RegExp:Map","RegExp:IntMap"] $
  --   dup <$> [ "[]","[[]]","[[a]]","[[]][]" ]

  group "anbn" anbn ["RegExp:Map","RegExp:IntMap"] $
    []
    -- ++ map dup ["","ab","aacbb","aaabbb","aaabbbb"]
    ++ [("30",replicate 30 'a' ++ replicate 30 'b')]

dup :: a -> (a,a)
dup a = (a,a)

outDir :: FilePath
outDir = "test/Benchmarks"

type Ok f b = (HasSingle b f, StarSemiring (f b), StarSemiring b, NFData b, Key f ~ String)

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

       , style @(RegExp ((->)   Char)) @Bool "RegExp:Function"
       , style @(RegExp (Map    Char)) @Bool "RegExp:Map"
       , style @(RegExp CharMap      ) @Bool "RegExp:IntMap"
       -- , style @(RegExp ((:->:) Char)) @Bool "RegExp:Memo"

       , style @(LTrie  ((->)   Char)) @Bool "LTrie:Function"
       -- , style @(LTrie  (Map    Char)) @Bool "LTrie:Map"
       , style @(LTrie  CharMap      ) @Bool "LTrie:IntMap"
       -- , style @(LTrie  ((:->:) Char)) @Bool "LTrie:Memo"

       ]
    where
      style :: forall f b. Ok f b => String -> Benchmark
      style s | s `elem` omit = bgroup "" []
              | otherwise     = bench s (nf (example @f @b !) str)

-- TODO: Generate the style name from the type via TypeRep.


-- For starL, nothing terminates.
