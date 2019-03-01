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

  defaultMainWith config [
      bgroup "" []

    , group "star-a" (star (single "a")) [] $
        replicate 100 'a'

    , group "letters" (star letter) [] $
        cats 50 "asdf" 

    , group "fish" (star letter <.> single "fish" <.> star letter) [] $
        take 30 (cycle az) ++ "fish" ++ take 30 (cycle az)

    , group "asas" (star (single "a") <.> star (single "a")) [] $
        replicate 30 'a' ++ replicate 30 'a'

    , group "asbs" (star (single "a") <.> star (single "b")) [] $
        replicate 30 'a' ++ replicate 30 'b'

    , group "asbas" (star (single "a") <.> single "b" <.> star (single "a")) [] $
        replicate 30 'a' ++ "b" ++ replicate 30 'a'

      -- With O = N, the dyck examples don't work for RegExp:Function, while anbn
      -- is okay.
    , group "dyck" dyck ["RegExp:Map","RegExp:IntMap"] $
        "[[[[[[[]]][[[[]]]][[[]]][]][[[[]]]]]][]]"

    , group "anbn" anbn ["RegExp:Map","RegExp:IntMap"] $
        replicate 30 'a' ++ replicate 30 'b'

    ]
 where
   config = defaultConfig
     { 
      timeLimit = 5 -- 0.1
     }

type Ok x b = (HasSingle String b x, StarSemiring x, StarSemiring b, NFData b)

group :: String -> (forall x b. Ok x b => x) -> [String] -> String -> Benchmark
group groupName example omit str =
  bgroup groupName
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
   style s | s `elem` omit = bench s (whnf id ())
                             -- bgroup "" []
           | otherwise     = bench s (nf (example @x @b !) str)


type O = Bool -- N

-- TODO: Generate the style name from the type via TypeRep.

az :: String
az = ['a'..'z']
