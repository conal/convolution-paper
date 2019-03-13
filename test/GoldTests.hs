{-# OPTIONS_GHC -Wno-unused-binds -Wno-unused-imports #-}  -- TEMP

module Main where

import Prelude hiding (sum,product,(^))

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map

import Data.IntMap.Lazy (IntMap)

import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

-- import Data.MemoTrie

import Misc   (cats)
import Semi
import RegExp (RegExp)
import Cofree  (Cofree)
import ShareMap (ShareMap)

import Examples

main :: IO ()
main = do
  defaultMain basicTests

basicTests :: TestTree
basicTests = testGroup "Various representations"
  [ testGroup "" []

  -- , tests @(String  ->              N) "Function"

  -- , tests @(RegExp ((->) Char)      N) "RegExpFun"
  -- , tests @(RegExp (Map  Char)      N) "RegExpMap"
  -- , tests @(RegExp CharMap          N) "RegExpIntMap"
  -- , tests @(RegExp (ShareMap Char)  N) "RegExpShareMap"

  -- , tests @(Cofree  ((->) Char)     N) "CofreeFun"
  , tests @(Cofree  (Map  Char)     N) "CofreeMap"
  -- , tests @(Cofree  CharMap         N) "CofreeIntMap"
  , tests @(Cofree  (ShareMap Char) N) "CofreeShareMap"

  ]

-- TODO: some tests with s other than Bool.

-- tests' :: forall x. Semiring x => String -> TestTree
-- tests' = undefined

tests :: forall x b.
  (HasSingle String b x, StarSemiring x, StarSemiring b, Show b)
  => String -> TestTree
tests group = testGroup group
  [ testGroup "" []

  , gold "as-eps"                         $ as  # ""
  , gold "as-a"                           $ as  # "a"

  , gold "pp-pi"                          $ pp # "pi"
  , gold "pp-pig"                         $ pp # "pig"
  , gold "pp-pig"                         $ pp # "pig"
  , gold "pp-pink"                        $ pp # "pink"
  , gold "pp-ping"                        $ pp # "ping"

  , gold "pps-q"                          $ pps # "q"
  , gold "pps-pig"                        $ pps # "pig"
  , gold "pps-pigpig"                     $ pps # "pigpig"
  , gold "pps-pigping"                    $ pps # "pigping"
  , gold "pps-pinkpigpinkpigpig"          $ pps # "pinkpigpinkpigpig"

  , gold "letters as0df"                  $ star letter # "as0df"
  , gold "letters asdf"                   $ star letter # "asdf"
  , gold "letters asdf 40"                $ star letter # cats 40 "asdf"

  , groupNot ["RegExpMap","RegExpIntMap"] $
    testGroup "anbn"
    [ gold "anbn-eps"                     $ anbn # ""
    , gold "anbn-ab"                      $ anbn # "ab"
    , gold "anbn-ba"                      $ anbn # "ba"
    , gold "anbn-aabb"                    $ anbn # "aabb"
    , gold "anbn-aacbb"                   $ anbn # "aacbb"
    , gold "anbn-aaabbb"                  $ anbn # "aaabbb"
    , gold "anbn-aaabbbb"                 $ anbn # "aaabbbb"
    ]

  , gold "asbs-aabbbb"  $ asbs # "aabbbb"
  , gold "asbs-aabbba"  $ asbs # "aabbba"

  , gold "asbas-aabaaa" $ asbas # "aabaaa"
  , gold "asbas-aabba"  $ asbas # "aabba"

  , gold "asas-100" $ asas # replicate 100 'a'

  , groupNot ["RegExpFun","RegExpMap","RegExpIntMap"] $
    testGroup "dyck"
    [ gold "dyck-a"                       $ dyck # "[]"
    , gold "dyck-b"                       $ dyck # "[[]]"
    , gold "dyck-c"                       $ dyck # "[[a]]"
    , gold "dyck-d"                       $ dyck # "[[]][]"
    , gold "dyck-e"                       $ dyck # "[[]][[]"
    ]

  ]
 where
   infixl 2 #
   (#) :: x -> String -> b
   (#) = (!)
   groupNot :: [String] -> TestTree -> TestTree
   groupNot gs | group `elem` gs = const (testGroup "" [])
               | otherwise       = id
   gold :: Show z => String -> z -> TestTree
   gold nm = goldenVsString nm ("test/gold/" <> nm <> ".txt")
             . pure . pack . show
