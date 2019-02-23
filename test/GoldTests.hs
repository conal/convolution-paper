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
import LTrie  (LTrie)

import Examples

main :: IO ()
main = do
  defaultMain basicTests

basicTests :: TestTree
basicTests = testGroup "Various representations"
  [ testGroup "" []

  , tests @((->) String)        @Bool "Function"

  , tests @(RegExp ((->) Char)) @Bool "RegExpFun"
  , tests @(RegExp (Map  Char)) @Bool "RegExpMap"
  , tests @(RegExp CharMap    ) @Bool "RegExpIntMap"

  , tests @(LTrie  ((->) Char)) @Bool "TrieFun"
  , tests @(LTrie  (Map  Char)) @Bool "TrieMap"
  , tests @(LTrie  CharMap    ) @Bool "TrieIntMap"

  ]

-- TODO: some tests with s other than Bool.

-- tests' :: forall x. Semiring x => String -> TestTree
-- tests' = undefined

tests :: forall f b.
  (HasSingle b f, Key f ~ String, StarSemiring (f b), StarSemiring b, Show b)
  => String -> TestTree
tests group = testGroup group
  [ testGroup "" []

  , gold "as-eps"                         $ as  # ""
  , gold "as-a"                           $ as  # "a"
  , gold "ass-eps"                        $ ass # ""
  , groupNot ["Function"]                 $
    gold "ass-a"                          $ ass # "a"

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

  , groupNot ["RegExpMap","RegExpIntMap"] $
    testGroup "dyck"
    [ gold "dyck-a"                       $ dyck # "[]"
    , gold "dyck-b"                       $ dyck # "[[]]"
    , gold "dyck-c"                       $ dyck # "[[a]]"
    , gold "dyck-d"                       $ dyck # "[[]][]"
    ]

  ]
 where
   infixl 2 #
   (#) :: f b -> String -> b
   x # s = x ! s
   groupNot :: [String] -> TestTree -> TestTree
   groupNot gs | group `elem` gs = const (testGroup "" [])
               | otherwise       = id
   gold :: Show z => String -> z -> TestTree
   gold nm = goldenVsString nm ("test/gold/" <> nm <> ".txt")
             . pure . pack . show
