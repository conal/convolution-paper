{-# OPTIONS_GHC -Wno-unused-binds -Wno-unused-imports #-}  -- TEMP

module Main where

import Prelude hiding (sum,product,(^))

import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap

-- TODO: try strict variants also

import Data.ByteString.Lazy.Char8 (pack)
import Data.Semigroup ((<>))
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

-- import Data.MemoTrie

import Misc   (cats)
import Semi
import RegExp (RegExp)
import LTrie  (LTrie)

import qualified Examples as X

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
  (HasSingle f b, Key f ~ String, StarSemiring (f b), Semiring b, Show b)
  => String -> TestTree
tests group = testGroup group
  [ testGroup "" []

  , gold "as-eps"                $ as ! ""
  , gold "as-a"                  $ as ! "a"
  , gold "ass-eps"               $ ass ! ""
  , groupNot ["Function"] $
    gold "ass-a"               $ ass ! "a"

  , gold "pp-pi"                 $ pp ! "pi"
  , gold "pp-pig"                $ pp ! "pig"
  , gold "pp-pig"                $ pp ! "pig"
  , gold "pp-pink"               $ pp ! "pink"
  , gold "pp-ping"               $ pp ! "ping"

  , gold "pps-q"                 $ pps ! "q"
  , gold "pps-pig"               $ pps ! "pig"
  , gold "pps-pigpig"            $ pps ! "pigpig"
  , gold "pps-pigping"           $ pps ! "pigping"
  , gold "pps-pinkpigpinkpigpig" $ pps ! "pinkpigpinkpigpig"

  , gold "letters as0df"         $ letters ! "as0df"
  , gold "letters asdf"          $ letters ! "asdf"
  , gold "letters asdf 40"       $ letters ! cats 40 "asdf"

  , groupNot ["RegExpMap","RegExpIntMap"] $
    testGroup "anbn"
    [ gold "anbn-eps"              $ anbn ! ""
    , gold "anbn-ab"               $ anbn ! "ab"
    , gold "anbn-ba"               $ anbn ! "ba"
    , gold "anbn-aabb"             $ anbn ! "aabb"
    , gold "anbn-aacbb"            $ anbn ! "aacbb"
    , gold "anbn-aaabbb"           $ anbn ! "aaabbb"
    , gold "anbn-aaabbbb"          $ anbn ! "aaabbbb"
    ]

  ]
 where
   sing = single @f @b
   a = sing "a"
   b = sing "b"
   as = star a
   ass = star as
   pink = sing "pink"
   pig = sing "pig"
   pp = pink <+> pig
   pps   = star pp
   anbn  = one <+> (a <.> anbn <.> b)
   letters = star (X.letter @f @b)
   groupNot :: [String] -> TestTree -> TestTree
   groupNot gs | group `elem` gs = const (testGroup "" [])
               | otherwise       = id
   gold :: Show z => String -> z -> TestTree
   gold nm = -- TODO: make directory if missing 
             goldenVsString nm
                ("test/gold/" <> nm <> ".txt")
             . pure . pack . show

-- TODO: Get more of the examples from X

-- TODO: generalize to other Integral or Enum types and add to Semi
newtype CharMap b = CharMap (IntMap b) deriving Functor

instance Additive b => Indexable CharMap b where
  type Key CharMap = Char
  CharMap m ! a = IntMap.findWithDefault zero (fromEnum a) m

instance Additive b => HasSingle CharMap b where a +-> b = CharMap (IntMap.singleton (fromEnum a) b)

instance Additive b => Additive (CharMap b) where
  zero = CharMap IntMap.empty
  CharMap u <+> CharMap v = CharMap (IntMap.unionWith (<+>) u v)

instance Additive b => DetectableZero (CharMap b) where isZero (CharMap m) = IntMap.null m
