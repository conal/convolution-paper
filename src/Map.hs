{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | A semiring wrapper for Map. Probably subsumed by Convo, but this one is
-- simpler for the paper.

module Map where

import Prelude hiding (sum)

import Data.Map (Map)
import qualified Data.Map as M

import Semi

infixl 0 *<-
newtype b *<- a = M (a ->* b) deriving (Show, Additive, HasSingle a b, LeftSemimodule b, DetectableZero, Indexable a b)

-- Homomorphic denotation
mapFun' :: (Ord a, Additive b) => (b *<- a) -> (b <-- a)
mapFun' (M m) = C (m !)

instance (Ord a, Monoid a, Semiring b) => Semiring (b *<- a) where
  one = M (mempty +-> one)
  M p <.> M q = sum [u <> v +-> p!u <.> q!v | u <- M.keys p, v <- M.keys q]



-- >>> x1 = single "a" <+> single "b"  :: Int *<- String
-- >>> x1 <+> x1
-- M (fromList [("a",2),("b",2)])
-- >>> x1 <.> x1
-- M (fromList [("aa",1),("ab",1),("ba",1),("bb",1)])

-- >>> x1 = single "a" <+> single "b"  :: Int *<- String
-- >>> x2 = single "b" <+> single "c"  :: Int *<- String
-- >>> x1 <+> x2
-- M (fromList [("a",1),("b",2),("c",1)])
-- >>> x1 <.> x2
-- M (fromList [("ab",1),("ac",1),("bb",1),("bc",1)])
-- >>> (x1 <+> x2) <.> (x1 <+> x2)
-- M (fromList [("aa",1),("ab",2),("ac",1),("ba",2),("bb",4),("bc",2),("ca",1),("cb",2),("cc",1)])

-- >>> x1 = one <+> single "a" <+> single "b"  :: Int *<- String
-- >>> x2 = one <+> single "b" <+> single "c"  :: Int *<- String
-- >>> x1 <+> x2
-- M (fromList [("",2),("a",1),("b",2),("c",1)])
-- >>> x1 <.> x2
-- M (fromList [("",1),("a",1),("ab",1),("ac",1),("b",2),("bb",1),("bc",1),("c",1)])
-- >>> (x1 <+> x2) <.> (x1 <+> x2)
-- M (fromList [("",4),("a",4),("aa",1),("ab",2),("ac",1),("b",8),("ba",2),("bb",4),("bc",2),("c",4),("ca",1),("cb",2),("cc",1)])

