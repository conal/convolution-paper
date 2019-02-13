{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | A semiring wrapper for Map. Probably subsumed by Convo, but this one is
-- simpler for the paper.

module Map where

import Prelude hiding (sum)

import Data.Map (Map)
import qualified Data.Map as M

import Semi

-- #include "GenInstances.inc"

infixl 0 *<-
newtype b *<- a = M (a ->* b) deriving (Show, Additive, HasSingle a b, LeftSemimodule b)

-- Homomorphic denotation
mapFun' :: (Ord a, Additive b) => b *<- a -> (b <-- a)
mapFun' (M m) = C (m !)

instance (Ord a, Monoid a, Semiring b) => Semiring (b *<- a) where
  one = M (mempty +-> one)
  -- M m <.> M m' =
  --   sum [k <> k' +-> v <.> v' | (k,v) <- M.toList m, (k',v') <- M.toList m']
  M p <.> M q = sum [u <> v +-> (p!u) <.> (q!v) | u <- M.keys p, v <- M.keys q]


-- >>> x1 = single "a" <+> single "b"  :: Map' String Int
-- >>> x1 <+> x1
-- M (fromList [("a",2),("b",2)])
-- >>> x1 <.> x1
-- M (fromList [("aa",1),("ab",1),("ba",1),("bb",1)])
