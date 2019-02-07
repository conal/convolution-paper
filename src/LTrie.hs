
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | List tries

module LTrie where

import Data.Map (Map)

import Constrained
import Semi
import Language

#include "GenInstances.inc"

-- | List trie, denoting '[c] -> b'"
infix 1 :<
data LTrie c b = b :< Map c (LTrie c b) deriving Show

instance Functor (LTrie c) where
  fmap f = go where go (a :< dp) = f a :< fmap go dp

instance FunctorC (LTrie c)

trieFun :: (Ord c, Additive b) => LTrie c b -> ([c] -> b)
trieFun (a :< dp) = a <: trieFun . (dp !)

instance (Ord c, Additive b) => Additive (LTrie c b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

FunctorSemimodule(LTrie c)

-- No Semiring instance, because one would have to map all possible keys to one.
-- Finite maps have the same problem, which we inherit here.

-- | Trim to a finite depth, for examination.
trimT :: (Ord c, Additive b) => Int -> LTrie c b -> LTrie c b
trimT 0 _ = zero
trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts

instance Decomposable b (Map c) (LTrie c b) where
  (<:) = (:<)
  decomp (b :< dp) = (b, dp)

type Trie' b c = Convo (LTrie c b)
