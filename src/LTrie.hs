-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | List tries

module LTrie where

import Prelude hiding (sum,product)

import Data.Map (Map,singleton)

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

-- trieFun :: (Ord c, Additive b) => LTrie c b -> ([c] -> b)
-- trieFun (a :< dp) = a <: trieFun . (dp !)

instance (Ord c, Additive b) => Indexable (LTrie c b) [c] b where
  -- (!) = trieFun
  (!) (a :< dp) = a <: (!) . (dp !)
  -- (a :< _ ) ! [] = a
  -- (_ :< dp) ! (c:cs) = (dp ! c) ! cs

instance (Ord c, Additive b) => Additive (LTrie c b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

FunctorSemimodule(LTrie c)

instance (Ord c, Semiring s) => HasSingle [c] (LTrie c s) where
  single = foldr cons nil
   where
     nil = one :< zero  -- Semiring s needed here
     cons c x = zero :< singleton c x  -- (c +-> x)

-- Is HasSingle even useful on LTrie?

-- No Semiring instance, because one would have to map all possible keys to one.
-- We inherit this limitation from finite maps.

-- | Trim to a finite depth, for examination.
trimT :: (Ord c, Additive b) => Int -> LTrie c b -> LTrie c b
trimT 0 _ = zero
trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts

instance Decomposable b (Map c) (LTrie c b) where
  (<:) = (:<)
  decomp (b :< dp) = (b, dp)

type LTrie' b c = Convo (LTrie c b)

deriving instance (Ord c, Semiring b) => HasSingle [c] (LTrie' b c)
