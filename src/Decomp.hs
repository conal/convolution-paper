
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Decomposable as a "language" representation

module Decomp where

import Text.Show.Functions ()  -- for Decomp

import Constrained
import Semi
import Language

#include "GenInstances.inc"

infix 1 :<
data Decomp c s = s :< (c -> Decomp c s) deriving Show

instance Functor (Decomp c) where
  fmap f = go where go (a :< dp) = f a :< go . dp

-- TODO: define fmapD for arbitrary decomposables

instance FunctorC (Decomp c)

-- trieFun :: (Ord c, Additive b) => Decomp c b -> ([c] -> b)
-- trieFun (a :< dp) = a <: trieFun . (dp !)

instance (Ord c, Additive b) => Indexable (Decomp c b) [c] b where
  (!) (a :< dp) = a <: (!) . (dp !)

  -- (a :< _ ) ! [] = a
  -- (_ :< dp) ! (c:cs) = (dp ! c) ! cs

  -- (a :< _ ) ! [] = a
  -- (_ :< dp) ! (c:cs) = dp c ! cs

-- TODO: define (!) for arbitrary decomposables.

instance (Ord c, Additive b) => Additive (Decomp c b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

FunctorSemimodule(Decomp c)

instance (Ord c, Additive s) => HasSingle [c] s (Decomp c s) where
  w +-> s = foldr cons nil w
   where
     nil = s :< zero
     cons c x = zero :< (c +-> x)

-- Is HasSingle even useful on Decomp?
