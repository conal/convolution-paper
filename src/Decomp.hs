
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

instance (Ord c, Semiring s) => HasSingle [c] (Decomp c s) where
#if 0
  -- Oops. We don't have Semiring (Decomp c s) for product.
  single w = product (map symbol w) where symbol c = zero <: singleton c one
  -- single = product . map symbol
  --  where
  --    symbol c = zero :< singleton c one
#else
  -- More streamlined
  single = foldr cons nil
   where
     nil = one :< zero  -- Semiring s needed here
     cons c x = zero :< (\ d -> if d == c then x else zero) -- (c +-> x)
#endif

-- Is HasSingle even useful on Decomp?
