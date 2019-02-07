-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | List tries

module LTrie where

import Prelude hiding (sum,product)

import Data.Map (Map)
import qualified Data.Map as M

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
#if 0
  -- Oops. We don't have Semiring (LTrie c s) for product.
  single w = product (map symbol w) where symbol c = zero <: singleton c one
  -- single = product . map symbol
  --  where
  --    symbol c = zero :< singleton c one
#else
  -- More streamlined
  single = foldr cons nil
   where
     nil = one :< zero  -- Semiring s needed here
     cons c x = zero :< M.singleton c x
#endif

-- Is HasSingle even useful on LTrie?

-- No Semiring instance, because one would have to map all possible keys to one.
-- Finite maps have the same problem, which we inherit here.

-- | Trim to a finite depth, for examination.
trimT :: (Ord c, Additive b) => Int -> LTrie c b -> LTrie c b
trimT 0 _ = zero
trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts

instance Decomposable b (Map c) (LTrie c b) where
  (<:) = (:<)
  decomp (b :< dp) = (b, dp)

type LTrie' b c = Convo (LTrie c b)

deriving instance (Ord c, Semiring b) => HasSingle [c] (LTrie' b c)
