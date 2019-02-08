#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | List tries

module LTrie where

import Prelude hiding (sum,product)

import Data.Map (Map)
import qualified Data.Map as M

import Constrained
import Semi
import Language

#ifdef EXAMPLES
import Examples
#endif

#include "GenInstances.inc"

-- | List trie, denoting '[c] -> b'"
infix 1 :<
data LTrie c b = b :< Map c (LTrie c b) -- deriving Show

instance (Show c, Show b) => Show (LTrie c b) where
  showsPrec p (a :< dp) = showParen (p >= 1) $ showsPrec 2 a . showString " :< " . showsPrec 2 (M.toList dp)

instance Functor (LTrie c) where
  fmap f = go where go (a :< dp) = f a :< fmap go dp

instance FunctorC (LTrie c)

-- trieFun :: (Ord c, Additive b) => LTrie c b -> ([c] -> b)
-- trieFun (a :< dp) = a <: trieFun . (dp !)

instance (Ord c, Additive b) => Indexable [c] b (LTrie c b) where
  -- (!) = trieFun
  (!) (a :< dp) = a <: (!) . (dp !)
  -- (a :< _ ) ! [] = a
  -- (_ :< dp) ! (c:cs) = (dp ! c) ! cs

instance (Ord c, Additive b) => Additive (LTrie c b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

FunctorSemimodule(LTrie c)

instance (Ord c, Additive b, DetectableZero b) => DetectableZero (LTrie c b) where
  isZero (a :< dp) = isZero a && isZero dp

-- instance (Ord c, Additive b, DetectableOne b) => DetectableOne (LTrie c b) where
--   isOne (a :< dp) = isOne a && isZero dp

instance (Ord c, Additive b) => HasSingle [c] b (LTrie c b) where
  w +-> b = foldr cons nil w
   where
     nil :: LTrie c b
     nil = b :< zero
     cons :: c -> LTrie c b -> LTrie c b
     cons c x = zero :< (c +-> x)

-- Is HasSingle even useful on LTrie?

-- No Semiring instance, because one would have to map all possible keys to one.
-- We inherit this limitation from finite maps.

-- | Trim to a finite depth, for examination.
trimT :: (Ord c, Additive b, DetectableZero b) => Int -> LTrie c b -> LTrie c b
trimT 0 _ = zero
-- trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts
trimT n (c :< ts) = c :< M.filter (not . isZero) (fmap (trimT (n-1)) ts)

instance Decomposable b (Map c) (LTrie c b) where
  (<:) = (:<)
  decomp (b :< dp) = (b, dp)

type LTrie' b c = Convo (LTrie c b)

trimT' :: (Ord c, Additive b, DetectableZero b) => Int -> LTrie' b c -> LTrie' b c
trimT' n (C x) = C (trimT n x)

#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L  = LTrie  Char Bool
type L' = Convo L

-- >>> pig :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< [])])])]
-- >>> pink :: L
-- False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])]
-- >>> pp :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])]

-- >>> pig :: L'
-- C (False :< [('p',False :< [('i',False :< [('g',True :< [])])])])
-- >>> pink :: L'
-- C (False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])])
-- >>> pp :: L'
-- C (False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])])

-- >>> pig :: L'
-- C (False :< [('p',False :< [('i',False :< [('g',True :< [])])])])
-- >>> pink :: L'
-- C (False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])])
-- >>> pp :: L'
-- C (False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])])

-- >>> trimT' 3 as :: L'
-- C (True :< [('a',True :< [('a',True :< [])])])
-- >>> trimT' 3 ass :: L'
-- C (True :< [('a',True :< [('a',True :< [])])])

-- >>> trimT' 7 anbn :: L'
-- C (True :< [('a',False :< [('a',False :< [('a',False :< [('b',False :< [('b',False :< [('b',True :< [])])])]),('b',False :< [('b',True :< [])])]),('b',True :< [])])])

-- >>> (anbn :: L') ! ""
-- True
-- >>> (anbn :: L') ! "a"
-- False
-- >>> (anbn :: L') ! "ab"
-- True
-- >>> (anbn :: L') ! "aabb"
-- True
-- >>> (anbn :: L') ! "aaaaabbbbb"
-- True

#endif
