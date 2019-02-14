#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | List tries

module LTrie where

import Prelude hiding (sum,product)

import GHC.Exts (coerce)
import Data.Map (Map)
import qualified Data.Map as M

import Constrained
import Semi hiding (pattern (:<:))
import Language

#ifdef EXAMPLES
import Examples
#endif

#include "GenInstances.inc"

-- | List trie, denoting '[c] -> b'"
infix 1 :<
data LTrie c b = b :< (c ->* LTrie c b) -- deriving Show

instance (Show c, Show b) => Show (LTrie c b) where
  showsPrec p (a :< dp) = showParen (p >= 1) $ showsPrec 2 a . showString " :< " . showsPrec 2 (M.toList dp)

instance Functor (LTrie c) where
  fmap f = go where go (a :< dp) = f a :< fmap go dp
  -- fmap f (a :< dp) = f a :< (fmap.fmap) f dp
  -- fmap f (a :< dp) = f a :< fmap (fmap f) dp

instance FunctorC (LTrie c)

instance (Ord c, Additive b) => Indexable [c] b (LTrie c b) where
  (b :< dp) ! w = case w of { [] -> b ; c:cs -> dp ! c ! cs }
  -- (a :< _ ) ! [] = a
  -- (_ :< dp) ! (c:cs) = (dp ! c) ! cs
  -- (!) (a :< dp) = a <: (!) . (dp !)

instance (Ord c, Additive b) => Additive (LTrie c b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

FunctorSemimodule(LTrie c)

-- instance (Ord c, Semiring b) => LeftSemimodule b (LTrie c b) where scale s = fmap (s <.>)

-- instance (Ord c, Semiring b) => LeftSemimodule b (LTrie c b) where
--   s `scale` (b :< dp) = s <.> b :< fmap (s `scale`) dp

instance (Ord c, Additive b, DetectableZero b) => DetectableZero (LTrie c b) where
  isZero (a :< dp) = isZero a && isZero dp

-- instance (Ord c, Additive b, DetectableOne b) => DetectableOne (LTrie c b) where
--   isOne (a :< dp) = isOne a && isZero dp

instance (Ord c, Additive b) => HasSingle [c] b (LTrie c b) where
#if 0
  w +-> b = case w of { [] -> b :< zero ; c:cs -> zero :< (c +-> cs +-> b) }
#elif 0
  []   +-> b = b :< zero
  c:cs +-> b = zero :< (c +-> cs +-> b)
#elif 1
  w +-> b = foldr (\ c t -> zero :< (c +-> t)) (b :< zero) w
#else
  w +-> b = foldr cons nil w
   where
     -- nil :: LTrie c b
     nil = b :< zero
     -- cons :: c -> LTrie c b -> LTrie c b
     cons c x = zero :< (c +-> x)
#endif

-- Is HasSingle even useful on LTrie? Yes, to inherit from LTrie'

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

#if 0

type LTrie' b c = Convo (LTrie c b)

trimT' :: (Ord c, Additive b, DetectableZero b) => Int -> LTrie' b c -> LTrie' b c
trimT' n (C x) = C (trimT n x)

#else

newtype LTrie' b c = L (LTrie c b) deriving (Additive, HasSingle [c] b, LeftSemimodule b, Indexable [c] b)

-- Derive Indexable?

-- unL :: LTrie' b c -> LTrie c b
-- unL (L t) = t

infix 1 :<:
pattern (:<:) :: b -> (c ->* LTrie' b c) -> LTrie' b c
pattern b :<: d <- L (b :< (coerce -> d)) where b :<: d = L (b :< coerce d)

-- pattern b :<: d <- L (b :< (fmap L -> d)) where b :<: d = L (b :< fmap unL d)

-- TODO: Use this version in the paper.


{-# COMPLETE (:<:) :: LTrie' #-}

trieFun' :: (Ord c, Additive b) => LTrie' b c -> (b <-- [c])
trieFun' (L t) = C (t !)

instance (Ord c, Semiring b, DetectableZero b) => Semiring (LTrie' b c) where
  one = one :<: zero
  (a :<: dp) <.> q = a .> q <+> (zero :<: fmap (<.> q) dp)

instance (Ord c, StarSemiring b, DetectableZero b) => StarSemiring (LTrie' b c) where
  star (a :<: dp) = q where q = star a .> (one :<: fmap (<.> q) dp)

#endif

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
