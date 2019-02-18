#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | List tries using Convo

module LTrie where

import Prelude hiding (sum,product)

import Data.Functor.Classes (Show1(..))
import GHC.Exts (coerce)
import Data.Map (Map)
import qualified Data.Map as M

import Misc
import Constrained
import Semi

#ifdef EXAMPLES
import Examples
#endif

-- #include "GenInstances.inc"

-- TODO: maybe rename LTrie to "Cofree". I'd use Ed's Cofree from the "free" library,
-- but he defined Key (Cofree f) = Seq (Key f), and I want [Key f]. Oh well.

-- | List trie, denoting '[c] -> b'"
infix 1 :<
data LTrie h b = b :< h (LTrie h b) -- deriving Show

instance Functor h => Functor (LTrie h) where
  fmap f = go where go (a :< dp) = f a :< fmap go dp
  -- fmap f (a :< dp) = f a :< (fmap.fmap) f dp
  -- fmap f (a :< dp) = f a :< fmap (fmap f) dp

-- TODO: I probably want FunctorC h, and inherit Ok.
instance Functor h => FunctorC (LTrie h)

instance (Indexable h, Additive1 h) => Indexable (LTrie h) where
  type instance Key (LTrie h) = [Key h]
  -- (b :< _ ) ! [] = b
  -- (_ :< ts) ! (k:ks) = ts ! k ! ks
  (b :< dp) ! w = case w of { [] -> b ; c:cs -> dp ! c ! cs }

instance (Additive1 h, Additive b) => Additive (LTrie h b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

-- FunctorSemimodule(LTrie h)

-- instance (Functor h, Semiring b) => LeftSemimodule b (LTrie h b) where scale s = fmap (s <.>)

-- instance (Functor h, Semiring b) => LeftSemimodule b (LTrie h b) where
--   s `scale` (b :< dp) = s <.> b :< fmap (s `scale`) dp

instance (Functor h, Semiring b) => LeftSemimodule b (LTrie h b) where
  scale s = go where go (b :< dp) = s <.> b :< fmap go dp

instance (Additive1 h, DetectableZero (h (LTrie h b)), DetectableZero b) => DetectableZero (LTrie h b) where
  isZero (a :< dp) = isZero a && isZero dp

instance (Functor h, Additive1 h, Semiring b, DetectableZero b) => Semiring (LTrie h b) where
  one = one :< zero
  (a :< dp) <.> q = a .> q <+> (zero :< fmap (<.> q) dp)

instance (Functor h, Additive1 h, DetectableZero1 h, DetectableZero b, DetectableOne b) => DetectableOne (LTrie h b) where
  isOne (a :< dp) = isOne a && isZero dp

instance (Functor h, Additive1 h, StarSemiring b, DetectableZero b) => StarSemiring (LTrie h b) where
  star (a :< dp) = q where q = star a .> (one :< fmap (<.> q) dp)

instance (HasSingle h, Additive1 h) => HasSingle (LTrie h) where
  w +-> b = foldr (\ c t -> zero :< c +-> t) (b :< zero) w

-- | Trim to a finite depth, for examination.
trimT :: (Functor h, Additive1 h, Additive b, DetectableZero b) => Int -> LTrie h b -> LTrie h b
trimT 0 _ = zero
trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts

#if 0

#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L  = LTrie  Char Bool

-- >>> pig :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< [])])])]
-- >>> pink :: L
-- False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])]
-- >>> pp :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])]

-- >>> trimT 3 as :: L
-- True :< [('a',True :< [('a',True :< [])])]
-- >>> trimT 3 ass :: L
-- True :< [('a',True :< [('a',True :< [])])]

-- >>> trimT 7 anbn :: L
-- True :< [('a',False :< [('a',False :< [('a',False :< [('b',False :< [('b',False :< [('b',True :< [])])])]),('b',False :< [('b',True :< [])])]),('b',True :< [])])]

-- >>> (anbn :: L) ! ""
-- True
-- >>> (anbn :: L) ! "a"
-- False
-- >>> (anbn :: L) ! "ab"
-- True
-- >>> (anbn :: L) ! "aabb"
-- True
-- >>> (anbn :: L) ! "aaaaabbbbb"
-- True

#endif

#endif
