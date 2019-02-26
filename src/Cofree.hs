#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | List tries using Convo

module Cofree where

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

-- TODO: maybe rename Cofree to "Cofree". I'd use Ed's Cofree from the "free" library,
-- but he defined Key (Cofree f) = Seq (Key f), and I want [Key f]. Oh well.

-- Move elsewhere

infix 1 <:
(<:) :: b -> (c -> ([c] -> b)) -> ([c] -> b)
b <: h = \ case { [] -> b ; c:cs  -> h c cs }

-- -- Experiment
-- infix 1 <#
-- (<#) :: (Indexable ([c] -> b) h, Key h ~ c)
--      => b -> h ([c] -> b) -> ([c] -> b)
-- b <# h = \ case { [] -> b ; c:cs  -> (h ! c) cs }

-- | List trie, denoting '[c] -> b'
infix 1 :<
data Cofree h b = b :< h (Cofree h b) deriving Functor

-- instance Functor h => Functor (Cofree h) where
--   fmap f = go where go (a :< dp) = f a :< fmap go dp
--   -- fmap f (a :< dp) = f a :< (fmap.fmap) f dp
--   -- fmap f (a :< dp) = f a :< fmap (fmap f) dp

-- TODO: I probably want FunctorC h, and inherit Ok.
instance Functor h => FunctorC (Cofree h)

instance Indexable c (Cofree h b) (h (Cofree h b)) => Indexable [c] b (Cofree h b) where
  -- (b :< _ ) ! [] = b
  -- (_ :< ts) ! (k:ks) = ts ! k ! ks
  -- (b :< dp) ! w = case w of { [] -> b ; c:cs -> dp ! c ! cs }
  -- (!) (b :< dp) = b <: (!) (fmap (!) dp)
  (!) (b :< dp) = b <: (!) . (!) dp

instance (Additive (h (Cofree h b)), Additive b) => Additive (Cofree h b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

-- FunctorSemimodule(Cofree h)

-- instance (Functor h, Semiring b) => LeftSemimodule b (Cofree h b) where scale s = fmap (s <.>)

-- instance (Functor h, Semiring b) => LeftSemimodule b (Cofree h b) where
--   s `scale` (b :< dp) = s <.> b :< fmap (s `scale`) dp

instance (Functor h, Semiring b) => LeftSemimodule b (Cofree h b) where
  scale s = fmap (s <.>)
  -- scale s = go where go (b :< dp) = s <.> b :< fmap go dp

instance (Functor h, Additive (h (Cofree h b)), Semiring b, DetectableZero b, DetectableOne b) => Semiring (Cofree h b) where
  one = one :< zero
  (a :< dp) <.> q = a .> q <+> (zero :< fmap (<.> q) dp)

instance (Functor h, Additive (h (Cofree h b)), StarSemiring b, DetectableZero b, DetectableOne b) => StarSemiring (Cofree h b) where
  star (a :< dp) = q where q = star a .> (one :< fmap (<.> q) dp)

instance (HasSingle c (Cofree h b) (h (Cofree h b)), Additive (h (Cofree h b)), Additive b) => HasSingle [c] b (Cofree h b) where
  w +-> b = foldr (\ c t -> zero :< c +-> t) (b :< zero) w

instance (Additive (h (Cofree h b)), DetectableZero (h (Cofree h b)), DetectableZero b)
      => DetectableZero (Cofree h b) where
  isZero (a :< dp) = isZero a && isZero dp

instance (Functor h, Additive (h (Cofree h b)), DetectableZero b, DetectableZero (h (Cofree h b)), DetectableOne b)
      => DetectableOne (Cofree h b) where
  isOne (a :< dp) = isOne a && isZero dp

-- | Trim to a finite depth, for examination.
trimT :: (Functor h, Additive (h (Cofree h b)), Additive b, DetectableZero b) => Int -> Cofree h b -> Cofree h b
trimT 0 _ = zero
trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts

#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L  = Cofree (Map Char) Bool

-- >>> pig :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< [])])])]
-- >>> pink :: L
-- False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])]
-- >>> pp :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])]

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

-- >>> (pig :: L) ! ""
-- False
-- >>> (pig :: L) ! "pi"
-- False
-- >>> (pig :: L) ! "pig"
-- True
-- >>> (pig :: L) ! "piggy"
-- False

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
