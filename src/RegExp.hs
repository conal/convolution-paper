#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | Regular expressions

module RegExp where

import Prelude hiding (sum,product)

import Data.Map (Map,keys)

import Semi hiding (Decomposable(..))

#ifdef EXAMPLES
import Examples
#endif

infixl 6 :<+>
infixl 7 :<.>

-- | Regular expression
data RegExp h b = Char (Key h)
                | Value b
                | RegExp h b :<+> RegExp h b
                | RegExp h b :<.> RegExp h b
                | Star (RegExp h b)
               -- deriving (Show,Eq)
              
-- #define OPTIMIZE

#ifdef OPTIMIZE

type D0 b = DetectableZero b
type D1 b = DetectableOne b

instance DetectableZero b => DetectableZero (RegExp h b) where
  isZero (Value b) = isZero b
  isZero _         = False

instance (DetectableZero b, DetectableOne b) => DetectableOne (RegExp h b) where
  isOne (Value b) = isOne b
  isOne _         = False

#else

type D0 b = (() ~ ())
type D1 b = (() ~ ())

#endif

instance (D0 b, Additive b) => Additive (RegExp h b) where
  zero  = Value zero
#ifdef OPTIMIZE
  p <+> q | isZero q  = p
          | isZero p  = q
          | otherwise = p :<+> q
#else
  (<+>) = (:<+>)
#endif

instance (Semiring b, D0 b, D1 b) => LeftSemimodule b (RegExp h b) where
#if 1
  b `scale` e = Value b <.> e
#else
  scale b = go
   where
     go (Char c)   = Char c
     go (Value b') = Value (b <.> b')
     go (u :<+> v) = go u <+> go v
     go (u :<.> v) = go u <.> go v
     go (Star u)   = star (go u)
#endif

instance (D0 b, D1 b, Semiring b) => Semiring (RegExp h b) where
  one   = Value one
#ifdef OPTIMIZE
  p <.> q | isOne q   = p
          | isOne p   = q
          | otherwise = p :<.> q
#else
  (<.>) = (:<.>)
#endif

instance (D0 b, D1 b, Semiring b) => StarSemiring (RegExp h b) where
  star = Star

instance (StarSemiring b, DetectableZero b, Eq (Key h)) => Indexable (RegExp h) b where
  type Key (RegExp h) = [Key h]
  e ! w = atEps (foldl deriv e w)

instance (StarSemiring b, DetectableZero b, Eq (Key h)) => HasSingle (RegExp h) b where
  w +-> b = b .> product (map Char w)

atEps :: StarSemiring b => RegExp h b -> b
atEps (Char _)   = zero
atEps (Value b)  = b
atEps (p :<+> q) = atEps p <+> atEps q
atEps (p :<.> q) = atEps p <.> atEps q
atEps (Star p)   = star (atEps p)

deriv :: (StarSemiring b, DetectableZero b, Eq (Key h)) => RegExp h b -> Key h -> RegExp h b
deriv (Char c)   = single c
deriv (Value _)  = zero
deriv (p :<+> q) = deriv p <+> deriv q
deriv (p :<.> q) = \ c -> atEps p .> deriv q c <+> deriv p c <.> q
                   -- fmap (atEps p .>) (deriv q) <+> fmap (<.> q) (deriv p)
deriv (Star p)   = \ c -> star (atEps p) .> deriv p c <.> star p
                   -- fmap (\ d -> star (atEps p) .> d <.> Star p) (deriv p)

-- | Interpret a regular expression
regexp :: (StarSemiring (f b), HasSingle f b, Semiring b, Key f ~ [Key h])
       => RegExp h b -> f b
regexp (Char c)   = single [c]
regexp (Value b)  = value b
regexp (u :<+> v) = regexp u <+> regexp v
regexp (u :<.> v) = regexp u <.> regexp v
regexp (Star u)   = star (regexp u)


-- Alternatively, use regexp to convert to LTrie, and then use (!).

#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L  = RegExp (Map Char) Bool
-- type L' = Convo L

-- Non-recursive examples are tidier with OPTIMIZE

-- >>> pig :: L
-- Char 'p' :<.> (Char 'i' :<.> Char 'g')
-- >>> pink :: L
-- Char 'p' :<.> (Char 'i' :<.> (Char 'n' :<.> Char 'k'))
-- >>> pp :: L
-- Char 'p' :<.> (Char 'i' :<.> (Char 'n' :<.> Char 'k')) :<+> Char 'p' :<.> (Char 'i' :<.> Char 'g')

-- >>> pig :: L'
-- C (Char 'p' :<.> (Char 'i' :<.> Char 'g'))
-- >>> pink :: L'
-- C (Char 'p' :<.> (Char 'i' :<.> (Char 'n' :<.> Char 'k')))
-- >>> pp :: L'
-- C (Char 'p' :<.> (Char 'i' :<.> (Char 'n' :<.> Char 'k')) :<+> Char 'p' :<.> (Char 'i' :<.> Char 'g'))

-- >>> pig :: L'
-- C ((Char 'p' :<.> (Char 'i' :<.> (Char 'g' :<.> Value True))) :<.> Value True)
-- >>> pink :: L'
-- C ((Char 'p' :<.> (Char 'i' :<.> (Char 'n' :<.> (Char 'k' :<.> Value True)))) :<.> Value True)
-- >>> pp :: L'
-- C ((Char 'p' :<.> (Char 'i' :<.> (Char 'n' :<.> (Char 'k' :<.> Value True)))) :<.> Value True :<+> (Char 'p' :<.> (Char 'i' :<.> (Char 'g' :<.> Value True))) :<.> Value True)
-- >>> (anbn :: L') ! ""
-- True
-- >>> deriv (anbn :: L')

-- The following examples wedge. I think they worked when we used functions
-- instead of maps.

-- >>> (anbn :: L') ! "a"
-- False
-- >>> (anbn :: L') ! "ab"
-- True
-- >>> (anbn :: L') ! "aabb"
-- True
-- >>> (anbn :: L') ! "aaaaabbbbb"
-- True

#endif
