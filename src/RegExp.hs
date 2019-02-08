#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | Regular expressions

module RegExp where

import Prelude hiding (sum,product)

import Data.Map (Map,keys)

import Semi
import Language

#ifdef EXAMPLES
import Examples
#endif

infixl 6 :<+>
infixl 7 :<.>

-- | Regular expression
data RegExp c b =
    Char c
  | Value b
  | RegExp c b :<+> RegExp c b
  | RegExp c b :<.> RegExp c b
  | Star (RegExp c b)
 deriving (Show,Eq)

-- If I use Convo, I think I can remove (:<.>) and Star and the Semiring
-- instance. Maybe keep for comparison.

-- #define OPTIMIZE

#ifdef OPTIMIZE

type D b = (DetectableZero b, DetectableOne b)

instance D b => DetectableZero (RegExp c b) where
  isZero (Value b) = isZero b
  isZero _         = False

instance D b => DetectableOne (RegExp c b) where
  isOne (Value b) = isOne b
  isOne _         = False

#else

type D b = (() ~ ())

#endif

instance (D b, Additive b) => Additive (RegExp c b) where
  zero  = Value zero
#ifdef OPTIMIZE
  p <+> q | isZero q  = p
          | isZero p  = q
          | otherwise = p :<+> q
#else
  (<+>) = (:<+>)
#endif

instance (D b, Semiring b) => Semimodule b (RegExp c b) where
  scale b = go
   where
     go (Char c)   = Char c
     go (Value b') = Value (b <.> b')
     go (u :<+> v) = go u <+> go v
     go (u :<.> v) = go u <.> go v
     go (Star u)   = star (go u)

instance (D b, Semiring b) => Semiring (RegExp c b) where
  one   = Value one
#ifdef OPTIMIZE
  p <.> q | isOne q   = p
          | isOne p   = q
          | otherwise = p :<.> q
#else
  (<.>) = (:<.>)
#endif

instance (D b, Semiring b) => StarSemiring (RegExp c b) where
  star = Star

instance (D b, Semiring b) => HasSingle [c] b (RegExp c b) where
  w +-> b = product (map Char w) <.> Value b

instance (D b, Ord c, StarSemiring b, DetectableZero b)
      => Decomposable b (Map c) (RegExp c b) where
  e <: d = Value e <+> sum [ single [c] <.> d ! c | c <- keys d ]

  atEps (Char _)   = zero
  atEps (Value b)  = b
  atEps (p :<+> q) = atEps p <+> atEps q
  atEps (p :<.> q) = atEps p <.> atEps q
  atEps (Star p)   = star (atEps p)
  
  deriv (Char c)   = single c
  deriv (Value _)  = zero
  deriv (p :<+> q) = deriv p <+> deriv q
  deriv (p :<.> q) = fmap (atEps p .>) (deriv q) <+> fmap (<.> q) (deriv p)
  deriv (Star p)   = fmap (\ d -> star (atEps p) .> d <.> Star p) (deriv p)

-- | Interpret a regular expression
regexp :: (Semiring b, Semimodule b x, StarSemiring x, HasSingle [c] b x, DetectableZero b)
       => RegExp c b -> x
regexp (Char c)     = single [c]
regexp (Value b)    = value b
regexp (u  :<+>  v) = regexp u <+> regexp v
regexp (u  :<.>  v) = regexp u <.> regexp v
regexp (Star u)     = star (regexp u)

instance (StarSemiring b, Ord c, DetectableZero b, D b)
      => Indexable [c] b (RegExp c b) where
  -- e ! w = (regexp e :: b <-- [c]) ! w
  (!) = accept

-- Alternatively, use regexp to convert to LTrie, and then use (!).


#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L  = RegExp Char Bool
type L' = Convo L

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
