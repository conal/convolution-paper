#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | Regular expressions

module RegExp where

import Prelude hiding (sum,product)

import Data.Map (Map,keys)
import Data.MemoTrie ((:->:))

import Semi

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
 deriving Functor

deriving instance (Show (Key h), Show b) => Show (RegExp h b)
deriving instance (Eq   (Key h), Eq   b) => Eq   (RegExp h b)

#define OPTIMIZE

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
  zero = Value zero
#ifdef OPTIMIZE
  p <+> q | isZero p  = q
          | isZero q  = p
          | otherwise = p :<+> q
#else
  (<+>) = (:<+>)
#endif

instance (Semiring b, D0 b, D1 b) => LeftSemimodule b (RegExp h b) where
#if 1
  scale b = fmap (b <.>)
#elif 1
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
  p <.> q | isZero p = zero
          | isOne  p = q
          -- | isZero q  = zero
          -- | isOne  q  = p
          | otherwise = p :<.> q
#else
  (<.>) = (:<.>)
#endif

instance (D0 b, D1 b, Semiring b) => StarSemiring (RegExp h b) where
#if 0
  -- Slightly slower in all benchmarks I tested
  star p | isZero p  = one
         | otherwise = Star p
#else
  star = Star
#endif

type FR h b = ( Additive (h (RegExp h b)), HasSingle (Key h) (RegExp h b) (h (RegExp h b))
              , Functor h, DetectableZero b, DetectableOne b )

instance (FR h b, StarSemiring b, c ~ Key h, Eq c)
      => Indexable [c] b (RegExp h b) where
  e ! w = atEps (foldl ((!) . deriv) e w)
  -- (!) e = atEps . foldl ((!) . deriv) e

instance (FR h b, StarSemiring b, c ~ Key h, Eq c)
      => HasSingle [c] b (RegExp h b) where
  w +-> b = b .> product (map Char w)

atEps :: StarSemiring b => RegExp h b -> b
atEps (Char _)   = zero
atEps (Value b)  = b
atEps (p :<+> q) = atEps p <+> atEps q
atEps (p :<.> q) = atEps p <.> atEps q
atEps (Star p)   = star (atEps p)

deriv :: (FR h b, StarSemiring b)
      => RegExp h b -> h (RegExp h b)
deriv (Char c)   = single c
deriv (Value _)  = zero
deriv (p :<+> q) = deriv p <+> deriv q
deriv (p :<.> q) = fmap (<.> q) (deriv p) <+> fmap (atEps p .>) (deriv q)
                   -- fmap (atEps p .>) (deriv q) <+> fmap (<.> q) (deriv p)
deriv (Star p)   = fmap (\ d -> star (atEps p) .> d <.> Star p) (deriv p)

-- | Interpret a regular expression
regexp :: (StarSemiring x, HasSingle [Key h] b x, Semiring b) => RegExp h b -> x
regexp (Char c)   = single [c]
regexp (Value b)  = value b
regexp (u :<+> v) = regexp u <+> regexp v
regexp (u :<.> v) = regexp u <.> regexp v
regexp (Star u)   = star (regexp u)


-- Alternatively, use regexp to convert to Cofree, and then use (!).

#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L = RegExp ((->) Char) Bool
-- type L = RegExp (Map Char) Bool

star1 :: Semiring b => b -> b
star1 b = one <+> b <.> star1 b

star2 :: L -> L
star2 b = one <+> b <.> star2 b

star3 :: L -> L
star3 b = Value True <+> b <.> star3 b

x1 :: L
x1 = star1 (single "a")

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


#if 0
#endif
