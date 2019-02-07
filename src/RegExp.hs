{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Regular expressions

module RegExp where

import Prelude hiding (sum,product)

import Semi
import Language

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

instance Additive b => Additive (RegExp c b) where
  zero  = Value zero
  (<+>) = (:<+>)

instance Semiring b => Semimodule b (RegExp c b) where
  scale b = go
   where
     go (Char c)   = Char c
     go (Value b') = Value (b <.> b')
     go (u :<+> v) = go u <+> go v
     go (u :<.> v) = go u <.> go v
     go (Star u)   = star (go u)

instance Semiring b => Semiring (RegExp c b) where
  one   = Value one
  (<.>) = (:<.>)

instance Semiring b => StarSemiring (RegExp c b) where
  star = Star

instance Semiring b => HasSingle [c] b (RegExp c b) where
  w +-> b = product (map Char w) <.> Value b

instance (Eq c, StarSemiring b) => Decomposable b ((->) c) (RegExp c b) where
  e <: d = Value e <+> sum [ single [c] <.> d c | c <- allVals ]

  atEps (Char _)   = zero
  atEps (Value b)  = b
  atEps (p :<+> q) = atEps p <+> atEps q
  atEps (p :<.> q) = atEps p <.> atEps q
  atEps (Star p)   = star (atEps p)
  
  deriv (Char c') c   = equal c' c
  deriv (Value _) _   = zero
  deriv (p :<+> q) c  = deriv p c <+> deriv q c
  deriv (p :<.> q) c  = -- deriv p c <.> q <+> Value (atEps p) <.> deriv q c
                        Value (atEps p) <.> deriv q c <+> deriv p c <.> q
  deriv (Star p) c = -- The following version works even if the atEps term
                        -- comes first in deriv (p :<.> q) c
                        Value (star (atEps p)) <.> deriv p c <.> star p
                        -- See 2018-01-13 journal.
                        -- The following version converges if the atEps term
                        -- comes second in deriv (p :<.> q) c
                        -- deriv (p <.> Star p) c -- since deriv c one = zero
                        -- deriv c (one <+> p <.> Star p)

-- TODO: fix deriv c (Star p) to compute deriv p c and deriv c (Star p)
-- just once. Do a bit of inlining and simplification.

-- | Interpret a regular expression
regexp :: (Semiring b, Semimodule b x, StarSemiring x, HasSingle [c] b x, DetectableZero b)
       => RegExp c b -> x
regexp (Char c)     = single [c]
regexp (Value b)    = value b
regexp (u  :<+>  v) = regexp u <+> regexp v
regexp (u  :<.>  v) = regexp u <.> regexp v
regexp (Star u)     = star (regexp u)

instance (StarSemiring b, Eq c, DetectableZero b)
      => Indexable [c] b (RegExp c b) where
  (!) = regexp

-- Alternatively, use regexp to convert to LTrie, and then use (!).