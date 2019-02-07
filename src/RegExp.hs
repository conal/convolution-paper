{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Regular expressions

module RegExp where

import Prelude hiding (sum,product)

import Semi
import Language

infixl 6 :<+>
infixl 7 :<.>

-- | Regular expression
data RegExp c s =
    Char c
  | Value s
  | RegExp c s :<+> RegExp c s
  | RegExp c s :<.> RegExp c s
  | Star (RegExp c s)
 deriving (Show,Eq)

instance Additive s => Additive (RegExp c s) where
  zero  = Value zero
  (<+>) = (:<+>)

instance Semiring s => Semimodule s (RegExp c s) where
  scale s = go
   where
     go (Char c)   = Char c
     go (Value s') = Value (s <.> s')
     go (u :<+> v) = go u <+> go v
     go (u :<.> v) = go u <.> go v
     go (Star u)   = star (go u)

instance Semiring s => Semiring (RegExp c s) where
  one   = Value one
  (<.>) = (:<.>)

instance Semiring s => StarSemiring (RegExp c s) where
  star = Star

instance Semiring s => HasSingle [c] (RegExp c s) where
  single = product . map Char

instance (Eq c, StarSemiring s) => Decomposable s ((->) c) (RegExp c s) where
  e <: d = Value e <+> sum [ single [c] <.> d c | c <- allVals ]

  atEps (Char _)   = zero
  atEps (Value s)  = s
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
regexp :: (StarSemiring x, Semiring s, HS x c s) => RegExp c s -> x
regexp (Char c)      = single [c]
regexp (Value s)     = value s
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Star u)   = star (regexp u)
