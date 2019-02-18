{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples

-- | Streams (infinite lists)

module Stream where

import Control.Applicative (Applicative(..))
import Data.Functor.Identity (Identity(..))

import Constrained
import Semi

#include "GenInstances.inc"

infixr 1 :<
data Stream b = b :< Stream b

instance Additive b => Additive (Stream b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

instance Semiring b => LeftSemimodule b (Stream b) where
  scale s = go where go (b :< dp) = s <.> b :< go dp

instance (Additive b, DetectableZero b) => DetectableZero (Stream b) where
  isZero (a :< dp) = isZero a && isZero dp

instance (Semiring b, DetectableZero b) => Semiring (Stream b) where
  one = one :< zero
  (a :< dp) <.> q = a .> q <+> (zero :< dp <.> q)

instance (Additive b, DetectableZero b, DetectableOne b) => DetectableOne (Stream b) where
  isOne (a :< dp) = isOne a && isZero dp

instance (StarSemiring b, DetectableZero b) => StarSemiring (Stream b) where
  star (a :< dp) = q where q = star a .> (one :< dp <.> q)

instance Additive b => HasSingle N b (Stream b) where
  w +-> b = foldN (zero :<) (b :< zero) w

foldN :: (b -> b) -> b -> N -> b
foldN h e 0 = e
foldN h e n = foldN h (h e) (n-1)

instance Indexable N b (Stream b) where
  (b :< bs) ! n = if n == 0 then b else bs ! (n-1)
