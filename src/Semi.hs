{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Commutative monoids, semirings, and semimodules

module Semi where

import Control.Applicative (liftA2)
import GHC.Natural (Natural)

-- | Commutative monoid
class Additive b where
  infixl 6 <+>
  (<+>) :: b -> b -> b
  zero :: b

class Additive b => Semimodule b s | b -> s where scale :: s -> b -> b

class Additive b => Semiring b where
  infixl 7 <.>
  (<.>) :: b -> b -> b
  one :: b

instance Additive Bool where
  (<+>) = (||)
  zero = False

instance Semiring Bool where
  (<.>) = (&&)
  one = True

#define Nums(t) \
instance Additive (t) where { (<+>) = (+) ; zero = 0 } ; \
instance Semiring (t) where { (<.>) = (*) ; one  = 1 } ; \
instance Semimodule (t) (t) where { scale = (*) } ;

-- Do I really want these Semimodule instances?

Nums(Integer)
Nums(Natural)
Nums(Int)
Nums(Float)
Nums(Double)
-- etc

#if 1

instance Additive b => Additive (a -> b) where
  (<+>) = liftA2 (<+>)
  zero = pure zero

instance Semiring b => Semiring (a -> b) where
  (<.>) = liftA2 (<.>)
  one = pure one

instance Semimodule b s => Semimodule (a -> b) s where
  scale s = fmap (scale s)

#else
instance Additive b => Additive (a -> b) where
  f <+> g = \ a -> f a <+> g a
  zero = const zero

instance Semiring b => Semiring (a -> b) where
  f <.> g = \ a -> f a <.> g a
  one = const one
#endif