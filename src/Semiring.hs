{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Semirings

module Semiring where

class Semiring a where
  infixl 7 <.>
  infixl 6 <+>
  zero, one     :: a
  (<+>), (<.>)  :: a -> a -> a

class Semiring a => ClosedSemiring a where
  closure :: a -> a
  closure p = q where q = one <+> p <.> q

class HasSingle a s where
  single :: s -> a

instance Semiring Integer where
  zero = 0
  one = 1
  (<+>) = (+)
  (<.>) = (*)

instance Semiring Bool where
  zero = False
  one = True
  (<+>) = (||)
  (<.>) = (&&)

instance ClosedSemiring Bool where
  closure _ = one

newtype Sum a = Sum { getSum :: a }

instance Semiring a => Semigroup (Sum a) where
  Sum a <> Sum b = Sum (a <+> b)

instance Semiring a => Monoid (Sum a) where
  mempty = Sum zero

sum :: (Foldable f, Semiring a) => f a -> a
sum = getSum . foldMap Sum

newtype Product a = Product { getProduct :: a }

instance Semiring a => Semigroup (Product a) where
  Product a <> Product b = Product (a <.> b)

instance Semiring a => Monoid (Product a) where
  mempty = Product one

product :: (Foldable f, Semiring a) => f a -> a
product = getProduct . foldMap Product

class Semiring a => DetectableZero a  where
  isZero :: a -> Bool

instance DetectableZero Bool where isZero = not

-- Variants

sum' :: (Foldable f, Semiring a) => f a -> a
sum' = foldr (<+>) zero

product' :: (Foldable f, Semiring a) => f a -> a
product' = foldr (<.>) one

{--------------------------------------------------------------------
    Language operations. Move elsewhere.
--------------------------------------------------------------------}

class HasDecomp a c s | a -> c s where
  atEps :: a -> s
  deriv :: c -> a -> a

-- | Derivative of a language w.r.t a string
derivs :: HasDecomp a c s => [c] -> a -> a
derivs s p = foldl (flip deriv) p s

accept :: HasDecomp a c s => a -> [c] -> s
accept p s = atEps (derivs s p)

type Language a c s = (ClosedSemiring a, HasSingle a [c], HasDecomp a c s)