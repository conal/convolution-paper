{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Semirings

module Semiring where

import qualified Data.Set as S
import qualified Data.Map as M

class Semiring a where
  infixl 7 <.>
  infixl 6 <+>
  zero, one     :: a
  (<+>), (<.>)  :: a -> a -> a

class Semiring a => StarSemiring a where
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

instance StarSemiring Bool where
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

sum', product' :: (Foldable f, Semiring a) => f a -> a
sum' = foldr (<+>) zero
product' = foldr (<.>) one

instance Monoid a => Semiring [a] where
  zero = []
  one = [mempty]
  p <+> q = p ++ q
  p <.> q = [u <> v | u <- p, v <- q]

instance Monoid a => StarSemiring [a] -- default

instance (Monoid a, Ord a) => Semiring (S.Set a) where
  zero = S.empty
  one = S.singleton mempty
  p <+> q = p `S.union` q
  p <.> q = S.fromList
             [u <> v | u <- S.toList p, v <- S.toList q]

-- instance (Monoid a, Ord a) => StarSemiring (S.Set a) -- default

instance (Monoid a, Ord a, Semiring b) => Semiring (M.Map a b) where
  zero = M.empty
  one = M.singleton mempty one
  p <+> q = M.unionWith (<+>) p q
  p <.> q = M.fromListWith (<+>)
              [(u <> v, s <.> t) | (u,s) <- M.toList p, (v,t) <- M.toList q]

{--------------------------------------------------------------------
    Language operations. Move elsewhere.
--------------------------------------------------------------------}

class HasDecomp a c s | a -> c s where
  atEps :: a -> s
  deriv :: a -> c -> a

-- | Derivative of a language w.r.t a string
derivs :: HasDecomp a c s => a -> [c] -> a
derivs = foldl deriv

accept :: HasDecomp a c s => a -> [c] -> s
accept p s = atEps (derivs p s)

type Language a c s = (StarSemiring a, HasSingle a [c], HasDecomp a c s)


instance HasSingle [a] a where single a = [a]

instance Eq c => HasDecomp [[c]] c Bool where
  atEps p = [] `elem` p
  deriv p c = [cs | c' : cs <- p, c' == c]


instance HasSingle (S.Set a) a where single = S.singleton

instance Ord c => HasDecomp (S.Set [c]) c Bool where
  atEps p = [] `S.member` p
  deriv p c = S.fromList [cs | c' : cs <- S.toList p, c' == c]

instance Semiring s => HasSingle (M.Map a s) a where
  single a = M.singleton a one

instance (Ord c, Semiring s) => HasDecomp (M.Map [c] s) c s where
  atEps p = M.findWithDefault zero [] p
  deriv p c = M.fromList [(cs,s) | (c':cs,s) <- M.toList p, c' == c]

