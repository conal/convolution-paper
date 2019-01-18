{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Semirings

module Semiring where

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

class Semiring a where
  infixl 7 <.>
  infixl 6 <+>
  zero, one     :: a
  (<+>), (<.>)  :: a -> a -> a

class Semiring a => StarSemiring a where
  closure :: a -> a
  closure p = q where q = one <+> p <.> q

class HasSingle a w | a -> w where
  single :: w -> a

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance Semiring b => Semiring (a -> b) where
  zero = const zero
  one  = const one
  f <+> g = \ a -> f a <+> g a
  f <.> g = \ a -> f a <.> g a

instance StarSemiring b => StarSemiring (a -> b) where
  closure f = \ a -> closure (f a)

instance HasSingle b w => HasSingle (a -> b) w where
  single w = const (single w)

(.>) :: Semiring s => s -> (a -> s) -> (a -> s)
s .> f  = (s <.>) . f

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

-- Variants

sum', product' :: (Foldable f, Semiring a) => f a -> a
sum' = foldr (<+>) zero
product' = foldr (<.>) one

class Semiring a => DetectableZero a  where
  isZero :: a -> Bool

instance DetectableZero Bool where isZero = not

instance Monoid a => Semiring [a] where
  zero = []
  one = [mempty]
  p <+> q = p ++ q
  p <.> q = [u <> v | u <- p, v <- q]

instance Monoid a => StarSemiring [a] -- default

instance (Monoid a, Ord a) => Semiring (Set a) where
  zero = S.empty
  one = S.singleton mempty
  p <+> q = p `S.union` q
  p <.> q = S.fromList
             [u <> v | u <- S.toList p, v <- S.toList q]

-- instance (Monoid a, Ord a) => StarSemiring (Set a) -- default

{--------------------------------------------------------------------
    Language operations. Move elsewhere.
--------------------------------------------------------------------}

-- The unique 'Semiring' homomorphism from 'Bool'.
boolVal :: Semiring s => Bool -> s
boolVal False = zero
boolVal True  = one

class Indexable p k v | p -> k v where
  (!) :: p -> k -> v

instance Indexable (k -> v) k v where
  f ! k = f k

instance (Ord k, Semiring v) => Indexable (Map k v) k v where
  m ! c = M.findWithDefault zero c m

type SR a = Semiring a
-- type SR a = (() ~ ())

class SR a => Decomposable a h s | a -> h s where
  infix 1 <:
  (<:)  :: s -> h a -> a
  atEps :: a -> s
  deriv :: a -> h a

-- TODO: Do I really want h to depend on a? Could we have more than one h per a?

-- | Derivative of a language w.r.t a string
derivs :: (Decomposable a h s, Indexable (h a) c a) => a -> [c] -> a
derivs = foldl ((!) . deriv)

accept :: (Decomposable a h s, Indexable (h a) c a) => a -> [c] -> s
accept p s = atEps (derivs p s)

-- type Language a c s = (StarSemiring a, HasSingle a [c], Decomposable a c s)

instance SR b => Decomposable ([c] -> b) ((->) c) b where
  (b <: _) []     = b
  (_ <: h) (c:cs) = h c cs
  atEps f = f []
  -- deriv f c = f . (c :)
  deriv f = \ c cs -> f (c : cs)

instance (Eq a, SR b) => HasSingle (a -> b) a where
  single a = boolVal . (== a)
  -- single a a' = boolVal (a' == a)

instance HasSingle [a] a where single a = [a]

-- instance Eq c => Decomposable [[c]] ((->) c) Bool where
--   atEps p = [] `elem` p
--   deriv p c = [cs | c' : cs <- p, c' == c]


instance HasSingle (Set a) a where single = S.singleton

instance Ord c => Decomposable (Set [c]) (Map c) Bool where
  e <: d = boolVal e <+> S.unions [ S.map (c:) css | (c,css) <- M.toList d ]
  atEps p = [] `S.member` p
  deriv p = M.fromListWith (<+>) [(c, S.singleton cs) | c:cs <- S.toList p]

{--------------------------------------------------------------------
    Temporary hack
--------------------------------------------------------------------}

allVals :: [c]
allVals = error "allVals not defined"
