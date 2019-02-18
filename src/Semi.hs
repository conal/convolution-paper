{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Commutative monoids, semirings, and semimodules

module Semi where

import Prelude hiding (sum,product)

-- import Control.Applicative (liftA2)
import GHC.Natural (Natural)
import Data.Functor.Identity (Identity(..))
import GHC.Exts (Coercible,coerce,Constraint)

import Data.Set (Set)
import Data.Map (Map)

import qualified Data.Set as S
import qualified Data.Map as M

import Misc
import Constrained

#include "GenInstances.inc"

{--------------------------------------------------------------------
    Classes
--------------------------------------------------------------------}

-- | Commutative monoid
class Additive b where
  zero :: b
  (<+>) :: b -> b -> b
  infixl 6 <+>

class Additive b => DetectableZero b where
  isZero :: b -> Bool

class Additive b => Semiring b where
  one :: b
  (<.>) :: b -> b -> b
  infixl 7 <.>

class Semiring b => DetectableOne b where
  isOne :: b -> Bool

class Semiring b => StarSemiring b  where
  star :: b -> b
  plus :: b -> b
  star x = one <+> plus x
  plus x = x <.> star x
  {-# INLINE star #-}
  {-# INLINE plus #-}

class {- (Semiring s, Additive b) => -} LeftSemimodule s b | b -> s where
  scale :: s -> b -> b
  -- default scale :: (Semiring b, s ~ b) => s -> b -> b  -- experimental
  -- scale = (<.>)
  default scale :: (Semiring s, Functor f, b ~ f s) => s -> b -> b  -- experimental
  scale s = fmap (s <.>)
  {-# INLINE scale #-}

-- TODO: Add the Semiring superclass, and remove redundant constraints
-- elsewhere. Search for occurrences of LeftSemimodule.

-- | 'scale' optimized for zero scalar
(.>) :: (Additive b, LeftSemimodule s b, DetectableZero s) => s -> b -> b
s .> b | isZero s  = zero
       | otherwise = s `scale` b
{-# INLINE (.>) #-}

type Additive1 = Con1 Additive
type Semiring1 = Con1 Semiring

{--------------------------------------------------------------------
    Singletons
--------------------------------------------------------------------}

class HasSingle a b x | x -> a b where
  infixr 2 +->
  (+->) :: a -> b -> x

single :: (HasSingle a b x, Semiring b) => a -> x
single a = a +-> one

value :: (HasSingle a b x, Monoid a) => b -> x
value b = mempty +-> b

instance (Eq a, Additive b) => HasSingle a b (a -> b) where
  a +-> b = \ a' -> if a == a' then b else zero

instance HasSingle a Bool [a] where
  a +-> b = if b then [a] else []

instance HasSingle a Bool (Set a) where
  a +-> b = if b then S.singleton a else S.empty

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance Additive Bool where
  zero = False
  (<+>) = (||)

instance DetectableZero Bool where isZero = not

instance Semiring Bool where
  one = True
  (<.>) = (&&)

instance DetectableOne Bool where isOne = id

instance StarSemiring Bool where star = const True

Nums(Integer)
Nums(Natural)
Nums(Int)
Nums(Float)
Nums(Double)
-- etc

ApplSemi((->) a)
-- etc

ApplMono([])
ApplMono(Set)
-- etc

infixr 0 ->*
type (->*) = Map

instance HasSingle a b (a ->* b) where (+->) = M.singleton

instance (Ord a, Additive b) => Additive (a ->* b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

-- NullZero(Map a)

instance (Ord a, Additive b) => DetectableZero (a ->* b) where isZero = M.null

FunctorSemimodule(Map a)

instance (Ord a, Monoid a, Semiring b) => Semiring (a ->* b) where
  one = mempty +-> one
  p <.> q = sum [u <> v +-> p!u <.> q!v | u <- M.keys p, v <- M.keys q]

#if 0

deriving instance Additive b       => Additive (Identity b)
deriving instance DetectableZero b => DetectableZero (Identity b)
deriving instance DetectableOne b  => DetectableOne (Identity b)
deriving instance LeftSemimodule s b   => LeftSemimodule s (Identity b)
deriving instance Semiring b       => Semiring (Identity b)

#endif

{--------------------------------------------------------------------
    Sum and product monoids
--------------------------------------------------------------------}

-- semiring-num defines 'add' and 'mul' via foldl', but I think I want foldr
-- instead.

newtype Sum a = Sum a deriving (Eq,Show)

getSum :: Sum a -> a
getSum (Sum a) = a

instance Semiring a => Semigroup (Sum a) where
  Sum a <> Sum b = Sum (a <+> b)

instance Semiring a => Monoid (Sum a) where
  mempty = Sum zero

sum :: (Foldable f, Semiring a) => f a -> a
sum = getSum . foldMap Sum

-- Handy for eliding the Sum Natural vs Natural distinction in the paper.
instance Num a => Num (Sum a) where
  fromInteger = Sum . fromInteger
  Sum a + Sum b = Sum (a + b)
  Sum a - Sum b = Sum (a - b)
  Sum a * Sum b = Sum (a * b)
  negate (Sum a) = Sum (negate a)
  abs    (Sum a) = Sum (abs a)
  signum (Sum a) = Sum (signum a)

missing :: String -> String -> z
missing ty op = error ("No " ++ op ++ " method for " ++ ty)

noSum :: String -> z
noSum = missing "Sum" "(*)"

instance Enum a => Enum (Sum a) where
  toEnum = Sum . toEnum
  fromEnum = fromEnum . getSum

newtype Product a = Product a deriving (Eq,Show)

getProduct :: Product a -> a
getProduct (Product a) = a

instance Semiring a => Semigroup (Product a) where
  Product a <> Product b = Product (a <.> b)

instance Semiring a => Monoid (Product a) where
  mempty = Product one

product :: (Foldable f, Semiring a) => f a -> a
product = getProduct . foldMap Product

type N = Sum Natural

type Z = Sum Integer

instance Splittable N where
  isEmpty n = n == 0
  splits n = [(i, n-i) | i <- [0 .. n]]

#if 1

{--------------------------------------------------------------------
    Indexable functors
--------------------------------------------------------------------}

-- Inspired by Indexable from Data.Key in the keys library.

class Indexable h where
  type Key h
  infixl 9 !
  (!) :: Additive a => h a -> Key h -> a

instance Indexable ((->) a) where
  type Key ((->) a) = a
  f ! k = f k

instance Ord a => Indexable (Map a) where
  type Key (Map a) = a
  m ! a = M.findWithDefault zero a m

#else

{--------------------------------------------------------------------
    Indexing with zero default
--------------------------------------------------------------------}

class Indexable k v p | p -> k v where
  infixl 9 !
  (!) :: p -> k -> v

instance Indexable k v (k -> v) where
  f ! k = f k

instance (Ord k, Additive v) => Indexable k v (Map k v) where
  m ! k = M.findWithDefault zero k m

-- The unique 'Semiring' homomorphism from 'Bool'.
fromBool :: Semiring s => Bool -> s
fromBool False = zero
fromBool True  = one

-- TODO: Map, N -> b

-- | Derivative of a language w.r.t a string
derivs :: (Decomposable b h x, Indexable c x (h x)) => x -> [c] -> x
-- derivs = foldl ((!) . deriv)
derivs = foldl (\ p c -> deriv p ! c)

accept :: (Decomposable b h x, Indexable c x (h x)) => x -> [c] -> b
-- accept x w = atEps (derivs x w)
accept x cs = atEps (foldl (\ p c -> deriv p ! c) x cs)

#endif
