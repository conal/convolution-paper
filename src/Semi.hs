{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Commutative monoids, semirings, and semimodules

module Semi where

import Prelude hiding (sum,product)

-- import Control.Applicative (liftA2)
import GHC.Natural (Natural)
import Data.Functor.Identity (Identity(..))
import GHC.Exts (Coercible,coerce,Constraint)

import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Set (Set)
-- import qualified Data.Set as S

import Misc
import Constrained

#include "GenInstances.inc"

{--------------------------------------------------------------------
    Classes
--------------------------------------------------------------------}

-- Inspired by Indexable from Data.Key in the keys library.
class Indexable h b where
  type Key h
  infixl 9 !
  (!) :: h b -> Key h -> b

instance Indexable ((->) a) b where
  type Key ((->) a) = a
  f ! k = f k

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

type Additive1     = Con1 Additive
type Semiring1     = Con1 Semiring
type StarSemiring1 = Con1 StarSemiring

type DetectableZero1 = Con1 DetectableZero
type DetectableOne1  = Con1 DetectableOne

{--------------------------------------------------------------------
    Singletons
--------------------------------------------------------------------}

class Indexable h b => HasSingle h b where
  infixr 2 +->
  (+->) :: Key h -> b -> h b

instance (Eq a, Additive b) => HasSingle ((->) a) b where
  a +-> b = \ a' -> if a == a' then b else zero

single :: (HasSingle h b, Semiring b) => Key h -> h b
single a = a +-> one

value :: (HasSingle h b, Monoid (Key h)) => b -> h b
value b = mempty +-> b

-- instance HasSingle a Bool [a] where
--   a +-> b = if b then [a] else []

-- instance HasSingle Set where
--   a +-> b = if b then S.singleton a else S.empty

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
-- ApplMono(Set)
-- etc

instance (Ord a, Additive b) => Additive (Map a b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

-- NullZero((->*) a)

instance (Ord a, Additive b) => DetectableZero (Map a b) where isZero = M.null

-- FunctorSemimodule(Map a)

instance Semiring b => LeftSemimodule b (Map a b) where scale b = fmap (b <.>)

instance (Ord a, Monoid a, Semiring b) => Semiring (Map a b) where
  one = mempty +-> one
  p <.> q = sum [u <> v +-> p!u <.> q!v | u <- M.keys p, v <- M.keys q]

instance (Ord a, Additive b) => Indexable (Map a) b where
  type Key (Map a) = a
  m ! a = M.findWithDefault zero a m

instance (Ord a, Additive b) => HasSingle (Map a) b where (+->) = M.singleton

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
