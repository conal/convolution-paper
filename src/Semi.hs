{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Commutative monoids, semirings, and semimodules

module Semi where

-- import Control.Applicative (liftA2)
import GHC.Natural (Natural)
import Data.Functor.Identity (Identity(..))
import GHC.Exts (Coercible,coerce,Constraint)

import Data.Set (Set)
import Data.Map (Map)

import qualified Data.Set as S
import qualified Data.Map as M

import Misc ((:*),Con1,Con2)
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

-- Suitable?
instance (Eq a, Additive b) => HasSingle a b (a -> b) where
  -- (+->) = equal'
  a +-> b = \ a' -> if a == a' then b else zero

instance HasSingle a Bool [a] where
  a +-> b = if b then [a] else []

instance HasSingle a Bool (Set a) where
  a +-> b = if b then S.singleton a else S.empty

infixr 0 ->*
type a ->* b = Map a b

instance HasSingle a b (a ->* b) where (+->) = M.singleton

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

instance (Ord a, Additive b) => Additive (a ->* b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

-- NullZero(Map a)

instance (Ord a, Additive b) => DetectableZero (a ->* b) where isZero = M.null

FunctorSemimodule(Map a)

-- Do I want Semiring (a ->* b)? If so, should it agree with a -> b. Oops! We'd
-- need one to map all domain values to one. I could do it with a total map, but
-- I think things then get complicated with different defaults.

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

{--------------------------------------------------------------------
    Decomposition (move elsewhere?)
--------------------------------------------------------------------}

type CoercibleF = Con2 Coercible

class (Functor h, CoercibleF h) => Decomposable b h x | x -> h b where
  infix 1 <:
  (<:)  :: b -> h x -> x
  decomp  :: x -> b :* h x
  atEps :: x -> b
  deriv :: x -> h x
  atEps = fst . decomp
  deriv = snd . decomp
  decomp x = (atEps x, deriv x)
  {-# MINIMAL (<:), ((deriv , atEps) | decomp) #-}

instance Semiring b => Decomposable b Identity (N -> b) where
  b <: Identity f = \ i -> if i == 0 then b else f (i - 1)
  atEps f = f 0
  deriv f = Identity (f . (1 +))

instance Decomposable b ((->) c) ([c] -> b) where
  (b <: _) [] = b
  (_ <: h) (c:cs) = h c cs
  decomp f = (f [], \ c cs -> f (c : cs))
 -- {-# COMPLETE (:<:) :: [c] -> b #-} -- won't parse

-- I probably don't need and can't benefit from these COMPLETE pragmas, since
-- I'm using the general Convo type. For the same reason, I don't think I'm
-- benefiting from the polymorphic :<: pattern anyway, since it's only used for
-- Convo.
-- 
-- TODO: specialize the (:<:) pattern's type to Convo. Perhaps wait to see
-- whether Convo really handles everything.

instance Ord c => Decomposable Bool (Map c) (Set [c]) where
  e <: d  = fromBool e <+> S.unions [ S.map (c:) css | (c,css) <- M.toList d ]
  atEps p = [] `S.member` p
  deriv p = M.fromListWith (<+>) [(c, S.singleton cs) | c:cs <- S.toList p]

-- The unique 'Semiring' homomorphism from 'Bool'.
fromBool :: Semiring s => Bool -> s
fromBool False = zero
fromBool True  = one

-- TODO: Map, N -> b

{--------------------------------------------------------------------
    Another experiment: Decomposables
--------------------------------------------------------------------}

newtype Decomp x = D x deriving (Show)

deriving instance Decomposable b h x => Decomposable b h (Decomp x)

deriving instance (Decomposable b h x, HasSingle a b x) => HasSingle a b (Decomp x)

infix 1 :<:
pattern (:<:) :: Decomposable b h x => b -> h (Decomp x) -> Decomp x
pattern b :<: as <- (decomp -> (b,as)) where b :<: as = b <: as
{-# COMPLETE (:<:) :: Decomp #-}

type AdditiveF  = Con1 Additive

instance (Decomposable b h x, AdditiveF h, Additive b) => Additive (Decomp x) where
  zero = zero :<: zero
  (a :<: dp) <+> (b :<: dq) = a <+> b  :<:  dp <+> dq

deriving instance (Decomposable b h x, AdditiveF h, Additive b, DetectableZero x)
               => DetectableZero (Decomp x)

instance (Decomposable b h x, Semiring b) => LeftSemimodule b (Decomp x) where
  s `scale` (b :<: dp) = s <.> b :<: fmap (s `scale`) dp

instance (Decomposable b h x, AdditiveF h, Semiring b, DetectableZero b)
      => Semiring (Decomp x) where
  one = one :<: zero
  (a :<: dp) <.> q = a .> q <+> (zero :<: fmap (<.> q) dp)

instance (Decomposable b h x, AdditiveF h, StarSemiring b, DetectableZero b)
      => StarSemiring (Decomp x) where
  star (a :<: dp) = q where q = star a .> (one :<: fmap (<.> q) dp)
