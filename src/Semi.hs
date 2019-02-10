-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Commutative monoids, semirings, and semimodules

module Semi where

-- import Control.Applicative (liftA2)
import GHC.Natural (Natural)
import Data.Functor.Identity (Identity(..))

import Data.Set (Set)
import Data.Map (Map)

import qualified Data.Set as S
import qualified Data.Map as M

import Misc ((:*))
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

class (Semiring s, Additive b) => Semimodule s b | b -> s where
  scale :: s -> b -> b
  -- default scale :: (Semiring b, s ~ b) => s -> b -> b  -- experimental
  -- scale = (<.>)
  default scale :: (Semiring s, Functor f, b ~ f s) => s -> b -> b  -- experimental
  scale s = fmap (s <.>)
  {-# INLINE scale #-}

-- TODO: Add the Semiring superclass, and remove redundant constraints
-- elsewhere. Search for occurrences of Semimodule.

-- | 'scale' optimized for zero scalar
(.>) :: (Additive b, Semimodule s b, DetectableZero s) => s -> b -> b
s .> b | isZero s  = zero
       | otherwise = s `scale` b
{-# INLINE (.>) #-}

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

instance (Ord a, Additive b) => Additive (Map a b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

NullZero(Map a)

FunctorSemimodule(Map a)

-- Do I want Semiring (Map a b)? If so, should it agree with a -> b. Oops! We'd
-- need one to map all domain values to one. I could do it with a total map, but
-- I think things then get complicated with different defaults.

#if 0

deriving instance Additive b       => Additive (Identity b)
deriving instance DetectableZero b => DetectableZero (Identity b)
deriving instance DetectableOne b  => DetectableOne (Identity b)
deriving instance Semimodule s b   => Semimodule s (Identity b)
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

{--------------------------------------------------------------------
    Indexing with zero default
--------------------------------------------------------------------}

class Indexable k v p | p -> k v where
  (!) :: p -> k -> v

instance Indexable k v (k -> v) where
  f ! k = f k

instance (Ord k, Additive v) => Indexable k v (Map k v) where
  m ! k = M.findWithDefault zero k m

{--------------------------------------------------------------------
    Decomposition (move elsewhere?)
--------------------------------------------------------------------}

class Decomposable b h x | x -> h b where
  infix 1 <:
  (<:)  :: b -> h x -> x
  decomp  :: x -> b :* h x
  atEps :: x -> b
  deriv :: x -> h x
  atEps = fst . decomp
  deriv = snd . decomp
  decomp x = (atEps x, deriv x)
  {-# MINIMAL (<:), ((deriv , atEps) | decomp) #-}

infix 1 :<:
pattern (:<:) :: Decomposable b h x => b -> h x -> x
pattern b :<: as <- (decomp -> (b,as)) where b :<: as = b <: as

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
    Convolution-style semiring
--------------------------------------------------------------------}

newtype Convo z = C z deriving (Show, Additive, DetectableZero)

unC :: Convo z -> z
unC (C z) = z

instance ( Decomposable b h z, Semimodule b z, Functor h, Additive z
         , DetectableZero b, DetectableOne b, DetectableZero (h (Convo z)) )
      => DetectableOne (Convo z) where
  isOne (a :<: dp) = isOne a && isZero dp

instance (Functor h, Decomposable b h z) => Decomposable b h (Convo z) where
  a <: dp = C (a <: fmap unC dp)
  decomp (C (decomp -> (a,dp))) = (a, fmap C dp)

{-# COMPLETE (:<:) :: Convo #-}

deriving instance Semimodule b z => Semimodule b (Convo z)

instance ( DetectableZero b, Semiring b, Functor h, Additive (h (Convo z))
         , Additive z, Semimodule b z, Decomposable b h z )
      => Semiring (Convo z) where
  one = one <: zero
  (a :<: dp) <.> q = (a .> q) <+> (zero :<: fmap (<.> q) dp)

instance ( DetectableZero b, StarSemiring b, Functor h, Additive (h (Convo z))
         , Additive z, Semimodule b z, Decomposable b h z
         ) => StarSemiring (Convo z) where
  star (a :<: dp) = q where q = star a .> (one :<: fmap (<.> q) dp)

deriving instance Indexable k v z => Indexable k v (Convo z)

#if 1

-- | Convolvable functions
infixl 1 <--
type b <-- a = Convo (a -> b)

-- Hm. I can't give Functor, Applicative, Monad instances for Convo (a -> b)
-- since I need a to be the parameter.
-- I guess I could wrap another newtype:

#else

infixl 1 <--
newtype b <-- a = F { unF :: Convo (a -> b) } deriving (Additive)

deriving instance Semiring b => Semimodule b (b <-- a)

deriving instance
  (DetectableZero b, Semiring b, Decomposable b h (a -> b), Applicative h)
  => Semiring (b <-- a)

deriving instance
  (DetectableZero b, StarSemiring b, Decomposable b h (a -> b), Applicative h)
  => StarSemiring (b <-- a)

instance (Decomposable b h (a -> b), Functor h) => Decomposable b h (b <-- a) where
  s <: dp = F (s :<: fmap unF dp)
  decomp (F (s :<: dp)) = (s, fmap F dp)
  -- decomp (F (s :<: (fmap F -> dp))) = (s, dp)

-- See how it goes

#endif

-- | Convolvable finite maps
type M' b a = Convo (Map a b)

-- | Convolvable finite sets
type S' a = Convo (Set a)
