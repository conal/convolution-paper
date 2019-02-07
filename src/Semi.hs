{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
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
  infixl 6 <+>
  (<+>) :: b -> b -> b
  zero :: b

class Additive b => DetectableZero b where
  isZero :: b -> Bool

class Additive b => Semiring b where
  infixl 7 <.>
  (<.>) :: b -> b -> b
  one :: b

class Semiring b => StarSemiring b  where
  star :: b -> b
  plus :: b -> b
  star x = one <+> plus x
  plus x = x <.> star x
  {-# INLINE star #-}
  {-# INLINE plus #-}

class Semimodule s b | b -> s where
  scale :: s -> b -> b
  -- default scale :: (Semiring b, s ~ b) => s -> b -> b  -- experimental
  -- scale = (<.>)
  default scale :: (Semiring s, Functor f, b ~ f s) => s -> b -> b  -- experimental
  scale s = fmap (s <.>)
  {-# INLINE scale #-}

-- | 'scale' optimized for zero scalar
(.>) :: (Semiring b, Semimodule s b, DetectableZero s) => s -> b -> b
s .> b | isZero s  = zero
       | otherwise = s `scale` b
{-# INLINE (.>) #-}

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance Additive Bool where
  (<+>) = (||)
  zero = False

instance DetectableZero Bool where isZero = not

instance Semiring Bool where
  (<.>) = (&&)
  one = True

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

-- Do I want Semiring (Map a b)? If so, should it agree with a -> b.
-- Maybe build it with Convo, but then I'm restricting the domain.

-- Even for lists, I suspect I should have one version that acts like functions
-- from N and another like convolution.

#if 0

deriving instance Additive b       => Additive (Identity b)
deriving instance DetectableZero b => DetectableZero (Identity b)
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
    Decomposition (move elsewhere?)
--------------------------------------------------------------------}

class Decomposable s h a | a -> h s where
  infix 1 <:
  (<:)  :: s -> h a -> a
  decomp  :: a -> s :* h a
  atEps :: a -> s
  deriv :: a -> h a
  atEps = fst . decomp
  deriv = snd . decomp
  decomp a = (atEps a, deriv a)
  {-# MINIMAL (<:), ((deriv , atEps) | decomp) #-}

infix 1 :<:
pattern (:<:) :: Decomposable s h a => s -> h a -> a
pattern s :<: as <- (decomp -> (s,as)) where s :<: as = s <: as

instance Semiring b => Decomposable b Identity (N -> b) where
  b <: Identity f = \ i -> if i == 0 then b else f (i - 1)
  atEps f = f 0
  deriv f = Identity (f . (1 +))

instance Semiring b => Decomposable b ((->) c) ([c] -> b) where
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
    Some convolution-style instances
--------------------------------------------------------------------}

#if 0

newtype Stream' b = S (Stream b) deriving Additive

FunctorSemimodule(Stream')
-- deriving instance Semiring b => Semimodule b (Stream' b)

instance Decomposable b Identity (Stream' b) where
  b <: Identity (S bs) = S (b :# bs)
  decomp (S (b :# bs)) = (b , Identity (S bs))
{-# COMPLETE (:<:) :: Stream' #-}
-- https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms/CompleteSigs

instance (DetectableZero b, Semiring b) => Semiring (Stream' b) where
  one = one <: Identity zero
  (u :<: us') <.> vs = (u .> vs) <+> (zero :<: fmap (<.> vs) us')


newtype Map' a b = M (Map a b) deriving Additive

FunctorSemimodule(Map' a)
-- deriving instance Semiring b => Semimodule b (Map' a b)

-- deriving instance Decomposable b Identity (Map' a b)

-- {-# COMPLETE (:<:) :: Map' a b #-}

-- instance (DetectableZero b, Semiring b) => Semiring (Stream' b) where
--   one = one <: zero
--   (u :<: us') <.> vs = (u .> vs) <+> (zero :<: fmap (<.> vs) us')

#endif

newtype Convo z = C z deriving (Show, Additive, DetectableZero)

unC :: Convo z -> z
unC (C z) = z

instance (Functor h, Decomposable b h z) => Decomposable b h (Convo z) where
  b <: zs = C (b <: fmap unC zs)
  decomp (C (decomp -> (b,zs))) = (b, fmap C zs)

{-# COMPLETE (:<:) :: Convo #-}

deriving instance Semimodule b z => Semimodule b (Convo z)

instance ( DetectableZero b, Semiring b, Applicative h
         , Additive z, Semimodule b z, Decomposable b h z )
      => Semiring (Convo z) where
  one = one <: pure zero
  (a :<: dp) <.> q = (a .> q) <+> (zero :<: fmap (<.> q) dp)

instance ( DetectableZero b, StarSemiring b, Applicative h
         , Additive z, Semimodule b z, Decomposable b h z
         ) => StarSemiring (Convo z) where
  star (a :<: dp) = q where q = star a .> (one :<: fmap (<.> q) dp)

#if 0

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
  -- decomp (F (s :<: dp)) = (s, fmap F dp)
  decomp (F (s :<: (fmap F -> dp))) = (s, dp)

-- See how it goes

#endif

type M' b a = Convo (Map a b)

