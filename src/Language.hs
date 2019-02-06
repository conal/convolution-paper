{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Generalized "languages", which is mostly Semiring & friends

module Language where

import GHC.Natural (Natural)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Functor.Identity (Identity(..))

-- import Data.TotalMap (TMap)
-- import qualified Data.TotalMap as T

-- SINGLE controlled by package.yaml

-- import Data.Semiring

import Misc (Stream(..))
import Semi

#ifdef SINGLE

class HasSingle x a | x -> a where
  single :: a -> x

-- I'll probably want to swap arguments in HasSingle.

infix 1 +->
(+->) :: (Semiring x, Semimodule s x, HasSingle x a, DetectableZero s)
      => a -> s -> x
a +-> s = s .> single a

value :: (Semimodule s x, HasSingle x a, DetectableZero s, Monoid a, Semiring x)
      => s -> x
value b = mempty +-> b

-- -- Suitable?
-- instance (Semiring s, Eq a) => HasSingle (a -> s) a s where
--   a +-> s = \ a' -> if a == a' then s else zero

instance HasSingle [a] a where single a = [a]

instance HasSingle (Set a) a where single a = S.singleton a

#else

class HasSingle x a s | x -> a s where
  infix 1 +->
  (+->) :: a -> s -> x

single :: (HasSingle x a s, Semiring s) => a -> x
single a = a +-> one

value :: (HasSingle x a s, Monoid a) => s -> x
value b = mempty +-> b

instance (Semiring s, Eq a) => HasSingle (a -> s) a s where
  a +-> s = \ a' -> if a == a' then s else zero

instance HasSingle [a] a Bool where
  a +-> s = if s then [a] else []

instance HasSingle (Set a) a Bool where
  a +-> s = if s then S.singleton a else S.empty

#endif

#ifdef SINGLE
type HS x c s = (Semimodule s x, DetectableZero s, HasSingle x [c])
#else
type HS x c s = HasSingle x [c] s
#endif

oneBool :: Semiring x => (a -> x) -> a -> Bool -> x
oneBool _ _ False = zero
oneBool f a True  = f a

equal :: (Eq a, Semiring s) => a -> a -> s
-- equal a a' = fromBool (a == a')

equal a a' = if a == a' then one else zero

class Indexable p k v | p -> k v where
  (!) :: p -> k -> v

instance Indexable (k -> v) k v where
  f ! k = f k

instance Indexable (Stream b) N b where
  (b :# bs) ! n = if n == 0 then b else bs ! (n-1)

-- instance Indexable (Stream b) N b where
--   (b :# _)  ! 0 = b
--   (_ :# bs) ! n = bs ! (n-1)

-- instance Indexable (Stream b) N b where
--   (b :# _)  ! Sum 0 = b
--   (_ :# bs) ! Sum n = bs ! Sum (n-1)

instance (Ord k, Semiring v) => Indexable (Map k v) k v where
  m ! k = M.findWithDefault zero k m

-- | Derivative of a language w.r.t a string
derivs :: (Decomposable s h a, Indexable (h a) c a) => a -> [c] -> a
derivs = foldl ((!) . deriv)

accept :: (Decomposable s h a, Indexable (h a) c a) => a -> [c] -> s
accept p s = atEps (derivs p s)

-- type Language a c s = (StarSemiring a, HasSingle a [c], Decomposable a c s)

-- instance (Ord k, Monoid k, Semiring v) => HasSingle (TMap k v) v where
--   single v = T.insert mempty v zero

-- instance Decomposable (TMap k v) (Map k v) v where
--   e <: d  = 

{--------------------------------------------------------------------
    Invertible monoids
--------------------------------------------------------------------}

class Monoid t => Splittable t where
  -- Whether equal to 'mempty'
  isEmpty :: t -> Bool
  -- | The inverse of 'mappend'
  splits :: t -> [(t,t)]

instance Splittable [a] where
  isEmpty = null
  splits []     = [([],[])]
  splits (a:as) = ([],a:as) : [((a:l),r) | (l,r) <- splits as]

-- Equivalently,

--   splits as@(a:as') = ([],as) : map (first (a:)) (splits as')

--   splits' as = ([],as) : go as
--    where
--      go []       = []
--      go (a:as')  = [((a:l),r) | (l,r) <- splits' as']

{--------------------------------------------------------------------
    Sum and product
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

type N = Sum Natural

-- instance Splittable N where
--   isEmpty (Sum n) = n == 0
--   splits (Sum n) = [(Sum i, Sum (n-i)) | i <- [0 .. n]]

instance Splittable N where
  isEmpty n = n == 0
  splits n = [(i, n-i) | i <- [0 .. n]]

-- >>> splits (4 :: N)
-- [(Sum 0,Sum 4),(Sum 1,Sum 3),(Sum 2,Sum 2),(Sum 3,Sum 1),(Sum 4,Sum 0)]

newtype Product a = Product a deriving (Eq,Show)

getProduct :: Product a -> a
getProduct (Product a) = a

instance Semiring a => Semigroup (Product a) where
  Product a <> Product b = Product (a <.> b)

instance Semiring a => Monoid (Product a) where
  mempty = Product one

product :: (Foldable f, Semiring a) => f a -> a
product = getProduct . foldMap Product

{--------------------------------------------------------------------
    Temporary hack
--------------------------------------------------------------------}

allVals :: [c]
allVals = error "allVals not defined"
