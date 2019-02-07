{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Generalized "languages", which is mostly Semiring & friends

module Language where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Functor.Identity (Identity(..))

-- import Data.TotalMap (TMap)
-- import qualified Data.TotalMap as T

-- SINGLE controlled by package.yaml

-- import Data.Semiring

import Misc
import Semi

class HasSingle a x | x -> a where
  single :: a -> x

infix 1 +->
(+->) :: (Semiring x, Semimodule s x, HasSingle a x, DetectableZero s)
      => a -> s -> x
a +-> s = s .> single a

value :: (Semimodule s x, HasSingle a x, DetectableZero s, Monoid a, Semiring x)
      => s -> x
value b = mempty +-> b

-- Suitable?
instance (Eq a, Semiring b) => HasSingle a (a -> b) where
  single = equal

instance HasSingle a [a] where single a = [a]

instance HasSingle a (Set a) where single a = S.singleton a

type HS x c s = (Semimodule s x, DetectableZero s, HasSingle [c] x)

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

instance (Ord k, Semiring v) => Indexable (Map k v) k v where
  m ! k = M.findWithDefault zero k m

-- | Derivative of a language w.r.t a string
derivs :: (Decomposable s h a, Indexable (h a) c a) => a -> [c] -> a
derivs = foldl ((!) . deriv)

accept :: (Decomposable s h a, Indexable (h a) c a) => a -> [c] -> s
accept p s = atEps (derivs p s)

-- type Language a c s = (StarSemiring a, HasSingle [c] a, Decomposable a c s)

-- instance (Ord k, Monoid k, Semiring v) => HasSingle v (TMap k v) where
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

instance Splittable N where
  isEmpty n = n == 0
  splits n = [(i, n-i) | i <- [0 .. n]]

-- >>> splits (4 :: N)
-- [(Sum 0,Sum 4),(Sum 1,Sum 3),(Sum 2,Sum 2),(Sum 3,Sum 1),(Sum 4,Sum 0)]

{--------------------------------------------------------------------
    Temporary hack
--------------------------------------------------------------------}

allVals :: [c]
allVals = error "allVals not defined"
