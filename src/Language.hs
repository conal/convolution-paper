-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Generalized "languages", which is mostly Semiring & friends

module Language where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Semi

infix 1 +->
class HasSingle a b x | x -> a b where
  (+->) :: a -> b -> x

single :: Semiring b => HasSingle a b x => a -> x
single a = a +-> one

value :: (HasSingle a b x, Monoid a)
      => b -> x
value b = mempty +-> b

-- Suitable?
instance (Eq a, Additive b) => HasSingle a b (a -> b) where
  (+->) = equal1

instance HasSingle a Bool [a] where
  a +-> b = if b then [a] else []

instance HasSingle a Bool (Set a) where
  a +-> b = if b then S.singleton a else S.empty

instance HasSingle a b (Map a b) where (+->) = M.singleton

oneBool :: Additive x => (a -> x) -> a -> Bool -> x
oneBool _ _ False = zero
oneBool f a True  = f a

equal1 :: (Eq a, Additive b) => a -> b -> a -> b
equal1 a b a' = if a == a' then b else zero

equal :: (Eq a, Semiring b) => a -> a -> b
equal a = equal1 a one

class Indexable p k v | p -> k v where
  (!) :: p -> k -> v

instance Indexable (k -> v) k v where
  f ! k = f k

instance (Ord k, Additive v) => Indexable (Map k v) k v where
  m ! k = M.findWithDefault zero k m

-- TODO: rename "a" to "x" for Decomposable and maybe some other classes.

-- | Derivative of a language w.r.t a string
derivs :: (Decomposable b h a, Indexable (h a) c a) => a -> [c] -> a
derivs = foldl ((!) . deriv)

accept :: (Decomposable b h a, Indexable (h a) c a) => a -> [c] -> b
accept p w = atEps (derivs p w)

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
