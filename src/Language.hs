-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Generalized "languages", which is mostly Semiring & friends

module Language where

import Semi

oneBool :: Additive x => (a -> x) -> a -> Bool -> x
oneBool _ _ False = zero
oneBool f a True  = f a

equal' :: (Eq a, Additive b) => a -> b -> a -> b
equal' a b a' = if a == a' then b else zero

equal :: (Eq a, Semiring b) => a -> a -> b
equal a = equal' a one

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

-- allVals :: [c]
-- allVals = error "allVals not defined"
