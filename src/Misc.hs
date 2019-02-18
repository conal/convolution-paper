-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Miscellany

module Misc where

infixl 6 :+

type (:*)  = (,)
type (:+)  = Either

type Unop a = a -> a

bool :: a -> a -> Bool -> a
bool t e b = if b then t else e

-- | Handy universal constraint alias
class    (forall u. con u => con (h u)) => Con1 con h
instance (forall u. con u => con (h u)) => Con1 con h

-- | Handy universal constraint alias
class    (forall u v. con u v => con (h u) (h v)) => Con2 con h
instance (forall u v. con u v => con (h u) (h v)) => Con2 con h


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
