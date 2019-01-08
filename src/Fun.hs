{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Languages as functions to semirings

module Fun where

import Prelude hiding (sum,product)

import Misc
import Semiring

{--------------------------------------------------------------------
    Abstract interfaces
--------------------------------------------------------------------}

class HasDecomp a c s | a -> c s where
  hasEps :: a -> s
  deriv :: c -> a -> a

-- TODO: rename hasEps

-- delta :: (Semiring a, HasDecomp a c s) => a -> a
-- delta a | hasEps a  = one
--         | otherwise = zero

-- | Derivative of a language w.r.t a string
derivs :: HasDecomp a c s => [c] -> a -> a
derivs s p = foldl (flip deriv) p s

accept :: HasDecomp a c s => a -> [c] -> s
accept p s = hasEps (derivs s p)

type Language a c s = (ClosedSemiring a, HasSingle a [c], HasDecomp a c s)

{--------------------------------------------------------------------
    Generalized predicates
--------------------------------------------------------------------}

-- The unique 'Semiring' homomorphism from 'Bool'.
boolVal :: Semiring s => Bool -> s
boolVal False = zero
boolVal True  = one

newtype FunTo b a = FunTo (a -> b)

instance Semiring s => Semiring (FunTo s [c]) where
  zero = FunTo (const zero)
  one = FunTo (boolVal . null)
  FunTo f <+> FunTo g = FunTo (\ x -> f x <+> g x)
  FunTo f <.> FunTo g = FunTo (\ x -> sum [ f u <.> g v | (u,v) <- splits x ] )

instance Semiring s => ClosedSemiring (FunTo s [c])

instance (Semiring s, Eq b) => HasSingle (FunTo s b) b where
  single x = FunTo (boolVal . (== x))

instance HasDecomp (FunTo s [c]) c s where
  hasEps (FunTo f) = f []
  deriv c (FunTo f) = FunTo (f . (c :))

