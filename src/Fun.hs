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
  atEps :: a -> s
  deriv :: c -> a -> a

-- | Derivative of a language w.r.t a string
derivs :: HasDecomp a c s => [c] -> a -> a
derivs s p = foldl (flip deriv) p s

accept :: HasDecomp a c s => a -> [c] -> s
accept p s = atEps (derivs s p)

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
  atEps (FunTo f) = f []
  deriv c (FunTo f) = FunTo (f . (c :))

{--------------------------------------------------------------------
    Regular expressions
--------------------------------------------------------------------}

infixl 6 :<+>
infixl 7 :<.>

-- | Regular expression
data RegExp c a =
    Char c
  | Value a
  | RegExp c a :<+> RegExp c a
  | RegExp c a :<.> RegExp c a
  | Closure (RegExp c a)
 deriving (Show,Eq)

instance Semiring a => Semiring (RegExp c a) where
  zero  = Value zero
  one   = Value one
  (<+>) = (:<+>)
  (<.>) = (:<.>)

instance Semiring a => ClosedSemiring (RegExp c a) where
  closure = Closure

instance (Functor f, Foldable f, Semiring a) => HasSingle (RegExp c a) (f c) where
  single = product . fmap Char

instance (Eq c, ClosedSemiring a) => HasDecomp (RegExp c a) c a where
  atEps (Char _)    = zero
  atEps (Value a)   = a
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Closure p) = closure (atEps p)
  
  deriv c (Char c') | c == c'   = one
                    | otherwise = zero
  deriv _ (Value _)             = zero
  deriv c (p :<+> q)            = deriv c p <+> deriv c q
  deriv c (p :<.> q)            = Value (atEps p) <.> deriv c q <+> deriv c p <.> q
  deriv c (Closure p)           = deriv c (p <.> Closure p) -- since deriv c one = zero
                                  -- deriv c (one <+> p <.> Closure p)

-- | Interpret a regular expression
regexp :: (ClosedSemiring a, HasSingle a [c]) => RegExp c a -> a
regexp (Char c)      = single [c]
regexp (Value a)     = a
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Closure u)   = closure (regexp u)
