{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}

-- | Commutative monoids, semirings, and semimodules

module Semi where

import Control.Applicative (liftA2)
-- import Control.Arrow (second)
import GHC.Natural (Natural)
import Data.Functor.Identity (Identity(..))

import qualified Data.Set as S
import qualified Data.Map as M

import Misc ((:*),Stream(..))

{--------------------------------------------------------------------
    Classes
--------------------------------------------------------------------}

-- | Commutative monoid
class Additive b where
  infixl 6 <+>
  (<+>) :: b -> b -> b
  zero :: b

class Additive b => DetectableZero b where isZero :: b -> Bool

class Additive b => Semiring b where
  infixl 7 <.>
  (<.>) :: b -> b -> b
  one :: b

class Semimodule s b | b -> s where
  scale :: s -> b -> b
  default scale :: (Semiring b, s ~ b) => s -> b -> b  -- experimental
  scale = (<.>)

-- | 'scale' optimized for zero scalar
(.>) :: (Semiring b, Semimodule s b, DetectableZero s) => s -> b -> b
s .> b | isZero s = zero
       | otherwise = s `scale` b

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

#define Nums(t) \
instance Additive (t) where { (<+>) = (+) ; zero = 0 } ; \
instance DetectableZero (t) where { isZero = (== 0)} ; \
instance Semiring (t) where { (<.>) = (*) ; one  = 1 } ; \
instance Semimodule (t) (t)

-- Do I really want these Semimodule instances?

Nums(Integer)
Nums(Natural)
Nums(Int)
Nums(Float)
Nums(Double)
-- etc

-- Additive, Semimodule, Semimodule from Applicative
#define Appls(qq) \
instance Additive b => Additive ((qq) b) where \
  { (<+>) = liftA2 (<+>) ; zero = pure zero } ; \
instance Semiring b => Semiring ((qq) b) where \
  { (<.>) = liftA2 (<.>) ; one = pure one } ; \
instance Semimodule s b => Semimodule s ((qq) b) where \
  scale s = fmap (scale s) ;

Appls((->) a)
Appls(Stream)
-- etc

-- Additive from Monoid
#define Mono(t) \
instance Monoid (t) => Additive (t) where { zero = mempty ; (<+>) = (<>) }

Mono([c])
Mono(S.Set a)
-- etc

instance (Ord a, Additive b) => Additive (M.Map a b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

deriving instance Additive b       => Additive (Identity b)
deriving instance DetectableZero b => DetectableZero (Identity b)
deriving instance Semimodule s b   => Semimodule s (Identity b)
deriving instance Semiring b       => Semiring (Identity b)

{--------------------------------------------------------------------
    Decomposition (elsewhere?)
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
  {-# MINIMAL (<:), (decomp | atEps , decomp) #-}

instance Decomposable b Identity (Stream b) where
  b <: Identity bs = b :# bs
  decomp (b :# bs) = (b , Identity bs)

infix 1 :<:
pattern (:<:) :: Decomposable s h a => s -> h a -> a
pattern s :<: as <- (decomp -> (s,as)) where s :<: as = s <: as

{--------------------------------------------------------------------
    Some convolution-style instances
--------------------------------------------------------------------}

newtype Stream' b = S (Stream b) deriving Additive

deriving instance Decomposable b Identity (Stream' b)
deriving instance Semimodule s b => Semimodule s (Stream' b)

-- instance Decomposable b Identity (Stream' b) where
--   b <: Identity (S bs) = S (b <: Identity bs)
--   decomp (S bs) = (second.fmap) S (decomp bs)

-- instance Semimodule s b => Semimodule s (Stream' b) where
--   s `scale` S bs = S (s `scale` bs)

-- instance (DetectableZero b, Semiring b) => Semiring (Stream' b) where
--   one = one <: zero
--   -- (u :<: Identity us') <.> vs = (u .> vs) <+> (zero :<: Identity (us' <.> vs))
--   (u :<: us') <.> vs = (u .> vs) -- <+> (zero :<: Identity (us' <.> vs))

-- Oops. u .> vs doesn't type-check.
-- I think I need to Semimodule b (Stream' b).
-- Probably other changes, too.

  
  -- one = S (one :# zero)
  -- S (u :# us') <.> vs = (u .> vs) <+> (zero :# us' <.> vs)
