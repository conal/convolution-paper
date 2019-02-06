{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Commutative monoids, semirings, and semimodules

module Semi where

import Control.Applicative (liftA2)
import GHC.Natural (Natural)

import qualified Data.Set as S
import qualified Data.Map as M

{--------------------------------------------------------------------
    Classes
--------------------------------------------------------------------}

-- | Commutative monoid
class Additive b where
  infixl 6 <+>
  (<+>) :: b -> b -> b
  zero :: b

class Additive b => DetectableZero b  where isZero :: b -> Bool

class Additive b => Semiring b where
  infixl 7 <.>
  (<.>) :: b -> b -> b
  one :: b

class Semimodule b s | b -> s where
  scale :: s -> b -> b
  default scale :: (Semiring b, s ~ b) => s -> b -> b  -- experimental
  scale = (<.>)

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance Additive Bool where
  (<+>) = (||)
  zero = False

instance Semiring Bool where
  (<.>) = (&&)
  one = True

#define Nums(t) \
instance Additive (t) where { (<+>) = (+) ; zero = 0 } ; \
instance Semiring (t) where { (<.>) = (*) ; one  = 1 } ; \
instance Semimodule (t) (t)

-- Do I really want these Semimodule instances?

Nums(Integer)
Nums(Natural)
Nums(Int)
Nums(Float)
Nums(Double)
-- etc

#if 1

#define Appls(qq) \
instance Additive b => Additive ((qq) b) where \
  { (<+>) = liftA2 (<+>) ; zero = pure zero } ; \
instance Semiring b => Semiring ((qq) b) where \
  { (<.>) = liftA2 (<.>) ; one = pure one } ; \
instance Semimodule b s => Semimodule ((qq) b) s where \
  scale s = fmap (scale s) ;

Appls((->) a)
-- etc

#elif 1

instance Additive b => Additive (a -> b) where
  (<+>) = liftA2 (<+>)
  zero = pure zero

instance Semiring b => Semiring (a -> b) where
  (<.>) = liftA2 (<.>)
  one = pure one

instance Semimodule b s => Semimodule (a -> b) s where
  scale s = fmap (scale s)

#else
instance Additive b => Additive (a -> b) where
  f <+> g = \ a -> f a <+> g a
  zero = const zero

instance Semiring b => Semiring (a -> b) where
  f <.> g = \ a -> f a <.> g a
  one = const one
#endif

#if 1

#define Mono(t) \
instance Monoid (t) => Additive (t) where { zero = mempty ; (<+>) = (<>) }

Mono([c])
Mono(S.Set a)
-- etc

#else

instance Additive [c] where
  zero = []
  (<+>) = (++)

instance Ord a => Additive (S.Set a) where
  zero = S.empty
  (<+>) = S.union

#endif

instance (Ord a, Additive b) => Additive (M.Map a b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)
