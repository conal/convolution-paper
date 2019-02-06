{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}

-- | Commutative monoids, semirings, and semimodules

module Semi where

import Control.Applicative (liftA2)
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
  -- default scale :: (Semiring b, s ~ b) => s -> b -> b  -- experimental
  -- scale = (<.>)

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
-- instance Semimodule (t) (t)

-- Do I really want these Semimodule instances?

Nums(Integer)
Nums(Natural)
Nums(Int)
Nums(Float)
Nums(Double)
-- etc

-- Additive, Semimodule, Semimodule from Applicative
#define Appls(f) \
instance Additive zz => Additive ((f) zz) where \
  { (<+>) = liftA2 (<+>) ; zero = pure zero } ; \
instance Semiring zz => Semiring ((f) zz) where \
  { (<.>) = liftA2 (<.>) ; one = pure one } ; \
instance Semiring zz => Semimodule zz ((f) zz) where \
  scale s = fmap (s <.>) ;


-- instance Semimodule s b => Semimodule s ((qq) b) where \
--   scale s = fmap (scale s) ;

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

instance (Ord a, Additive b) => DetectableZero (M.Map a b) where isZero = M.null

instance Semiring b => Semimodule b (M.Map a b) where scale s = fmap (s <.>)

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

infix 1 :<:
pattern (:<:) :: Decomposable s h a => s -> h a -> a
pattern s :<: as <- (decomp -> (s,as)) where s :<: as = s <: as

{--------------------------------------------------------------------
    Some convolution-style instances
--------------------------------------------------------------------}

newtype Stream' b = S (Stream b) deriving Additive

deriving instance Semiring b => Semimodule b (Stream' b)

#if 1

instance Decomposable b Identity (Stream b) where
  b <: Identity bs = b :# bs
  decomp (b :# bs) = (b, Identity bs)
{-# COMPLETE (:<:) :: Stream #-}

instance Decomposable b Identity (Stream' b) where
  b <: Identity (S bs) = S (b :# bs)
  decomp (S (b :# bs)) = (b , Identity (S bs))
{-# COMPLETE (:<:) :: Stream' #-}
-- https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms/CompleteSigs

#else

instance Decomposable b Identity (Stream b) where
  b <: Identity bs = b :# bs
  decomp (b :# bs) = (b, Identity bs)
{-# COMPLETE (:<:) :: Stream #-}

deriving instance Decomposable b Identity (Stream' b)
{-# COMPLETE (:<:) :: Stream' #-}
-- https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms/CompleteSigs

#endif

-- I don't think I'll use Decomposable on Stream b, so I guess I prefer to skip
-- it. On the other hand, I wonder about giving a general Semiring for wrapped
-- decomposable semirings.

instance (DetectableZero b, Semiring b) => Semiring (Stream' b) where
  one = one <: zero
  (u :<: us') <.> vs = (u .> vs) <+> (zero :<: fmap (<.> vs) us')


newtype Map' a b = M (M.Map a b) deriving Additive

deriving instance Semiring b => Semimodule b (Map' a b)

-- deriving instance Decomposable b Identity (Map' a b)

-- {-# COMPLETE (:<:) :: Map' a b #-}

-- instance (DetectableZero b, Semiring b) => Semiring (Stream' b) where
--   one = one <: zero
--   (u :<: us') <.> vs = (u .> vs) <+> (zero :<: fmap (<.> vs) us')

newtype Convo f b = C (f b) deriving (Show, Additive, DetectableZero)

unC :: Convo f b -> f b
unC (C z) = z

instance (Functor h, Decomposable b h (f b)) => Decomposable b h (Convo f b) where
  b <: zs = C (b :<: fmap unC zs)
  decomp (C (decomp -> (b,zs))) = (b, fmap C zs)

  -- decomp (C (b :<: zs)) = (b, fmap C zs)  -- "Pattern match(es) are non-exhaustive"

-- deriving instance Decomposable b h (f b) => Decomposable b h (Convo f b)

-- --     • Couldn't match representation of type ‘h (f b)’
-- --                                with that of ‘h (Convo f b)’
-- --         arising from a use of ‘GHC.Prim.coerce’
-- --       NB: We cannot know what roles the parameters to ‘h’ have;
-- --         we must assume that the role is nominal

{-# COMPLETE (:<:) :: Convo #-}
-- https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms/CompleteSigs

-- Semiring, Semimodule

-- deriving instance Additive (f b) => Additive (Convo f b) -- or in type decl

deriving instance Semimodule b (f b) => Semimodule b (Convo f b)

instance ( DetectableZero b, Semiring b, Applicative h
         , Additive (f b), Semimodule b (f b), Decomposable b h (f b) )
      => Semiring (Convo f b) where
  one = one <: pure zero
  (u :<: us') <.> vs = (u .> vs) <+> (zero :<: fmap (<.> vs) us')
