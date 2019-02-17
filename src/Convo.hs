
{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Abandoned experiment

module Convo where

-- import Control.Applicative (liftA2)

import Data.Functor.Identity (Identity(..))
import GHC.Exts (Coercible)

import Data.Set (Set)
import Semi hiding ((:<:))

infix 1 :<:
pattern (:<:) :: Decomposable b h x => b -> h x -> x
pattern b :<: as <- (decomp -> (b,as)) where b :<: as = b <: as

{--------------------------------------------------------------------
    Convolution-style semiring
--------------------------------------------------------------------}

type AF f = (Functor f, Applicative f)

-- type CoercibleF t = forall a b. Coercible a b => Coercible (t a) (t b)

class    (forall u v. Coercible u v => Coercible (t u) (t v)) => CoercibleFC t
instance (forall u v. Coercible u v => Coercible (t u) (t v)) => CoercibleFC t

newtype Convo z = C z
  deriving (Show, Additive, DetectableZero, LeftSemimodule b, HasSingle a b)

-- When I try deriving Decomposable b h:
-- 
--  • Couldn't match representation of type ‘h z’
--                             with that of ‘h (Convo z)’
--      arising from the coercion of the method ‘<:’
--        from type ‘b -> h z -> z’ to type ‘b -> h (Convo z) -> Convo z’
--    NB: We cannot know what roles the parameters to ‘h’ have;
--      we must assume that the role is nominal
--  • When deriving the instance for (Decomposable b h (Convo z))
-- 
-- To do: check whether GHC has role constraints

unC :: Convo z -> z
unC (C z) = z

instance ( Decomposable b h z, LeftSemimodule b z, Additive z
         , DetectableZero b, DetectableOne b, DetectableZero (h (Convo z)) )
      => DetectableOne (Convo z) where
  isOne (a :<: dp) = isOne a && isZero dp


#if 0

deriving instance (forall a b. Coercible a b => Coercible (t a) (t b), Decomposable b h z) => Decomposable b h (Convo z)

-- • Couldn't match representation of type ‘t0 a’ with that of ‘t0 b1’
--   NB: We cannot know what roles the parameters to ‘t0’ have;
--     we must assume that the role is nominal
-- • In the ambiguity check for an instance declaration
--   To defer the ambiguity check to use sites, enable AllowAmbiguousTypes

-- deriving instance (Decomposable b h z, CoercibleFC h) => Decomposable b h (Convo z)

#else

instance Decomposable b h z => Decomposable b h (Convo z) where
  a <: dp = C (a <: fmap unC dp)
  decomp (C (decomp -> (a,dp))) = (a, fmap C dp)
  {-# INLINE (<:) #-}
  {-# INLINE decomp #-}
{-# COMPLETE (:<:) :: Convo #-}

#endif

-- deriving instance LeftSemimodule b z => LeftSemimodule b (Convo z)

instance ( DetectableZero b, Semiring b, Additive (h (Convo z))
         , Additive z, LeftSemimodule b z, Decomposable b h z )
      => Semiring (Convo z) where
  one = one <: zero
  (a :<: dp) <.> q = (a .> q) <+> (zero :<: fmap (<.> q) dp)

instance ( DetectableZero b, StarSemiring b, Additive (h (Convo z))
         , Additive z, LeftSemimodule b z, Decomposable b h z
         ) => StarSemiring (Convo z) where
  star (a :<: dp) = q where q = star a .> (one :<: fmap (<.> q) dp)

deriving instance Indexable k v z => Indexable k v (Convo z)

#if 0

-- | Convolvable functions
infixl 0 <--
type b <-- a = Convo (a -> b)

-- Hm. I can't give Functor, Applicative, Monad instances for Convo (a -> b)
-- since I need a to be the parameter.
-- I guess I could wrap another newtype:

(!^) :: Indexable a b z => z -> (b <-- a)
(!^) = C . (!)

#elif 1

infixl 0 <--
newtype b <-- a = F (a -> b) deriving (Additive, HasSingle a b, LeftSemimodule b, Indexable a b)

-- deriving instance Decomposable b h (a -> b) => Decomposable b h (b <-- a)

-- • Couldn't match representation of type ‘h (a -> b)’
--                            with that of ‘h (b <-- a)’
--     arising from a use of ‘GHC.Prim.coerce’
--   NB: We cannot know what roles the parameters to ‘h’ have;
--     we must assume that the role is nominal

-- Instead, manually derive special cases. Does GHC have role constraints?

deriving instance Semiring b => Decomposable b Identity (b <-- N)
deriving instance Decomposable b ((->) c) (b <-- [c])

(!^) :: Indexable a b z => z -> (b <-- a)
(!^) = F . (!)

#else

-- infixl 1 <--
-- newtype b <-- a = F { unF :: Convo (a -> b) }
--   deriving (Additive, LeftSemimodule b)

-- deriving instance Semiring b => LeftSemimodule b (b <-- a)

-- deriving instance
--   (DetectableZero b, Semiring b, Decomposable b h (a -> b), Applicative h)
--   => Semiring (b <-- a)

-- deriving instance
--   (DetectableZero b, StarSemiring b, Decomposable b h (a -> b), Applicative h)
--   => StarSemiring (b <-- a)

-- instance (Decomposable b h (a -> b)) => Decomposable b h (b <-- a) where
--   s <: dp = F (s :<: fmap unF dp)
--   decomp (F (s :<: dp)) = (s, fmap F dp)
--   -- decomp (F (s :<: (fmap F -> dp))) = (s, dp)

-- See how it goes

#endif

-- | Convolvable finite maps
type M' b a = Convo (a ->* b)

-- | Convolvable finite sets
type S' a = Convo (Set a)
