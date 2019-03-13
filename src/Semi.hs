{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -Wno-orphans #-}

-- | Commutative monoids, semirings, and semimodules

module Semi where

import Prelude hiding (sum,product,(^))

import Control.Applicative (liftA2)
import Control.Arrow (first)
import GHC.Natural (Natural)
import Data.Functor.Identity (Identity(..))
import Data.Maybe (fromMaybe,isNothing)
import GHC.Exts (Coercible,coerce,Constraint)
import Control.DeepSeq (NFData)
import GHC.TypeLits (KnownNat)

import Data.Map (Map)
import qualified Data.Map as M
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.Set (Set)
import qualified Data.Set as S
import Data.MemoTrie

import Data.Finite (Finite)
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as V

import Misc
-- import Constrained

#include "GenInstances.inc"

{--------------------------------------------------------------------
    Classes
--------------------------------------------------------------------}

-- Keyed functors. Useful for memoization in RegExp and maybe elsewhere.
type family Key (h :: * -> *) :: *

-- Taken from Data.Key
class Functor f => Keyed f where
  mapWithKey :: (Key f -> a -> b) -> f a -> f b

-- Inspired by Indexable from Data.Key in the keys library.
class Indexable a b x | x -> a b where
  infixl 9 !
  (!) :: x -> a -> b

-- | Enumerate non-zero values
class Indexable a b x => Listable a b x where toList :: x -> [(a,b)]

-- TODO: rename toList to "nonZeros" or some such. Introduce early in the paper,
-- and use for representations like Map.

-- TODO: Laws: (!) must be natural; h must presere additivity, and !)| is an
-- Additive homomorphism.

-- | Commutative monoid
class Additive b where
  zero :: b
  (<+>) :: b -> b -> b
  infixr 6 <+>

class {- Additive b => -} DetectableZero b where
  isZero :: b -> Bool

class Additive b => Semiring b where
  one :: b
  (<.>) :: b -> b -> b
  infixr 7 <.>

class {- Semiring b => -} DetectableOne b where
  isOne :: b -> Bool

class Semiring b => StarSemiring b  where
  star :: b -> b
  plus :: b -> b
  star x = one <+> plus x
  plus x = x <.> star x
  {-# INLINE star #-}
  {-# INLINE plus #-}

class {- (Semiring s, Additive b) => -} LeftSemimodule s b | b -> s where
  scale :: s -> b -> b
  -- default scale :: (Semiring b, s ~ b) => s -> b -> b  -- experimental
  -- scale = (<.>)
  default scale :: (Semiring s, Functor f, b ~ f s) => s -> b -> b  -- experimental
  scale s = fmap (s <.>)
  {-# INLINE scale #-}

-- TODO: Add the Semiring superclass, and remove redundant constraints
-- elsewhere. Search for occurrences of LeftSemimodule.

-- | 'scale' optimized for zero or one scalar
infixr 7 .>
(.>) :: (Additive b, LeftSemimodule s b, DetectableZero s, DetectableOne s) => s -> b -> b
s .> b | isZero s  = zero
       | isOne  s  = b
       | otherwise = s `scale` b
{-# INLINE (.>) #-}

#if 0
type Additive1     = Con1 Additive
type Semiring1     = Con1 Semiring
type StarSemiring1 = Con1 StarSemiring

type DetectableZero1 = Con1 DetectableZero
type DetectableOne1  = Con1 DetectableOne
#endif

{--------------------------------------------------------------------
    Singletons
--------------------------------------------------------------------}

class Indexable a b x => HasSingle a b x where
  infixr 2 +->, *->
  (+->) :: a -> b -> x
  (*->) :: Set a -> b -> x
  a +-> b = S.singleton a *-> b
  default (*->) :: Additive x => Set a -> b -> x
  as *-> b = sum [a +-> b | a <- S.elems as]
  {-# MINIMAL (+->) | (*->) #-}

single :: (HasSingle a b x, Semiring b) => a -> x
single a = a +-> one

singles :: (HasSingle a b x, Semiring b) => Set a -> x
singles as = as *-> one

value :: (HasSingle a b x, Monoid a) => b -> x
value b = mempty +-> b

-- instance HasSingle a Bool [a] where
--   a +-> b = if b then [a] else []

-- instance HasSingle a Bool (Set a) where
--   a +-> b = if b then S.singleton a else S.empty

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

instance Additive Bool where
  zero = False
  (<+>) = (||)

instance DetectableZero Bool where isZero = not

instance Semiring Bool where
  one = True
  (<.>) = (&&)

instance DetectableOne Bool where isOne = id

instance StarSemiring Bool where star = const True

Nums(Integer)
Nums(Natural)
Nums(Int)
Nums(Float)
Nums(Double)
Nums(Rational)
-- etc

-- Experiment
instance StarSemiring (Natural) where
  star 0 = 1
  star _ = 987654321

-- ApplSemi((->) a)  -- use monoid semiring instead for now
-- etc

-- ApplMono([])
-- ApplMono(Set)
-- etc

type instance Key ((->) a) = a

instance Keyed ((->) a) where
  mapWithKey h f = \ a -> h a (f a)

instance Indexable a b (a -> b) where
  f ! k = f k

instance (Eq a, Additive b) => HasSingle a b (a -> b) where
  a +-> b = \ a' -> if a' == a then b else zero
  -- as *-> b = \ a' -> if a' `S.member` as then b else zero

instance Additive b => Additive (a -> b) where
  zero = pure zero
  (<+>) = liftA2 (<+>)
  -- zero = \ _ -> zero
  -- f <+> g  = \ a -> f a <+> g a

type D01 b = (DetectableZero b, DetectableOne b)

-- Short-circuiting <.>
infixr 7 <..>
(<..>) :: (Semiring b, DetectableZero b, DetectableOne b) => b -> b -> b
x <..> y | isZero x  = zero
         | isOne  x  = y
         | otherwise = x <.> y

instance (Monoid a, Eq a, Splittable a, Semiring b, D01 b) => Semiring (a -> b) where
  one = single mempty
  f <.> g = \ w -> sum [f u <..> g v | (u,v) <- splits w]

instance (Monoid a, Eq a, Splittable a, Semiring b, D01 b) => StarSemiring (a -> b)

instance (Ord a, Additive b) => Additive (Map a b) where
  zero = M.empty
  (<+>) = M.unionWith (<+>)

instance DetectableZero (Map a b) where isZero = M.null

#if 1
-- Experiment for Poly
instance DetectableOne (Map a b) where isOne = const False
#else
instance (Monoid a, Ord a, Additive b, DetectableOne b) => DetectableOne (Map a b) where
  isOne m = isOne (m!mempty) && isZero (M.delete mempty m)
#endif

-- FunctorSemimodule(Map a)

instance Semiring b => LeftSemimodule b (Map a b) where scale b = fmap (b <.>)

instance (Ord a, Monoid a, Semiring b) => Semiring (Map a b) where
  one = mempty +-> one
  p <.> q = sum [u <> v +-> p!u <.> q!v | u <- M.keys p, v <- M.keys q]

type instance Key (Map a) = a

instance Keyed (Map a) where mapWithKey = M.mapWithKey

instance (Ord a, Additive b) => Indexable a b (Map a b) where
  m ! a = M.findWithDefault zero a m

instance (Ord a, Additive b) => Listable a b (Map a b) where toList = M.toList

instance (Ord a, Additive b) => HasSingle a b (Map a b) where
  (+->) = M.singleton
  as *-> b = M.fromList [(a,b) | a <- S.elems as]

-- newtype Identity b = Identity b

type instance Key Identity = ()

instance Keyed Identity where mapWithKey h = fmap (h ())

instance Indexable () b (Identity b) where Identity a ! () = a

instance Listable () b (Identity b) where toList (Identity b) = [((),b)]

instance Additive b => HasSingle () b (Identity b) where
  -- us *-> b = if S.null us then zero else Identity b
  () +-> b = Identity b

deriving instance Additive b         => Additive (Identity b)
deriving instance DetectableZero b   => DetectableZero (Identity b)
deriving instance DetectableOne b    => DetectableOne (Identity b)
deriving instance LeftSemimodule s b => LeftSemimodule s (Identity b)
deriving instance Semiring b         => Semiring (Identity b)

-- newtype Id b = Id b deriving 
--  (Functor, Additive, DetectableZero, DetectableOne, LeftSemimodule s, Semiring)

type instance Key Maybe = ()

instance Keyed Maybe where mapWithKey h = fmap (h ())

instance Additive b => Indexable () b (Maybe b) where
  -- Nothing ! () = zero
  -- Just b  ! () = b
  mb ! () = fromMaybe zero mb

instance Additive b => Listable () b (Maybe b) where
  toList Nothing  = []
  toList (Just b) = [((),b)]

instance (DetectableZero b, Additive b) => HasSingle () b (Maybe b) where 
  () +-> b | isZero b  = Nothing
           | otherwise = Just b

instance Additive b => Additive (Maybe b) where
  zero = Nothing
  Nothing <+> v = v
  u <+> Nothing = u
  Just a <+> Just b = Just (a <+> b)

instance Semiring b => Semiring (Maybe b) where
  one = Just one
  Nothing <.> _ = zero
  _ <.> Nothing = zero
  Just a <.> Just b = Just (a <.> b)

instance DetectableZero (Maybe b) where
  isZero = isNothing
  -- We could also check Just b for b==0

instance DetectableOne b => DetectableOne (Maybe b) where
  isOne (Just b) | isOne b = True
  isOne _ = False

{--------------------------------------------------------------------
    Sum and product monoids
--------------------------------------------------------------------}

-- semiring-num defines 'add' and 'mul' via foldl', but I think I want foldr
-- instead.

newtype Sum a = Sum a deriving
  (Eq,Ord,NFData,Num,Real,Integral,Additive,DetectableZero,Semiring,DetectableOne,StarSemiring)

instance Show a => Show (Sum a) where
  showsPrec d (Sum a) = showsPrec d a

getSum :: Sum a -> a
getSum (Sum a) = a

instance Additive a => Semigroup (Sum a) where
  Sum a <> Sum b = Sum (a <+> b)

instance Additive a => Monoid (Sum a) where
  mempty = Sum zero

sum :: (Foldable f, Additive a) => f a -> a
sum = getSum . foldMap Sum

missing :: String -> String -> z
missing ty op = error ("No " ++ op ++ " method for " ++ ty)

noSum :: String -> z
noSum = missing "Sum" "(*)"

instance Enum a => Enum (Sum a) where
  toEnum = Sum . toEnum
  fromEnum = fromEnum . getSum

newtype Product a = Product a deriving (Eq,Show)

getProduct :: Product a -> a
getProduct (Product a) = a

instance Semiring a => Semigroup (Product a) where
  Product a <> Product b = Product (a <.> b)

instance Semiring a => Monoid (Product a) where
  mempty = Product one

product :: (Foldable f, Semiring a) => f a -> a
product = getProduct . foldMap Product

type N = Sum Natural

type Z = Sum Integer

-- Experiment
class HasPow x n b | x n -> b where
  infixr 8 ^#
  (^#) :: x -> n -> b

instance Semiring b => HasPow b N b where
  (^#) = (^)

instance (HasPow x n b, Additive x, Ord k, Additive n, Semiring b)
      => HasPow (Map k x) (Map k n) b where
  bs ^# ns = product [b ^# ns!i | (i,b) <- toList bs]


infixr 8 ^
(^), pow :: Semiring a => a -> N -> a
pow = (^)  -- useful for the paper
#if 0
a ^ n = product (replicate (fromIntegral n) a)
#else
-- Adapted from (^) in the GHC Prelude
x0 ^ y0 | y0 == 0   = one
        | otherwise = f x0 y0
    where -- f : x0 ^ y0 = x ^ y
          f x y | even y    = f (x <.> x) (y `quot` 2)
                | y == 1    = x
                | otherwise = g (x <.> x) (y `quot` 2) x         -- See Note [Half of y - 1]
          -- g : x0 ^ y0 = (x ^ y) <.> z
          g x y z | even y = g (x <.> x) (y `quot` 2) z
                  | y == 1 = x <.> z
                  | otherwise = g (x <.> x) (y `quot` 2) (x <.> z) -- See Note [Half of y - 1]

{- Note [Half of y - 1]
   ~~~~~~~~~~~~~~~~~~~~~
   Since y is guaranteed to be odd and positive here,
   half of y - 1 can be computed as y `quot` 2, optimising subtraction away.
-}

#endif

instance Splittable N where
  isEmpty n = n == 0
  splits n = [(i, n-i) | i <- [0 .. n]]

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

instance DetectableZero () where isZero () = True
instance DetectableOne  () where isOne  () = True

type instance Key [] = N

instance Keyed [] where mapWithKey h = zipWith h [0 ..]

instance Additive b => Indexable N b [b] where
  [] ! _ = zero
  (b : _ ) ! 0 = b
  (_ : bs) ! n = bs ! (n-1)

instance Additive b => Listable N b [b] where
  toList = zip [0 ..]

instance (Additive b, DetectableZero b) => HasSingle N b [b] where
  0 +-> b | isZero b = zero
          | otherwise = [b] 
  n +-> b = zero : (n-1 +-> b)
  -- TODO: efficient *->

-- Should I really be using up lists here instead of saving them?
-- Maybe wrap in a newtype

-- [a] as a denotation of a <-- N

-- See Cofree
instance Additive b => Additive [b] where
  zero = []
  [] <+> bs = bs
  as <+> [] = as
  (a : as) <+> (b : bs) = a <+> b : as <+> bs

instance (Semiring b, D01 b) => Semiring [b] where
  one = one : zero
  [] <.> _ = []  -- 0 * q == 0
  (a : dp) <.> q = a .> q <+> (zero : dp <.> q)

instance DetectableZero [b] where isZero = null

instance DetectableOne b => DetectableOne [b] where
  isOne [b] = isOne b
  isOne _ = False

instance Semiring b => LeftSemimodule b [b] where
  scale s = fmap (s <.>)

instance (Semiring b, Num b, DetectableZero b, DetectableOne b)
      => Num [b] where
  fromInteger = value . fromInteger
  negate = ((-1) .>)
  (+) = (<+>)
  (*) = (<.>)
  abs = fmap abs
  signum = fmap signum


-- TODO: generalize to other Integral or Enum types and add to Semi
newtype CharMap b = CharMap (IntMap b) deriving Functor

type instance Key CharMap = Char

instance Keyed CharMap where
  mapWithKey h (CharMap m) = CharMap (IntMap.mapWithKey (h . toEnum) m)

instance Additive b => Indexable Char b (CharMap b) where
  CharMap m ! a = IntMap.findWithDefault zero (fromEnum a) m

instance Additive b => Listable Char b (CharMap b) where
  toList (CharMap m) = first toEnum <$> IntMap.toList m

instance Additive b => HasSingle Char b (CharMap b) where
  a +-> b = CharMap (IntMap.singleton (fromEnum a) b)
  -- TODO: efficient *->

instance Additive b => Additive (CharMap b) where
  zero = CharMap IntMap.empty
  CharMap u <+> CharMap v = CharMap (IntMap.unionWith (<+>) u v)

instance Additive b => DetectableZero (CharMap b) where isZero (CharMap m) = IntMap.null m

type instance Key ((:->:) a) = a

instance HasTrie a => Indexable a b (a :->: b) where
  (!) = untrie

instance (HasTrie a, Eq a, Additive b) => HasSingle a b (a :->: b) where
  a +-> b = trie (a +-> b)
  -- TODO: efficient *->

instance (HasTrie a, Additive b) => Additive (a :->: b) where
  zero = trie zero
  u <+> v = trie (untrie u <+> untrie v)

-- False negatives are okay. Only used for optimization
instance (HasTrie a, Additive b) => DetectableZero (a :->: b) where isZero _ = False
-- instance Additive b => DetectableOne  (a :->: b) where isOne  _ = False


{--------------------------------------------------------------------
    Vectors
--------------------------------------------------------------------}

-- instance Splittable (Finite n) where
--   splits n = 

type Fin n = Sum (Finite n)

-- Maybe Monoid won't cut it here, since Finite n isn't properly additive.

type instance Key (Vector n) = Fin n

instance Indexable (Fin n) b (Vector n b) where
  v ! Sum i = v `V.index` i

instance (KnownNat n, DetectableZero b) => Listable (Fin n) b (Vector n b) where
  toList v = filter (not . isZero . snd) ([0 ..] `zip` V.toList v)

instance (KnownNat n, Additive b) => HasSingle (Fin n) b (Vector n b) where
  Sum i +-> b = V.generate (\ j -> if j == i then b else zero)
  -- TODO: efficient *->

instance (KnownNat n, Additive b) => Additive (Vector n b) where
  zero = pure zero
  (<+>) = liftA2 (<+>)

instance DetectableZero b => DetectableZero (Vector n b) where
  isZero = all isZero

-- instance (KnownNat n, Semiring b) => Semiring (Vector n b) where
--   one = 0 +-> one

-- instance DetectableOne b => DetectableOne (Vector n b) where
--   isOne = 
