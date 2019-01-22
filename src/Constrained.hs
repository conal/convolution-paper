
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some constrained classes

module Constrained where

import Control.Applicative (liftA2)
import Control.Monad (join)
import GHC.Generics
import GHC.Types (Constraint)
import Data.Set (Set)
import qualified Data.Set as S
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MS

import Data.Semiring

import Misc
import Set hiding (Trie)

type Ok2 f a b = (Ok f a, Ok f b)
type Ok3 f a b c = (Ok2 f a b, Ok f c)
type Ok4 f a b c d = (Ok2 f a b, Ok2 f c d)

class FunctorC f where
  type Ok f a :: Constraint
  type Ok f a = ()
  fmapC :: Ok2 f a b => (a -> b) -> f a -> f b
  default fmapC :: Functor f => (a -> b) -> f a -> f b
  fmapC = fmap

class FunctorC f => ApplicativeC f where
  pureC :: Ok f a => a -> f a
  default pureC :: Applicative f => a -> f a
  pureC = pure
  liftA2C :: Ok3 f a b c => (a -> b -> c) -> f a -> f b -> f c
  default liftA2C :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
  liftA2C = liftA2

infixl 1 >>==
class ApplicativeC f => MonadC f where
  joinC :: Ok f a => f (f a) -> f a
  default joinC :: Monad f => f (f a) -> f a
  joinC = join
  (>>==) :: Ok2 f a b => f a -> (a -> f b) -> f b
  default (>>==) :: Monad f => f a -> (a -> f b) -> f b
  (>>==) = (>>=)

bindViaJoin :: (MonadC f, Ok3 f a b (f b)) => f a -> (a -> f b) -> f b
bindViaJoin as f = joinC (fmapC f as)

joinViaBind :: (MonadC f, Ok2 f a (f a)) => f (f a) -> f a
joinViaBind q = q >>== id

class FunctorC f => MonoidalC f where
  unitC :: Ok f () => f ()
  crossC :: Ok2 f a b => f a -> f b -> f (a :* b)

pureViaUnit :: Ok2 f () a => MonoidalC f => a -> f a
pureViaUnit a = fmapC (const a) unitC

unitViaPure :: Ok f () => ApplicativeC f => f ()
unitViaPure = pureC ()

liftA2ViaCross :: (MonoidalC f, Ok4 f a b (a :* b) c) => (a -> b -> c) -> f a -> f b -> f c
liftA2ViaCross h as bs = fmapC (uncurry h) (as `crossC` bs)

crossViaLiftA2 :: (ApplicativeC f, Ok3 f a b (a :* b)) => f a -> f b -> f (a :* b)
crossViaLiftA2 = liftA2C (,)

instance FunctorC []
instance ApplicativeC []
instance MonadC []
-- etc

instance MonoidalC [] where
  unitC = unitViaPure
  crossC = crossViaLiftA2

instance FunctorC Set where
  type Ok Set a = Ord a
  fmapC = S.map

instance MonoidalC Set where
  unitC = unitViaPure
  crossC = S.cartesianProduct

instance ApplicativeC Set where
  pureC = S.singleton
  liftA2C = liftA2ViaCross

instance MonadC Set where
  joinC = S.unions . S.elems
  (>>==) = bindViaJoin

instance FunctorC MultiSet where
  type Ok MultiSet a = Ord a
  fmapC = MS.map

instance MonoidalC MultiSet where
  unitC = unitViaPure
  crossC = crossViaLiftA2
  -- as `crossC` bs =
  --   MS.fromOccurList
  --     [((a,b),m*n) | (a,m) <- MS.toOccurList as, (b,n) <- MS.toOccurList bs]

-- Maybe use the explicit crossC but with `fromDistinctAscOccurList`, since the
-- list is ordered and distinct.

instance ApplicativeC MultiSet where
  pureC = MS.singleton
  liftA2C h as bs =
    MS.fromOccurList
      [(h a b,m*n) | (a,m) <- MS.toOccurList as, (b,n) <- MS.toOccurList bs]
  -- liftA2C = liftA2ViaCross

instance MonadC MultiSet where
  joinC = MS.join
  (>>==) = bindViaJoin

-- newtype Pred s = Pred (s -> Bool)

-- Can we give a FunctorC instance for Pred? I guess we'd have to sum over the
-- preimage of the function being mapped.
