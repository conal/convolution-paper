{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Code for the paper.

module Code where

import Data.Monoid ((<>))
import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import Data.List (stripPrefix)
import Data.Map (Map)
import qualified Data.Map as Map

{--------------------------------------------------------------------
    Abstract interface
--------------------------------------------------------------------}

class Semiring a where
  infixl 7 <.>
  infixl 6 <+>
  zero, one     :: a
  (<+>), (<.>)  :: a -> a -> a

class Semiring a => ClosedSemiring a where
  closure :: a -> a
  closure p = q where q = one <+> p <.> q

class HasSingle a x where
  single :: x -> a

instance Semiring Integer where
  zero = 0
  one = 1
  (<+>) = (+)
  (<.>) = (*)

{--------------------------------------------------------------------
    Sets of strings (or other monoidal values)
--------------------------------------------------------------------}

#if 0

instance Semiring (Set a) where
  zero = emptyset
  one = single mempty
  p + q = set (s | s `elem` p || s `elem` q)
  p <.> q = set (p <> q | u `elem` p && v `elem` q)

instance ClosedSemiring (Set a) where
  closure p = bigunion (n >= 0) (p^n)

instance HasSingle (Set a) a where
  single a = set a

#endif

newtype Pred s = Pred (s -> Bool)

#if 0

setPred :: Set a -> Pred a
setPred as = Pred (\ a -> a `elem` as)

predSet :: Pred a -> Set a
predSet (Pred f) = set (a | f a)

#endif

{--------------------------------------------------------------------
    Predicates
--------------------------------------------------------------------}

instance Semiring (Pred [c]) where
  zero = Pred (const False)
  one = Pred null
  Pred f <+> Pred g = Pred (\ x -> f x || g x)
  Pred f <.> Pred g = Pred (\ x -> or [ f u && g v | (u,v) <- splits x ] )

instance ClosedSemiring (Pred [c])

instance Eq s => HasSingle (Pred s) s where
  single s = Pred (== s)

-- All ways of splitting a given list (inverting |(<>)|).
splits :: [a] -> [([a],[a])]
splits []       = [([],[])]
splits (a:as')  = ([],a:as') : [((a:l),r) | (l,r) <- splits as']

-- splits as@(a:as') = ([],as) : map (first (a:)) (splits as')

{--------------------------------------------------------------------
    Classic list-of-successes
--------------------------------------------------------------------}

-- Match a prefix of given string and yield corresponding suffixes for all
-- successful matches.
newtype Resid c = Resid ([c] -> [[c]])

residPred :: Resid c -> Pred [c]
residPred (Resid f) = Pred (any null . f)

#if 1

instance Semiring (Resid c) where
  zero = Resid (fail "no match")
  one = Resid return
  Resid f <+> Resid g = Resid (liftA2 (<>) f g)
  Resid f <.> Resid g = Resid (f >=> g)

#else

instance Semiring (Resid c) where
  zero = Resid (const [])
  one = Resid (\ s -> [s])
  Resid f <+> Resid g = Resid (\ s -> f s <> g s)
  Resid f <.> Resid g = Resid (\ s -> [s'' | s' <- f s, s'' <- g s'])

#endif

instance ClosedSemiring (Resid c)

instance Eq c => HasSingle (Resid c) [c] where
  single x = Resid (\ s -> case stripPrefix x s of
                             Just s' -> [s']
                             Nothing -> [])
                     

{--------------------------------------------------------------------
    String tries
--------------------------------------------------------------------}

data STrie c = STrie Bool (Map c (STrie c))

trieFun :: Ord c => STrie c -> ([c] -> Bool)
trieFun (STrie e _ ) [] = e
trieFun (STrie _ ts) (c:cs) =
  case Map.lookup c ts of
    Nothing -> False
    Just t  -> trieFun t cs

-- funSTrie :: ([c] -> Bool) -> STrieFun c
-- funSTrie f = STrieFun (f []) ...

-- How to construct the Map c?

triePred :: Ord c => STrie c -> Pred [c]
triePred = Pred . trieFun

-- predSTrie :: Ord c => Pred [c] -> STrie c


