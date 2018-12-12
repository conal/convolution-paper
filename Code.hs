{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Code for the paper.

module Code where

import Data.Monoid ((<>))
import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import Data.List (stripPrefix)
-- import Data.Map (Map)
-- import qualified Data.Map as Map
import GHC.Generics

import qualified Data.IntTrie as IT  -- data-inttrie

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

infixl 7 :*
infixl 6 :+

type (:*)  = (,)
type (:+)  = Either

type Unop a = a -> a

bool :: a -> a -> Bool -> a
bool t e b = if b then t else e

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

-- Equivalently
splits' :: [a] -> [([a],[a])]
splits' as = ([],as) : go as
 where
   go []       = []
   go (a:as')  = [((a:l),r) | (l,r) <- splits' as']

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
    Memoization via generalized tries
--------------------------------------------------------------------}

infixr 0 :->:

-- | Memo trie from k to v
type k :->: v = Trie k v

-- | Domain types with associated memo tries
class Functor (Trie k) => HasTrie k where
    type Trie k :: * -> *
    trie   :: (k  ->  v) -> (k :->: v)
    untrie :: (k :->: v) -> (k  ->  v)

-- | Indexing. Synonym for 'untrie'.
(!) :: HasTrie k => (k :->: v) -> k  ->  v
(!) = untrie

-- Identity trie. To do: make idTrie the method, and define trie via idTrie.
idTrie :: HasTrie k => k :->: k
idTrie = trie id

-- | Trie-based function memoizer
memo :: HasTrie k => Unop (k -> v)
memo = untrie . trie

-- | Memoize a binary function, on its first argument and then on its
-- second.  Take care to exploit any partial evaluation.
memo2 :: (HasTrie s,HasTrie t) => Unop (s -> t -> a)

-- | Memoize a ternary function on successive arguments.  Take care to
-- exploit any partial evaluation.
memo3 :: (HasTrie r,HasTrie s,HasTrie t) => Unop (r -> s -> t -> a)

-- | Lift a memoizer to work with one more argument.
mup :: HasTrie t => (b -> c) -> (t -> b) -> (t -> c)
mup mem f = memo (mem . f)

memo2 = mup memo
memo3 = mup memo2

instance HasTrie () where
  type Trie () = Par1
  trie f = Par1 (f ())
  untrie (Par1 v) = \ () -> v

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  type Trie (Either a b) = Trie a :*: Trie b
  trie   f           = trie (f . Left) :*: trie (f . Right)
  untrie (ta :*: tb) = untrie ta `either` untrie tb

instance (HasTrie a, HasTrie b) => HasTrie (a :* b) where
  type Trie (a :* b) = Trie a :.: Trie b
  trie   f = Comp1 (trie (trie . curry f))
  untrie (Comp1 tt) = uncurry (untrie (fmap untrie tt))

#define HasTrieIsomorph(Context,Type,IsoType,toIso,fromIso) \
instance Context => HasTrie (Type) where {\
  type Trie (Type) = Trie (IsoType); \
  trie f = trie (f . (fromIso)); \
  untrie t = untrie t . (toIso); \
}

--  enumerate = (result.fmap.first) (fromIso) enumerate;

-- HasTrieIsomorph( (), Bool, Either () ()
--                , bool (Right ()) (Left ())
--                , either (\ () -> False) (\ () -> True))

data Pair a = a :# a deriving (Functor,Foldable)

instance HasTrie Bool where
  type Trie Bool = Pair
  trie f = (f False :# f True)
  untrie (f :# t) c = if c then t else f

HasTrieIsomorph( (HasTrie a, HasTrie b, HasTrie c)
               , (a,b,c), ((a,b),c)
               , \ (a,b,c) -> ((a,b),c), \ ((a,b),c) -> (a,b,c))

HasTrieIsomorph( (HasTrie a, HasTrie b, HasTrie c, HasTrie d)
               , (a,b,c,d), ((a,b,c),d)
               , \ (a,b,c,d) -> ((a,b,c),d), \ ((a,b,c),d) -> (a,b,c,d))

#if 0

-- As well as the functor combinators themselves

HasTrieIsomorph( HasTrie x, Const x a, x, getConst, Const )

HasTrieIsomorph( HasTrie a, Id a, a, unId, Id )

HasTrieIsomorph( ( HasTrie f a, HasTrie (g a) )
               , (f :*: g) a, (f a,g a)
               , \ (fa :*: ga) -> (fa,ga), \ (fa,ga) -> (fa :*: ga) )

HasTrieIsomorph( (HasTrie (f a), HasTrie (g a))
               , (f :+: g) a, Either (f a) (g a)
               , eitherF Left Right, either InL InR )

HasTrieIsomorph( HasTrie (g (f a))
               , (g :. f) a, g (f a) , unComp1, Comp1 )

#endif


#define HasTrieIntegral(Type) \
instance HasTrie Type where { \
  type Trie Type = IT.IntTrie; \
  trie   = (<$> IT.identity); \
  untrie = IT.apply; \
}

HasTrieIntegral(Int)
HasTrieIntegral(Integer)

-- HasTrieIntegral(Char)  -- Oops. Needs Num

HasTrieIsomorph((),Char,Int,fromEnum,toEnum)

-- TODO: clean up the isomorphism stuff with a type class similar to Generic but
-- without functors. Use for default definitions of Trie, trie, and untrie.

#if 1

{--------------------------------------------------------------------
    String tries
--------------------------------------------------------------------}

data LTrie c a = LTrie a (c :->: LTrie c a)

deriving instance HasTrie c => Functor (LTrie c)

instance HasTrie c => HasTrie [c] where
  type Trie [c] = LTrie c
  trie f = LTrie (f []) (trie (\ c -> trie (f . (c :))))
  untrie (LTrie e ts) = list e (untrie . untrie ts)

-- Equivalently:
-- 
--   untrie (LTrie e _ ) [] = e
--   untrie (LTrie _ ts) (c:cs) = untrie (untrie ts c) cs
--
--   untrie (LTrie e ts) = list e (\ c cs -> untrie (untrie ts c) cs)

list :: b -> (a -> [a] -> b) -> [a] -> b
list b _ [] = b
list _ f (a:as) = f a as

ltriePred :: HasTrie c => LTrie c Bool -> Pred [c]
ltriePred = Pred . untrie

predLTrie :: HasTrie c => Pred [c] -> LTrie c Bool
predLTrie (Pred f) = trie f

#endif
                     
