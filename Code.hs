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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Code for the paper.

module Code where

import Prelude hiding (sum,product)

import Data.Monoid (Monoid(..))
import Control.Arrow (second)
import Control.Applicative (liftA2)
import Control.Monad (join,(>=>))
import Data.List (stripPrefix)
import GHC.Generics
import GHC.Types (Constraint)
import Data.Maybe (maybeToList)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MS

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

class HasSingle a s where
  single :: s -> a

class HasDecomp a c | a -> c where
  hasEps :: a -> Bool
  deriv :: c -> a -> a

-- | Derivative of a language w.r.t a string
derivs :: HasDecomp a c => [c] -> a -> a
derivs s p = foldl (flip deriv) p s

type Language a c = (ClosedSemiring a, HasSingle a [c], HasDecomp a c)

instance Semiring Integer where
  zero = 0
  one = 1
  (<+>) = (+)
  (<.>) = (*)

instance Semiring Bool where
  zero = False
  one = True
  (<+>) = (||)
  (<.>) = (&&)

instance ClosedSemiring Bool where
  closure _ = one

newtype Sum a = Sum { getSum :: a }

instance Semiring a => Semigroup (Sum a) where
  Sum a <> Sum b = Sum (a <+> b)

instance Semiring a => Monoid (Sum a) where
  mempty = Sum zero

sum :: (Foldable f, Semiring a) => f a -> a
sum = getSum . foldMap Sum

newtype Product a = Product { getProduct :: a }

instance Semiring a => Semigroup (Product a) where
  Product a <> Product b = Product (a <.> b)

instance Semiring a => Monoid (Product a) where
  mempty = Product one

product :: (Foldable f, Semiring a) => f a -> a
product = getProduct . foldMap Product

{--------------------------------------------------------------------
    Sets of strings (or other monoidal values)
--------------------------------------------------------------------}

#if 0

instance Semiring (Set a) where
  zero = emptyset
  one = single mempty
  p + q = set (a | a `elem` p || a `elem` q)
  p <.> q = set (p <> q | u `elem` p && v `elem` q)

instance ClosedSemiring (Set a) where
  closure p = bigunion (n >= 0) (p^n)

instance HasSingle (Set a) a where
  single a = set a

instance Eq a => HasDecomp (Set a) a where
  hasEps p = [] `elem` p
  deriv c p = set (cs | c : cs `elem` p)

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

instance HasDecomp (Pred [c]) c where
  hasEps (Pred f) = f []
  deriv c (Pred f) = Pred (f . (c :))

{--------------------------------------------------------------------
    Classic list-of-successes
--------------------------------------------------------------------}

-- Match a prefix of given string and yield corresponding suffixes for all
-- successful matches.
newtype Resid s = Resid ([s] -> [[s]])

residPred :: Resid s -> Pred [s]
residPred (Resid f) = Pred (any null . f)

#if 1

instance Semiring (Resid s) where
  zero = Resid (fail "no match")
  one = Resid return
  Resid f <+> Resid g = Resid (liftA2 (<>) f g)
  Resid f <.> Resid g = Resid (f >=> g)

#else

instance Semiring (Resid s) where
  zero = Resid (const [])
  one = Resid (\ s -> [s])
  Resid f <+> Resid g = Resid (\ s -> f s <> g s)
  Resid f <.> Resid g = Resid (\ s -> [s'' | s' <- f s, s'' <- g s'])

#endif

instance ClosedSemiring (Resid s)

instance Eq s => HasSingle (Resid s) [s] where
  -- single x = Resid (\ s -> case stripPrefix x s of
  --                            Just s' -> [s']
  --                            Nothing -> [])
  single x = Resid (maybeToList . stripPrefix x)

instance HasDecomp (Resid s) s where
  hasEps (Resid f) = any null (f [])
  deriv c (Resid f) = Resid (f . (c :)) -- TODO: check

#if 0
            deriv      :: c -> a -> a
       flip deriv      :: a -> c -> a
foldl (flip deriv) a s :: a
#endif

accept :: HasDecomp a c => a -> [c] -> Bool
accept p s = hasEps (derivs s p)

{--------------------------------------------------------------------
    Regular expressions
--------------------------------------------------------------------}

infixl 6 :<+>
infixl 7 :<.>

-- | Regular expression
data RegExp c =
    Char c
  | Zero
  | One
  | RegExp c :<+> RegExp c
  | RegExp c :<.> RegExp c
  | Closure (RegExp c)
 deriving (Show,Eq)

-- TODO: instantiate Show manually, using the method names instead of constructors.

-- TODO: consider returning to Char instead of Single. Otherwise, we have
-- redundant representations. On the other hand, regular expressions over
-- general monoids is a pretty cool idea.

-- -- Optimize RegExp methods via semiring laws
-- #define OptimizeRegexp

#ifdef OptimizeRegexp

type OkSym = Eq

instance Eq c => Semiring (RegExp c) where
  zero  = Zero
  one   = One
  Zero <+> b = b
  a <+> Zero = a
  a :<.> c <+> b :<.> d | a == b = a <.> (c <+> d)
  a :<.> c <+> b :<.> d | c == d = (a <+> b) <.> c
  a <+> b = a :<+> b
  Zero <.> _ = Zero
  _ <.> Zero = Zero
  One <.> b = b
  a <.> One = a
  a <.> b = a :<.> b

instance Eq c => ClosedSemiring (RegExp c) where
  closure Zero = One
  closure e    = Closure e

#else

type OkSym c = (() :: Constraint)

instance Semiring (RegExp c) where
  zero  = Zero
  one   = One
  (<+>) = (:<+>)
  (<.>) = (:<.>)

instance ClosedSemiring (RegExp c) where
  closure = Closure

#endif

#if 0

instance OkSym c => HasSingle (RegExp c) [c] where
  -- single = foldr (\ c e -> Char c <.> e) One
  single = product . fmap Char

#else
-- Or from an arbitrary foldable
instance (Functor f, Foldable f, OkSym c) => HasSingle (RegExp c) (f c) where
  single = product . fmap Char
  -- single = foldr (\ c e -> Char c <.> e) One

-- We could even define balanced folding of sums and products via two monoid
-- wrappers.

#endif

delta :: (Semiring a, HasDecomp a c) => a -> a
delta a | hasEps a  = one
        | otherwise = zero

instance Eq c => HasDecomp (RegExp c) c where
  hasEps (Char _)    = zero
  hasEps Zero        = zero
  hasEps One         = one
  hasEps (p :<+> q)  = hasEps p <+> hasEps q
  hasEps (p :<.> q)  = hasEps p <.> hasEps q
  hasEps (Closure p) = closure (hasEps p)
  
  deriv c (Char c') | c == c'   = one
                    | otherwise = zero
  deriv _ Zero                  = zero
  deriv _ One                   = zero
  deriv c (p :<+> q)            = deriv c p <+> deriv c q
#if 1
  -- This one definition works fine if we have OptimizeRegexp
  deriv c (p :<.> q)            = delta p <.> deriv c q <+> deriv c p <.> q
#else
  deriv c (p :<.> q) | hasEps p  = deriv c q <+> deriv c p <.> q
                     | otherwise = deriv c p <.> q
#endif
  deriv c (Closure p)           = deriv c (p <.> Closure p) -- since deriv c one = zero
                        -- deriv c (one <+> p <.> Closure p)

-- | Interpret a regular expression
regexp :: (ClosedSemiring a, HasSingle a [c]) => RegExp c -> a
regexp (Char c)      = single [c]
regexp Zero          = zero
regexp One           = one
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Closure u)   = closure (regexp u)

{--------------------------------------------------------------------
    Decomposition as language
--------------------------------------------------------------------}

infixr 5 :<:
data Decomp c = Bool :<: (c -> Decomp c)

decompPred :: Decomp c -> Pred [c]
decompPred = Pred . decompPred'

decompPred' :: Decomp c -> ([c] -> Bool)
-- decompPred' (e :<: f) = list e (decompPred' . f)
decompPred' = list' . second (decompPred' .) . undecomp

-- decompPred' (e :<: f) = list e (\ c cs -> decompPred' (f c) cs)

predDecomp :: Pred [c] -> Decomp c
predDecomp (Pred p) = predDecomp' p

predDecomp' :: ([c] -> Bool) -> Decomp c
-- predDecomp' p = p [] :<: (\ c -> predDecomp' (p . (c :)))
-- predDecomp' p = p [] :<: (\ c -> predDecomp' (\ cs -> p (c : cs)))
-- predDecomp' p = p [] :<: predDecomp' . (\ c -> \ cs -> p (c : cs))

-- predDecomp' p = e :<: predDecomp' . f
--  where
--    (e,f) = unlist p

predDecomp' = decomp . second (predDecomp' .) . unlist

decomp :: Bool :* (c -> Decomp c) -> Decomp c
decomp (e,f) = e :<: f

undecomp :: Decomp c -> Bool :* (c -> Decomp c)
undecomp (e :<: f) = (e,f)

instance Semiring (Decomp c) where
  zero = False :<: const zero
  one  = True  :<: const zero
  (a :<: ps') <+> (b :<: qs') = (a || b) :<: liftA2 (<+>) ps' qs'
  (a :<: ps') <.> q@(b :<: qs') = (a && b) :<: liftA2 h ps' qs'
   where
     h p' q' = (if a then q' else zero) <+> (p' <.> q)

  -- (<+>) = liftA2 (||)

instance ClosedSemiring (Decomp c)

instance Eq c => HasSingle (Decomp c) [c] where
  single = product . map symbol
   where
     symbol c = False :<: (\ c' -> if c'==c then one else zero)

  -- single [] = one
  -- single (c:cs) = False :<: (\ c' -> if c==c' then single cs else zero)

instance HasTrie c => HasDecomp (Decomp c) c where
  hasEps (a :<: _) = a
  deriv c (_ :<: ps') = ps' c

{--------------------------------------------------------------------
    List trie with finite maps as language
--------------------------------------------------------------------}

infixr 5 :|
data LT c = Bool :| Map c (LT c) deriving Show

trimLT :: Ord c => Int -> LT c -> LT c
trimLT 0 _ = zero
trimLT n (a :| m) = a :| (trimLT (n-1) <$> m)

instance Ord c => Semiring (LT c) where
  zero = False :| M.empty
  one  = True  :| M.empty
  (a :| ps') <+> (b :| qs') = (a || b) :| M.unionWith (<+>) ps' qs'
#if 0
  -- Works, but it leaves many zero entries in the maps, due to (delta p <.>)
  p@(a :| ps') <.> q@(b :| qs') =
    (a && b) :| M.unionWith (<+>) (fmap (<.> q) ps') (fmap (delta p <.>) qs')
#elif 0
  (a :| ps') <.> q@(b :| qs') = (a && b) :| M.unionWith (<+>) us vs
   where
     us = fmap (<.> q) ps'
     vs | a = qs'
        | otherwise = M.empty
#elif 1
  (a :| ps') <.> q = (if a then q else zero) <+> (False :| fmap (<.> q) ps')
#else
  (False :| ps') <.> q = False :| fmap (<.> q) ps'
  (True  :| ps') <.> q@(b :| qs') = b :| M.unionWith (<+>) (fmap (<.> q) ps') qs'
#endif

instance Ord c => ClosedSemiring (LT c) where
  closure (_ :| ps') = q
   where
     q = True :| fmap (<.> q) ps'

instance (Ord c, Eq c) => HasSingle (LT c) [c] where
  single = foldr (\ c p -> False :| M.singleton c p) one
  -- single [] = one
  -- single (c:cs) = False :| M.singleton c (single cs)

instance Ord c => HasDecomp (LT c) c where
  hasEps (a :| _) = a
  deriv c (_ :| ps') = M.findWithDefault zero c ps'

{--------------------------------------------------------------------
    List trie as a language
--------------------------------------------------------------------}

instance HasTrie c => Semiring (LTrie c Bool) where
  zero = pure zero
  one = True :< pure zero
  ~(a :< ps') <+> ~(b :< qs') = (a || b) :< liftA2 (<+>) ps' qs'
  -- (<+>) = liftA2 (||) -- liftA2 (<+>)
  ~(a :< ps') <.> ~q@(b :< qs') = (a && b) :< liftA2 h ps' qs'
   where
     -- h p' q' = (if a then q' else zero) <+> (p' <.> q)
     -- h p' q' = if a then q' <+> p' <.> q else p' <.> q
     h | a         = \ p' q' -> q' <+> p' <.> q
       | otherwise = \ p' _  -> p' <.> q

-- Oops: I think I'll have to wrap LTrie to make it a language instance, because
-- I'll want a different Applicative. Wait and see.

instance HasTrie c => ClosedSemiring (LTrie c Bool)

closureLT :: HasTrie c => LTrie c Bool -> LTrie c Bool
closureLT t = t'
 where
   -- t' = one <+> (t <.> t')  -- diverge
   -- t' = t <.> t' -- diverge
   -- t' = t <.> t -- converge
   t' = one <+> t <.> (one <+> t <.> (one <+> t <.> (one <+> t <.> (one <+> t)))) -- converge

instance (HasTrie c, Eq c) => HasSingle (LTrie c Bool) [c] where
  single = foldr (\ c p -> False :< trie (\ c' -> if c==c' then p else zero)) one
  -- single [] = one -- True :< pure zero
  -- single (c:cs) = False :< trie (\ c' -> if c==c' then single cs else zero)

instance HasTrie c => HasDecomp (LTrie c Bool) c where
  hasEps (a :< _) = a
  deriv c (_ :< ps') = ps' ! c

{--------------------------------------------------------------------
    Memoization via generalized tries
--------------------------------------------------------------------}

infixr 0 :->:

-- | Memo trie from k to v
type k :->: v = Trie k v

-- | Domain types with associated memo tries
class Applicative (Trie k) => HasTrie k where
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

instance Applicative Pair where
  pure a = a :# a
  (f :# g) <*> (a :# b) = f a :# g b

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

{--------------------------------------------------------------------
    String tries
--------------------------------------------------------------------}

infixr 5 :<
data LTrie c a = a :< (c :->: LTrie c a)

-- TODO: Use HasTrieIsomorph for [c]. I'll probably have to add instances of
-- Semiring etc for generics.

deriving instance HasTrie c => Functor (LTrie c)

instance HasTrie c => Applicative (LTrie c) where
  pure a = t where t = a :< pure t
  liftA2 h ~(a :< as) ~(b :< bs) = h a b :< (liftA2.liftA2) h as bs

instance HasTrie c => HasTrie [c] where
  type Trie [c] = LTrie c
  trie f = f [] :< trie (\ c -> trie (f . (c :)))
  untrie (e :< ts) = list e (untrie . untrie ts)

-- Equivalently:
-- 
--   untrie (e :< _ ) [] = e
--   untrie (_ :< ts) (c:cs) = untrie (untrie ts c) cs
--   
--   untrie (e :< ts) = list e (\ c cs -> untrie (untrie ts c) cs)

list :: a -> (c -> [c] -> a) -> [c] -> a
list a _ [] = a
list _ f (c:as) = f c as

list' :: a :* (c -> [c] -> a) -> ([c] -> a)
list' = uncurry list

unlist :: ([c] -> a) -> a :* (c -> [c] -> a)
unlist f = (f [], \ c as -> f (c:as))

--   \ c cs -> f (c:cs)
-- = \ c cs -> (f . (c :)) cs
-- = \ c -> f . (c :)
-- = \ c -> der c f
-- = flip der f

-- TODO: rewrite trie @[c] vis unlist.

-- TODO: rename list & unlist.

-- TODO: Rewrite trie/untrie via list/unlist.
-- Maybe change HasTrie to have one isomorphism-valued method.
-- Or save for the isomorphism paper.

ltriePred :: HasTrie c => LTrie c Bool -> Pred [c]
ltriePred = Pred . untrie

predLTrie :: HasTrie c => Pred [c] -> LTrie c Bool
predLTrie (Pred f) = trie f

#if 0

{--------------------------------------------------------------------
    Temporary tests
--------------------------------------------------------------------}

lta,ltb :: LT Char
lta = single "a"
ltb = single "b"

#endif

{--------------------------------------------------------------------
    Constrained classes
--------------------------------------------------------------------}

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
