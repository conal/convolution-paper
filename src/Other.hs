-- | Languages as sets/predicates

module Other where

import Prelude hiding (sum,product)

-- import Data.Monoid (Monoid(..))

import Control.Applicative (liftA2)

import GHC.Generics

import qualified Data.IntTrie as IT  -- data-inttrie

import Misc
import Semiring
import Set hiding (Trie)

{--------------------------------------------------------------------
    List trie as a language
--------------------------------------------------------------------}

instance HasTrie c => Semiring (LTrie c Bool) where
  zero = pure zero
  one = True :| pure zero
  ~(a :| ps') <+> ~(b :| qs') = (a || b) :| liftA2 (<+>) ps' qs'
  -- (<+>) = liftA2 (||) -- liftA2 (<+>)
  ~(a :| ps') <.> ~q@(b :| qs') = (a && b) :| liftA2 h ps' qs'
   where
     -- h p' q' = (if a then q' else zero) <+> (p' <.> q)
     -- h p' q' = if a then q' <+> p' <.> q else p' <.> q
     h | a         = \ p' q' -> q' <+> p' <.> q
       | otherwise = \ p' _  -> p' <.> q

-- Oops: I think I'll have to wrap LTrie to make it a language instance, because
-- I'll want a different Applicative. Wait and see.

instance HasTrie c => StarSemiring (LTrie c Bool)

closureLT :: HasTrie c => LTrie c Bool -> LTrie c Bool
closureLT t = t'
 where
   -- t' = one <+> (t <.> t')  -- diverge
   -- t' = t <.> t' -- diverge
   -- t' = t <.> t -- converge
   t' = one <+> t <.> (one <+> t <.> (one <+> t <.> (one <+> t <.> (one <+> t)))) -- converge

instance (HasTrie c, Eq c) => HasSingle (LTrie c Bool) [c] where
  single = foldr (\ c p -> False :| trie (\ c' -> if c==c' then p else zero)) one
  -- single [] = one -- True :| pure zero
  -- single (c:cs) = False :| trie (\ c' -> if c==c' then single cs else zero)

-- instance HasTrie c => HasDecomp (LTrie c Bool) (Trie c) Bool where
--   (<:) = (:|)
--   atEps (a :| _) = a
--   deriv (_ :| d) = d

-- Illegal type synonym family application in instance: Trie c

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

-- -- | Indexing. Synonym for 'untrie'.
-- (!) :: HasTrie k => (k :->: v) -> k  ->  v
-- (!) = untrie

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

infix 1 :|
data LTrie c a = a :| (c :->: LTrie c a)

-- TODO: Use HasTrieIsomorph for [c]. I'll probably have to add instances of
-- Semiring etc for generics.

deriving instance HasTrie c => Functor (LTrie c)

instance HasTrie c => Applicative (LTrie c) where
  pure a = t where t = a :| pure t
  liftA2 h ~(a :| as) ~(b :| bs) = h a b :| (liftA2.liftA2) h as bs

instance HasTrie c => HasTrie [c] where
  type Trie [c] = LTrie c
  trie f = f [] :| trie (\ c -> trie (f . (c :)))
  untrie (e :| ts) = list e (untrie . untrie ts)

-- Equivalently:
-- 
--   untrie (e :| _ ) [] = e
--   untrie (_ :| ts) (c:cs) = untrie (untrie ts c) cs
--   
--   untrie (e :| ts) = list e (\ c cs -> untrie (untrie ts c) cs)

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

lta,ltb :: DecompM Char
lta = single "a"
ltb = single "b"

#endif
