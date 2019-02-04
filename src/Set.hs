-- | Languages as sets/predicates

module Set where

import Prelude hiding (sum,product)

-- import Data.Monoid (Monoid(..))
import Control.Arrow (second)
import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import Text.Show.Functions ()  -- for Decomp
import Data.List (stripPrefix)
import GHC.Types (Constraint)
import Data.Maybe (maybeToList)
import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Set (Set)
-- import qualified Data.Set as S
import Data.Semiring

import Misc
import Language

delta :: (Semiring a, Decomposable a c Bool) => a -> a
delta a | atEps a   = one
        | otherwise = zero

{--------------------------------------------------------------------
    Sets of strings (or other monoidal values)
--------------------------------------------------------------------}

#if 0

instance Semiring (Set a) where
  zero = emptyset
  one = single mempty
  p + q = set (a | a `elem` p || a `elem` q)
  p <.> q = set (u <> v | u `elem` p && v `elem` q)

instance StarSemiring (Set a) where
  star p = bigunion (n >= 0) (p^n)

-- instance HasSingle (Set a) a where
--   single a = set a

oneBool :: Semiring x => (a -> x) -> a -> Bool -> x
oneBool _ _ False = zero
oneBool f a True  = f a

instance HasSingle (Set a) a Bool where
  a +-> s = if s then set a else emptyset
  -- (+->) = oneBool set
  -- single a = set a

instance Eq a => Decomposable (Set a) a Bool where
  e <: h = (if e then set mempty else emptyset) `union` bigunion c h c
  atEps p = [] `elem` p
  deriv p c = set (cs | c : cs `elem` p)

#endif

{--------------------------------------------------------------------
    Lists
--------------------------------------------------------------------}

-- Data.Semiring (in semiring-num) gives instances for [a], but I want a
-- different choice. For now, add a newtype. In the paper, perhaps hide the
-- constructor via a %format directive.

newtype List a = L [a]
#if 0
  deriving Show
#else
instance Show a => Show (List a) where show (L as) = show as
#endif

instance Monoid a => Scalable (List a) Bool where
  s `scale` as = if s then as else zero
  -- scale False = const (L [])
  -- scale True  = id

instance Monoid a => Semiring (List a) where
  zero = L []
  one = L [mempty]
  L u <+> L v = L (u +#+ v)
  L u <.> L v = L (liftA2 (<>) u v)

infixr 5 +#+
(+#+) :: [a] -> [a] -> [a]
[] +#+ bs = bs
(a:as) +#+ bs = a : (bs +#+ as)

-- >>> "abcd" +#+ "efghij"
-- "aebfcgdhij"
-- >>> takeL 5 (star (single "ab"))
-- ["","ab","abab","ababab","abababab"]
-- >>> takeL 5 (star (star (single "ab")))
-- ["","","","",""]
-- >>> (single "a" <+> single "b") :: L String
-- ["a","b"]
-- >>> (single "a" <+> single "b") <+> (single "c" <+> single "d") :: L String
-- ["a","c","b","d"]

instance Monoid a => StarSemiring (List a)

#ifdef SINGLE
instance HasSingle (List a) a where
  single a = L [a]
#else
instance Eq a => HasSingle (Pred a) a Bool where
  a +-> s = if s then [a] else zero
#endif

instance Ord c => Decomposable (List [c]) (Map c) Bool where
  e <: m = L $
    (if e then ([] :) else id) $
    [c:w | (c,L ws) <- M.toList m, w <- ws]
  atEps (L ws) = any null ws
  deriv (L ws) = M.unionsWith (<+>) [M.singleton c (L [cs]) | c:cs <- ws]

takeL :: Int -> List a -> List a
takeL n (L as) = L (take n as)

-- >>> one :: L String
-- [""]

-- >>> single "a" :: L String
-- ["a"]

-- >>> takeL 5 (star (single "a") :: L String)
-- ["","a","aa","aaa","aaaa"]

-- >>> takeL 5 (star zero :: L String)
-- [""]

-- >>> takeL 5 (star one :: L String)
-- ["","","","",""]

-- >>> deriv (single "a" :: L String)
-- ... <hang> ...


-- Oh! deriv on an infinite list cannot give any information, becausse it 

-- >>> deriv (star (single "a") :: L String)

elems :: (Semiring p, HasSingle p a) => [a] -> p
elems as = sum [single a | a <- as]

{--------------------------------------------------------------------
    Predicates
--------------------------------------------------------------------}

newtype Pred a = Pred { unPred :: a -> Bool }

instance Show (Pred a) where show = const "<Pred>"

#if 0

setPred :: Set a -> Pred a
setPred as = Pred (\ a -> a `elem` as)

predSet :: Pred a -> Set a
predSet (Pred f) = set (a | f a)

#endif

instance Scalable (Pred a) Bool where
  s `scale` Pred f = Pred ((s <.>) . f)

instance Splittable a => Semiring (Pred a) where
  zero = Pred (const False)
  one = Pred isEmpty
  Pred f <+> Pred g = Pred (\ w -> f w || g w)
  Pred f <.> Pred g = Pred (\ w -> or [ f u && g v | (u,v) <- splits w ] )

instance StarSemiring (Pred [c])

#ifdef SINGLE
instance Eq a => HasSingle (Pred a) a where
  single a = Pred (fromBool . (== a))
#else
instance Eq a => HasSingle (Pred a) a Bool where
  a +-> s = Pred (a +-> s)
#endif

instance Decomposable (Pred [c]) ((->) c) Bool where
  e <: h = fromBool e <+> Pred (\ w -> or [ unPred (h c) w | c <- allVals ])
  atEps (Pred f) = f []
  -- deriv (Pred f) c = Pred (f . (c :))
  deriv (Pred f) c = Pred (\ cs -> f (c : cs))

-- >>> unPred one ""
-- True
-- >>> unPred one "a"
-- False

-- >>> unPred (single "a") ""
-- False
-- >>> unPred (single "a") "a"
-- True

-- >>> unPred (star (single "a")) ""
-- >>> unPred (star (single "a")) "a"

-- >>> unPred (star (single "a")) "aa"
-- True
-- >>> unPred (star (single "a")) "b"
-- False

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
  one = Resid (\ c -> [c])
  Resid f <+> Resid g = Resid (\ w -> f w <> g w)
  Resid f <.> Resid g = Resid (\ w -> [w'' | w' <- f w, w'' <- g w'])

#endif

instance StarSemiring (Resid c)

#ifdef SINGLE
instance Eq c => HasSingle (Resid c) [c] where
  single w = Resid (maybeToList . stripPrefix w)
#else
instance Eq c => HasSingle (Resid c) [c] Bool where
  (+->) = oneBool (\ w -> Resid (maybeToList . stripPrefix w))
#endif

-- instance Decomposable (Resid s) s Bool where
--   (<:) = error "(<:) not yet defined on Resid"
--   atEps (Resid f) = any null (f [])
--   deriv (Resid f) c = Resid (f . (c :)) -- TODO: check

#if 0
            deriv      :: c -> a -> a
       flip deriv      :: a -> c -> a
foldl (flip deriv) a s :: a
#endif

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
  | Star (RegExp c)
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

instance Eq c => StarSemiring (RegExp c) where
  star Zero = One
  star e    = Star e

#else

type OkSym c = (() :: Constraint)

instance Semiring (RegExp c) where
  zero  = Zero
  one   = One
  (<+>) = (:<+>)
  (<.>) = (:<.>)

instance StarSemiring (RegExp c) where
  star = Star

#endif

#ifdef SINGLE
instance OkSym c => HasSingle (RegExp c) [c] where
  single = product . fmap Char
#else
instance OkSym c => HasSingle (RegExp c) [c] Bool where
  -- single = foldr (\ c e -> Char c <.> e) One
  (+->) = oneBool (product . map Char)
#endif

instance Eq c => Decomposable (RegExp c) ((->) c) Bool where
  (<:) = error "(<:) not yet defined on RegExp"
  atEps (Char _)    = zero
  atEps Zero        = zero
  atEps One         = one
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Star p) = star (atEps p)
  
  deriv (Char c') c | c == c'   = one
                    | otherwise = zero
  deriv Zero _                  = zero
  deriv One _                   = zero
  deriv (p :<+> q) c            = deriv p c <+> deriv q c
#if 1
  -- This one definition works fine if we have OptimizeRegexp
  deriv (p :<.> q) c            = delta p <.> deriv q c <+> deriv p c <.> q
#else
  -- Fix to check atEps p just once, not once per c
  deriv (p :<.> q) c | atEps p   = deriv p c <.> q <+> deriv q c
                                   -- deriv q c <+> deriv p c <.> q
                     | otherwise = deriv p c <.> q
#endif
  deriv (Star p) c   = deriv p c <.> star p
                        -- = deriv (p <.> Star p) c -- since deriv c one = zero
                        -- = deriv c (one <+> p <.> Star p)

instance Scalable (RegExp c) Bool where
  scale True  = id
  scale False = const Zero

-- TODO: Maybe use (.>) in deriv (p :<.> q)

-- | Interpret a regular expression
regexp :: (StarSemiring x, HS x c Bool) => RegExp c -> x
regexp (Char c)      = single [c]
regexp Zero          = zero
regexp One           = one
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Star u)   = star (regexp u)

{--------------------------------------------------------------------
    Decomposition as language
--------------------------------------------------------------------}

-- infix 1 :<:
data Decomp c = Bool :<: (c -> Decomp c)

inDecomp :: Decomp c -> ([c] -> Bool)
inDecomp (e :<: _ ) [] = e
inDecomp (_ :<: ds) (c:cs) = inDecomp (ds c) cs
-- inDecomp (e :<: f) = list e (inDecomp . f)
-- inDecomp = list' . second (inDecomp .) . undecomp

-- decompPred' (e :<: f) = list e (\ c cs -> decompPred' (f c) cs)

instance Scalable (Decomp c) Bool where
  scale s = go
   where
     go (e :<: ts) = (s <.> e) :<: (go . ts)

-- A hopefully temporary hack for testing.
-- (Some of the tests show the language representation.)
instance Show (Decomp c) where show _ = "<Decomp>"

decompPred :: Decomp c -> Pred [c]
decompPred = Pred . inDecomp

predDecomp :: Pred [c] -> Decomp c
predDecomp (Pred p) = predDecomp' p

predDecomp' :: ([c] -> Bool) -> Decomp c
-- predDecomp' p = p [] :<: (\ c -> predDecomp' (p . (c :)))
-- predDecomp' p = p [] :<: (\ c -> predDecomp' (\ cs -> p (c : cs)))
-- predDecomp' p = p [] :<: predDecomp' . (\ c -> \ cs -> p (c : cs))

-- predDecomp' p = e :<: predDecomp' . f
--  where
--    (e,f) = unlist p

predDecomp' = mkDecomp . second (predDecomp' .) . unlist

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

mkDecomp :: Bool :* (c -> Decomp c) -> Decomp c
mkDecomp (e,f) = e :<: f

undecomp :: Decomp c -> Bool :* (c -> Decomp c)
undecomp (e :<: f) = (e,f)

instance Semiring (Decomp c) where
  zero = False :<: const zero
  one  = True  :<: const zero
  (a :<: ps') <+> (b :<: qs') = (a || b) :<: liftA2 (<+>) ps' qs'
  (a :<: ps') <.> ~q@(b :<: qs') = (a && b) :<: liftA2 h ps' qs'
   where
     h p' q' = (if a then q' else zero) <+> p' <.> q

  -- (<+>) = liftA2 (||)

instance StarSemiring (Decomp c) where
  -- See 2019-01-13 joural
  star (a :<: dp) = q
    where
      q = as :<: fmap h dp
      as = star a
      h d = as .> d <.> q

#ifdef SINGLE
instance Eq c => HasSingle (Decomp c) [c] where
  single = product . map symbol
   where
     symbol c = False :<: (\ c' -> if c'==c then one else zero)
#else
instance Eq c => HasSingle (Decomp c) [c] Bool where
  (+->) = oneBool (product . map symbol)
   where
     symbol c = False :<: (\ c' -> if c'==c then one else zero)
#endif

instance Decomposable (Decomp c) ((->) c) Bool where
  (<:) = (:<:)
  atEps (a :<: _) = a
  deriv (_ :<: ds) c = ds c

{--------------------------------------------------------------------
    List trie with finite maps as language
--------------------------------------------------------------------}

infix 1 :<
data Trie c = Bool :< Map c (Trie c) deriving Show

inTrie :: Ord c => Trie c -> [c] -> Bool
inTrie (e :< _ ) [] = e
inTrie (_ :< ds) (c:cs) = inTrie (ds `mat` c) cs

mat :: (Ord c, Semiring a) => Map c a -> c -> a
m `mat` c = M.findWithDefault zero c m

triePred :: Ord c => Trie c -> Pred [c]
triePred = Pred . inTrie

decomp :: Ord c => Trie c -> Decomp c
-- decomp (e :< ds) = e :<: (\ c -> decomp (ds `mat` c))
-- decomp (e :< ds) = e :<: (\ c -> decomp (mat ds c))
decomp (e :< ds) = e :<: (decomp . (ds `mat`))

instance Scalable (Trie c) Bool where
  scale s = go
   where
     go (e :< ts) = (s <.> e) :< fmap go ts

-- triePred = decompPred . decomp

-- trimLT :: Ord c => Int -> Trie c -> Trie c
-- trimLT 0 _ = zero
-- trimLT n (a :< m) = a :< (trimLT (n-1) <$> m)

instance Ord c => Semiring (Trie c) where
  zero = False :< M.empty
  one  = True  :< M.empty
  (a :< ps') <+> (b :< qs') = (a || b) :< M.unionWith (<+>) ps' qs'
#if 0
  -- Works, but it leaves many zero entries in the maps (due to (delta p <.>))
  -- and wedges for the recursive anbn examples even with the lazy pattern.
  p@(a :< ps') <.> ~q@(b :< qs') =
    (a && b) :< M.unionWith (<+>) (fmap (<.> q) ps') (fmap (delta p <.>) qs')
#elif 1
  -- Wedges for recursive anbn examples with the lazy pattern.
  (a :< ps') <.> ~q@(b :< qs') = (a && b) :< M.unionWith (<+>) us vs
   where
     us = fmap (<.> q) ps'
     vs = if a then qs' else M.empty
#elif 0
  -- Works even for recursive anbn examples.
  (a :< ps') <.> q = (if a then q else zero) <+> (False :< fmap (<.> q) ps')
#else
  -- Works even for recursive anbn examples.
  (False :< ps') <.> q = False :< fmap (<.> q) ps'
  (True  :< ps') <.> q@(b :< qs') = b :< M.unionWith (<+>) (fmap (<.> q) ps') qs'
#endif

instance Ord c => StarSemiring (Trie c) where

  -- Correct? Look for counterexamples.
  star (_ :< ds) = q where q = True :< fmap (<.> q) ds

  -- -- See 2019-01-13 joural
  -- star (a :< dp) = q
  --   where
  --     q = as :< fmap h dp
  --     as = star a
  --     h d = as .> d <.> q

#ifdef SINGLE
instance Ord c => HasSingle (Trie c) [c] where
  single = foldr (\ c p -> False :< M.singleton c p) one
#else
instance Ord c => HasSingle (Trie c) [c] Bool where
  (+->) = oneBool (product . map symbol)
   where
     symbol c = False :< M.singleton c one
#endif

instance Ord c => DetectableZero (Trie c) where
  isZero (b :< m) = isZero b && M.null m

instance Ord c => Decomposable (Trie c) (Map c) Bool where
  (<:) = (:<)
  atEps (b :< _) = b
  deriv (_ :< d) = d

