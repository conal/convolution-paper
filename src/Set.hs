-- | Languages as sets/predicates

module Set where

import Prelude hiding (sum,product)

-- import Data.Monoid (Monoid(..))
import Control.Arrow (second)
import Control.Applicative (liftA2)
import Control.Monad ((>=>))
import Data.List (stripPrefix)
import GHC.Types (Constraint)
import Data.Maybe (maybeToList)
import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Set (Set)
-- import qualified Data.Set as S

import Misc
import Semiring

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
  closure p = bigunion (n >= 0) (p^n)

instance HasSingle (Set a) a where
  single a = set a

instance Eq a => Decomposable (Set a) a Bool where
  e <: h = (if e then set mempty else emptyset) `union` bigunion c h c
  atEps p = [] `elem` p
  deriv p c = set (cs | c : cs `elem` p)

#endif

-- listElems :: Ord a => [a] -> Set a

-- listElems = foldr insert S.empty where insert a as = S.singleton a `S.union` as

-- listElems = foldr S.insert S.empty

-- listElems []      = S.empty
-- listElems (a:as)  = S.singleton a `S.union` listElems as

{--------------------------------------------------------------------
    Predicates
--------------------------------------------------------------------}

newtype Pred s = Pred { unPred :: s -> Bool }

#if 0

setPred :: Set a -> Pred a
setPred as = Pred (\ a -> a `elem` as)

predSet :: Pred a -> Set a
predSet (Pred f) = set (a | f a)

#endif

allVals :: [c]
allVals = error "allVals not defined"

instance Semiring (Pred [c]) where
  zero = Pred (const False)
  one = Pred null
  Pred f <+> Pred g = Pred (\ w -> f w || g w)
  Pred f <.> Pred g = Pred (\ w -> or [ f u && g v | (u,v) <- splits w ] )

instance StarSemiring (Pred [c])

instance Eq s => HasSingle (Pred s) s where
  single s = Pred (== s)

instance Decomposable (Pred [c]) ((->) c) Bool where
  e <: h = boolVal e <+> Pred (\ w -> or [ unPred (h c) w | c <- allVals ])
  atEps (Pred f) = f []
  -- deriv (Pred f) c = Pred (f . (c :))
  deriv (Pred f) c = Pred (\ cs -> f (c : cs))

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

instance StarSemiring (Resid s)

instance Eq s => HasSingle (Resid s) [s] where
  -- single x = Resid (\ s -> case stripPrefix x s of
  --                            Just s' -> [s']
  --                            Nothing -> [])
  single x = Resid (maybeToList . stripPrefix x)

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

instance Eq c => StarSemiring (RegExp c) where
  closure Zero = One
  closure e    = Closure e

#else

type OkSym c = (() :: Constraint)

instance Semiring (RegExp c) where
  zero  = Zero
  one   = One
  (<+>) = (:<+>)
  (<.>) = (:<.>)

instance StarSemiring (RegExp c) where
  closure = Closure

#endif

#if 1

instance OkSym c => HasSingle (RegExp c) [c] where
  -- single = foldr (\ c e -> Char c <.> e) One
  single = product . map Char

#else
-- Or from an arbitrary foldable
instance (Functor f, Foldable f, OkSym c) => HasSingle (RegExp c) (f c) where
  single = product . fmap Char
  -- single = foldr (\ c e -> Char c <.> e) One

-- We could even define balanced folding of sums and products via two monoid
-- wrappers.

#endif

instance Eq c => Decomposable (RegExp c) ((->) c) Bool where
  (<:) = error "(<:) not yet defined on RegExp"
  atEps (Char _)    = zero
  atEps Zero        = zero
  atEps One         = one
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Closure p) = closure (atEps p)
  
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
  deriv (Closure p) c   = deriv p c <.> closure p
                        -- = deriv (p <.> Closure p) c -- since deriv c one = zero
                        -- = deriv c (one <+> p <.> Closure p)

-- | Interpret a regular expression
regexp :: (StarSemiring a, HasSingle a [c]) => RegExp c -> a
regexp (Char c)      = single [c]
regexp Zero          = zero
regexp One           = one
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Closure u)   = closure (regexp u)

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

scaleD :: Bool -> Decomp c -> Decomp c
scaleD False _ = zero
scaleD s (e :<: ts) = (s <.> e) :<: (scaleD s . ts)

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
  closure (a :<: dp) = q
    where
      q = as :<: fmap h dp
      as = closure a
      h d = as `scaleD` d <.> q

instance Eq c => HasSingle (Decomp c) [c] where
  single = product . map symbol
   where
     symbol c = False :<: (\ c' -> if c'==c then one else zero)

  -- single [] = one
  -- single (c:cs) = False :<: (\ c' -> if c==c' then single cs else zero)

instance Decomposable (Decomp c) ((->) c) Bool where
  (<:) = (:<:)
  atEps (a :<: _) = a
  deriv (_ :<: ds) c = ds c

{--------------------------------------------------------------------
    List trie with finite maps as language
--------------------------------------------------------------------}

-- infix 1 :<
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
  closure (_ :< ds) = q where q = True :< fmap (<.> q) ds

  -- -- See 2019-01-13 joural
  -- closure (a :< dp) = q
  --   where
  --     q = as :< fmap h dp
  --     as = closure a
  --     h d = as `scaleT` d <.> q

instance Ord c => HasSingle (Trie c) [c] where
  -- single = foldr (\ c p -> False :< M.singleton c p) one
  -- single [] = one
  -- single (c:cs) = False :< M.singleton c (single cs)
  single = product . map symbol
   where
     symbol c = False :< M.singleton c one

instance Ord c => DetectableZero (Trie c) where
  isZero (b :< m) = isZero b && M.null m

instance Ord c => Decomposable (Trie c) (Map c) Bool where
  (<:) = (:<)
  atEps (b :< _) = b
  deriv (_ :< d) = d

