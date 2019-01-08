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

import Misc
import Semiring

delta :: (Semiring a, HasDecomp a c Bool) => a -> a
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
  p <.> q = set (p <> q | u `elem` p && v `elem` q)

instance ClosedSemiring (Set a) where
  closure p = bigunion (n >= 0) (p^n)

instance HasSingle (Set a) a where
  single a = set a

instance Eq a => HasDecomp (Set a) a Bool where
  atEps p = [] `elem` p
  deriv c p = set (cs | c : cs `elem` p)

#endif

{--------------------------------------------------------------------
    Predicates
--------------------------------------------------------------------}

newtype Pred s = Pred (s -> Bool)

#if 0

setPred :: Set a -> Pred a
setPred as = Pred (\ a -> a `elem` as)

predSet :: Pred a -> Set a
predSet (Pred f) = set (a | f a)

#endif

instance Semiring (Pred [c]) where
  zero = Pred (const False)
  one = Pred null
  Pred f <+> Pred g = Pred (\ x -> f x || g x)
  Pred f <.> Pred g = Pred (\ x -> or [ f u && g v | (u,v) <- splits x ] )

instance ClosedSemiring (Pred [c])

instance Eq s => HasSingle (Pred s) s where
  single s = Pred (== s)

instance HasDecomp (Pred [c]) c Bool where
  atEps (Pred f) = f []
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

instance HasDecomp (Resid s) s Bool where
  atEps (Resid f) = any null (f [])
  deriv c (Resid f) = Resid (f . (c :)) -- TODO: check

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

instance Eq c => HasDecomp (RegExp c) c Bool where
  atEps (Char _)    = zero
  atEps Zero        = zero
  atEps One         = one
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Closure p) = closure (atEps p)
  
  deriv c (Char c') | c == c'   = one
                    | otherwise = zero
  deriv _ Zero                  = zero
  deriv _ One                   = zero
  deriv c (p :<+> q)            = deriv c p <+> deriv c q
#if 1
  -- This one definition works fine if we have OptimizeRegexp
  deriv c (p :<.> q)            = delta p <.> deriv c q <+> deriv c p <.> q
#else
  deriv c (p :<.> q) | atEps p  = deriv c q <+> deriv c p <.> q
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

-- infix 1 :<:
data Decomp c = Bool :<: (c -> Decomp c)

inDecomp :: Decomp c -> ([c] -> Bool)
inDecomp (e :<: _ ) [] = e
inDecomp (_ :<: ds) (c:cs) = inDecomp (ds c) cs
-- inDecomp (e :<: f) = list e (inDecomp . f)
-- inDecomp = list' . second (inDecomp .) . undecomp

-- decompPred' (e :<: f) = list e (\ c cs -> decompPred' (f c) cs)

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

instance ClosedSemiring (Decomp c)

instance Eq c => HasSingle (Decomp c) [c] where
  single = product . map symbol
   where
     symbol c = False :<: (\ c' -> if c'==c then one else zero)

  -- single [] = one
  -- single (c:cs) = False :<: (\ c' -> if c==c' then single cs else zero)

instance HasDecomp (Decomp c) c Bool where
  atEps (a :<: _) = a
  deriv c (_ :<: ds) = ds c

{--------------------------------------------------------------------
    List trie with finite maps as language
--------------------------------------------------------------------}

-- infix 1 :|
data DecompM c = Bool :| Map c (DecompM c) deriving Show

inDecompM :: Ord c => DecompM c -> [c] -> Bool
inDecompM (e :| _ ) [] = e
inDecompM (_ :| ds) (c:cs) = inDecompM (ds `mat` c) cs

mat :: (Ord c, Semiring a) => Map c a -> c -> a
m `mat` c = M.findWithDefault zero c m

mdecompPred :: Ord c => DecompM c -> Pred [c]
mdecompPred = Pred . inDecompM

decomp :: Ord c => DecompM c -> Decomp c
-- decomp (e :| ds) = e :<: (\ c -> decomp (ds `mat` c))
-- decomp (e :| ds) = e :<: (\ c -> decomp (mat ds c))
decomp (e :| ds) = e :<: (decomp . (ds `mat`))

-- mdecompPred = decompPred . decomp

-- trimLT :: Ord c => Int -> DecompM c -> DecompM c
-- trimLT 0 _ = zero
-- trimLT n (a :| m) = a :| (trimLT (n-1) <$> m)

instance Ord c => Semiring (DecompM c) where
  zero = False :| M.empty
  one  = True  :| M.empty
  (a :| ps') <+> (b :| qs') = (a || b) :| M.unionWith (<+>) ps' qs'
#if 0
  -- Works, but it leaves many zero entries in the maps (due to (delta p <.>))
  -- and wedges for the recursive anbn examples even with the lazy pattern.
  p@(a :| ps') <.> ~q@(b :| qs') =
    (a && b) :| M.unionWith (<+>) (fmap (<.> q) ps') (fmap (delta p <.>) qs')
#elif 1
  -- Wedges for recursive anbn examples with the lazy pattern.
  (a :| ps') <.> ~q@(b :| qs') = (a && b) :| M.unionWith (<+>) us vs
   where
     us = fmap (<.> q) ps'
     vs = if a then qs' else M.empty
#elif 0
  -- Works even for recursive anbn examples.
  (a :| ps') <.> q = (if a then q else zero) <+> (False :| fmap (<.> q) ps')
#else
  -- Works even for recursive anbn examples.
  (False :| ps') <.> q = False :| fmap (<.> q) ps'
  (True  :| ps') <.> q@(b :| qs') = b :| M.unionWith (<+>) (fmap (<.> q) ps') qs'
#endif

instance Ord c => ClosedSemiring (DecompM c) where
  closure (_ :| ds) = q where q = True :| fmap (<.> q) ds

instance Ord c => HasSingle (DecompM c) [c] where
  -- single = foldr (\ c p -> False :| M.singleton c p) one
  -- single [] = one
  -- single (c:cs) = False :| M.singleton c (single cs)
  single = product . map symbol
   where
     symbol c = False :| M.singleton c one

instance Ord c => HasDecomp (DecompM c) c Bool where
  atEps (a :| _) = a
  deriv c (_ :| ds) = ds `mat` c
