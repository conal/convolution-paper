{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Languages as functions to semirings

module Fun where

import Prelude hiding (sum,product)

import Control.Applicative (liftA2)
import Text.Show.Functions ()  -- for Decomp
import Data.Map (Map)
import qualified Data.Map as M

import Misc
import Semiring

{--------------------------------------------------------------------
    Generalized predicates
--------------------------------------------------------------------}

newtype s <-- a = F (a -> s)

instance Semiring s => Semiring (s <-- [c]) where
  zero = F (const zero)
  one = F (boolVal . null)
  F f <+> F g = F (\ w -> f w <+> g w)
  F f <.> F g = F (\ w -> sum [ f u <.> g v | (u,v) <- splits w ] )

instance Semiring s => StarSemiring (s <-- [c])

instance (Semiring s, Eq b) => HasSingle (s <-- b) b where
  single x = F (boolVal . (== x))

instance HasDecomp (s <-- [c]) c s where
  atEps (F f) = f []
  deriv (F f) c = F (f . (c :))

{--------------------------------------------------------------------
    Classic list-of-successes
--------------------------------------------------------------------}

-- Match a prefix of given string and yield corresponding suffixes for all
-- successful matches.
newtype Resid c s = Resid ([c] -> [([c], s)])

residF :: Semiring s => Resid c s -> (s <-- [c])
residF (Resid f) = F (\ w -> sum [ s | (w',s) <- f w, null w' ])

#if 0

instance Semiring s => Semiring (Resid c s) where
  zero = Resid (fail "no match")
  one = Resid return
  Resid f <+> Resid g = Resid (liftA2 (<>) f g)
  Resid f <.> Resid g = Resid (f >=> g)

#else

instance Semiring s => Semiring (Resid c s) where
  zero = Resid (const [])
  one = Resid (\ s -> [(s,one)])
  Resid f <+> Resid g = Resid (\ w -> f w <> g w)
  Resid f <.> Resid g = Resid (\ w -> [(w'', s <.> s') | (w',s) <- f w, (w'',s') <- g w'])

#endif

-- WORKING HERE.

#if 0

instance StarSemiring (Resid s)

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

#endif

{--------------------------------------------------------------------
    Regular expressions
--------------------------------------------------------------------}

infixl 6 :<+>
infixl 7 :<.>

-- | Regular expression
data RegExp c s =
    Char c
  | Value s
  | RegExp c s :<+> RegExp c s
  | RegExp c s :<.> RegExp c s
  | Closure (RegExp c s)
 deriving (Show,Eq)

instance Semiring s => Semiring (RegExp c s) where
  zero  = Value zero
  one   = Value one
  (<+>) = (:<+>)
  (<.>) = (:<.>)

instance Semiring s => StarSemiring (RegExp c s) where
  closure = Closure

instance (Functor f, Foldable f, Semiring s) => HasSingle (RegExp c s) (f c) where
  single = product . fmap Char

instance (Eq c, StarSemiring s) => HasDecomp (RegExp c s) c s where
  atEps (Char _)    = zero
  atEps (Value s)   = s
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Closure p) = closure (atEps p)
  
  deriv (Char c') c   = boolVal (c == c')
                        -- if c == c' then one else zero
  deriv (Value _) _   = zero
  deriv (p :<+> q) c  = deriv p c <+> deriv q c
  deriv (p :<.> q) c  = -- deriv p c <.> q <+> Value (atEps p) <.> deriv q c
                        Value (atEps p) <.> deriv q c <+> deriv p c <.> q
  deriv (Closure p) c = -- The following version works even if the atEps term
                        -- comes first in deriv (p :<.> q) c
                        Value (closure (atEps p)) <.> deriv p c <.> closure p
                        -- See 2018-01-13 journal.
                        -- The following version converges if the atEps term
                        -- comes second in deriv (p :<.> q) c
                        -- deriv (p <.> Closure p) c -- since deriv c one = zero
                        -- deriv c (one <+> p <.> Closure p)

-- TODO: fix deriv c (Closure p) to compute deriv p c and deriv c (Closure p)
-- just once. Do a bit of inlining and simplification.

-- | Interpret a regular expression
regexp :: (StarSemiring s, HasSingle s [c]) => RegExp c s -> s
regexp (Char c)      = single [c]
regexp (Value s)     = s
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Closure u)   = closure (regexp u)

{--------------------------------------------------------------------
    Decomposition as language
--------------------------------------------------------------------}

infix 1 <:
(<:) :: b -> (c -> [c] -> b) -> [c] -> b
(b <: _) []     = b
(_ <: h) (c:cs) = h c cs

-- der :: ([c] -> b) -> c -> ([c] -> b)

-- -- Identity:
-- deFun :: ([c] -> b) -> ([c] -> b)
-- deFun f = f [] <: \ c cs -> f (c:cs)

infix 1 :<:
data Decomp c s = s :<: (c -> Decomp c s) deriving Show

scaleD :: DetectableZero s => s -> Decomp c s -> Decomp c s
scaleD s _ | isZero s = zero
scaleD s (e :<: ts) = (s <.> e) :<: (scaleD s . ts)

decompFun :: Decomp c s -> ([c] -> s)
decompFun (e :<: ds) = e <: decompFun . ds

funDecomp :: ([c] -> s) -> Decomp c s
funDecomp f = atEps f :<: funDecomp . deriv f

-- funDecomp f = f [] :<: funDecomp . \ c -> f . (c :)
-- funDecomp f = f [] :<: \ c -> funDecomp (f . (c :))

-- f :: [c] -> s
-- f . (c :) :: [c] -> s
-- funDecomp (f . (c :)) :: Decomp c s

-- decompFun (e :<: _ ) [] = e
-- decompFun (_ :<: ds) (c:cs) = decompFun (ds c) cs

-- decompFun (e :<: ds) = list e (\ c cs -> decompFun (ds c) cs)
-- decompFun (e :<: ds) = list e (decompFun . ds)

-- -- If I keep, move to Misc
-- list :: b -> (c -> [c] -> b) -> [c] -> b
-- list b _ [] = b
-- list _ f (c:cs) = f c cs

-- -- A hopefully temporary hack for testing.
-- -- (Some of the tests show the language representation.)
-- instance Show (Decomp c s) where show (e :<: f) = "Decomp " ++ show e ++ " <function>"

decompF :: Decomp c s -> (s <-- [c])
decompF = F . decompFun

instance DetectableZero s => Semiring (Decomp c s) where
#if 0
  -- For the paper
  zero = zero :<: \ _c -> zero
  one  = one  :<: \ _c -> zero
  (a :<: dp) <+> (b :<: dq) = (a <+> b) :<: \ c -> dp c <+> dq c
  (a :<: dp) <.> ~q@(b :<: dq) = (a <.> b) :<: \ c -> scaleD a (dq c) <+> dp c <.> q
#else
  zero = zero :<: const zero
  one  = one  :<: const zero
  (a :<: dp) <+> (b :<: dq) = (a <+> b) :<: liftA2 (<+>) dp dq
#if 1
  (a :<: dp) <.> q = scaleD a q <+> (zero :<: (<.> q) . dp)
#else
  (a :<: dp) <.> ~q@(b :<: dq) = (a <.> b) :<: liftA2 h dp dq
   where
     h u v = scaleD a v <+> u <.> q
#endif

#endif

instance (StarSemiring s, DetectableZero s) => StarSemiring (Decomp c s) where
  -- See 2019-01-13 joural
  closure (a :<: dp) = q
    where
      q = as :<: fmap h dp
      as = closure a
      h d = as `scaleD` d <.> q

instance (DetectableZero s, Eq c) => HasSingle (Decomp c s) [c] where
#if 0
  single w = product [zero :<: boolVal (c' == c) | c <- w]
#else
  single = product . map symbol
   where
     -- symbol c = zero :<: (\ c' -> boolVal (c' == c))
     symbol c = zero :<: (boolVal . (== c))
#endif

instance HasDecomp (Decomp c s) c s where
  atEps (a :<: _) = a
  deriv (_ :<: ds) c = ds c

{--------------------------------------------------------------------
    List trie with finite maps
--------------------------------------------------------------------}

infix 1 :<
data Trie c s = s :< Map c (Trie c s) deriving Show

type OD c s = (Ord c, DetectableZero s)

trimT :: OD c s => Int -> Trie c s -> Trie c s
trimT 0 _ = zero
trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts

scaleT :: OD c s => s -> Trie c s -> Trie c s
scaleT s | isZero s  = const zero
         | otherwise = go
 where
   go ~(e :< ts) = (s <.> e) :< fmap go ts

-- scaleT s (e :< ts) = (s <.> e) :< fmap (scaleT s) ts

-- TODO: generalize scaleT to tmap, and then let scaleT s = tmap (s <.>).

-- -- Oops. We'd need to enumerate all of c.
-- funTrie :: ([c] -> s) -> Trie c s

-- funTrie :: ([c] -> s) -> Trie c s
-- funTrie f = 

trieFun :: OD c s => Trie c s -> ([c] -> s)
trieFun (e :< d) = e <: trieFun . (d !)

-- trieFun (e :< d) = e <: \ c cs -> trieFun (d ! c) cs

-- trieFun (e :< _ ) [] = e
-- trieFun (_ :< ts) (c:cs) = trieFun (ts ! c) cs

(!) :: (Ord c, Semiring s) => Map c s -> c -> s
m ! c = M.findWithDefault zero c m

trieF :: OD c s => Trie c s -> (s <-- [c])
trieF = F . trieFun

instance OD c s => Semiring (Trie c s) where
  zero = zero :< M.empty
  one  = one  :< M.empty
  ~(a :< dp) <+> ~(b :< dq) = (a <+> b) :< M.unionWith (<+>) dp dq
  -- (a :< dp) <+> (b :< dq) = (a <+> b) :< (dp <+> dq)
  -- c would have to be a monoid, though we could eliminate by introducing an
  -- Additive superclass of Semiring.
#if 0
  -- Wedges for the recursive anbn examples even with the lazy pattern.
  (a :< dp) <.> ~q@(b :< dq) =
    (a <.> b) :< M.unionWith (<+>) (fmap (<.> q) dp) (fmap (scaleT a) dq)
#elif 0
  -- Wedges for recursive anbn examples even with the lazy pattern.
  (a :< dp) <.> ~q@(b :< dq) = (a <.> b) :< M.unionWith (<+>) us vs
   where
     us = fmap (<.> q) dp
     vs = fmap (scaleT a) dq
#elif 1
  -- Works even for recursive anbn examples.
  (a :< dp) <.> q = a `scaleT` q <+> (zero :< fmap (<.> q) dp)
#elif 1
  -- Works even for recursive anbn examples.
  ~(a :< ps) <.> q = a `scaleT` q <+> (zero :< fmap (<.> q) ps)
#else
  -- Works even for recursive anbn examples.
  (a :< dp) <.> ~q@(b :< dq)
    | isZero a = zero :< fmap (<.> q) dp
    | otherwise = a <.> b :< M.unionWith (<+>) (fmap (<.> q) dp) (fmap (scaleT a) dq)
#endif

-- instance OD c s => StarSemiring (Trie c s) where
--   -- Wrong
--   closure (_ :< ds) = q where q = one :< fmap (<.> q) ds

instance (Ord c, StarSemiring s, DetectableZero s) => StarSemiring (Trie c s) where
#if 1
  -- Works
  closure (a :< dp) = q where q = closure a `scaleT` (one :< fmap (<.> q) dp)
#else
  -- Works
  -- See 2019-01-13 joural
  closure (a :< dp) = q
    where
      q = as :< fmap h dp
      as = closure a
      h d = as `scaleT` d <.> q
#endif

-- TODO: Fix so that scaleT checks isZero as only once.

instance OD c s => HasSingle (Trie c s) [c] where
  single w = product [zero :< M.singleton c one | c <- w]
  -- single = product . map symbol
  --  where
  --    symbol c = zero :< M.singleton c one


instance OD c s => HasDecomp (Trie c s) c s where
  atEps (a :< _) = a
  deriv (_ :< ds) c = ds ! c

{--------------------------------------------------------------------
    Temporary for testing
--------------------------------------------------------------------}


type T = Trie Char Bool
