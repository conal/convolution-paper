{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Languages as functions to semirings

module Fun where

import Prelude hiding (sum,product)

import Control.Applicative (liftA2)
import Text.Show.Functions ()  -- for Decomp
import Data.Map
  ( Map,toList,fromListWith,empty,singleton,insert,unionWith
  , unionsWith,mapKeys,findWithDefault,keysSet )
-- import qualified Data.Map as M
import qualified Data.Set as S

import Misc
import Semiring
import Constrained

{--------------------------------------------------------------------
    Flipped functions / generalized predicates
--------------------------------------------------------------------}

newtype b <-- a = F { unF :: a -> b }

instance Semiring s => Semiring (s <-- [c]) where
  zero = F (const zero)
  one = F (boolVal . null)
  F f <+> F g = F (\ w -> f w <+> g w)
  F f <.> F g = F (\ w -> sum [ f u <.> g v | (u,v) <- splits w ] )

instance Semiring s => StarSemiring (s <-- [c])

instance (Semiring s, Eq b) => HasSingle (s <-- b) b where
  single x = F (boolVal . (== x))

instance Semiring s => Decomposable (s <-- [c]) ((->) c) s where
  b <: h = F (b <: unF . h)

  -- b <: h = F f where  f []      = b
  --                     f (c:cs)  = unF (h c) cs

  -- b <: h = F f
  --   where
  --     f []   = b
  --     f (c:cs) = unF (h c) cs

  -- b <: h = F (\ case []   -> b
  --                    c:cs -> unF (h c) cs)

  atEps (F f) = f mempty
  deriv (F f) = \ c -> F (\ cs -> f (c:cs))

-- The Functor and Applicative instances exist but are not computable.

instance Semiring b => FunctorC ((<--) b) where
  fmapC h (F f) = F (\ w -> undefined h f w)

instance Semiring b => ApplicativeC ((<--) b) where
  pureC a = F (\ w -> undefined a w)
  liftA2C h (F f) (F g) = F (\w -> undefined h f g w)

{--------------------------------------------------------------------
    Flipped finite maps
--------------------------------------------------------------------}

-- TODO: Infix notation for Map'

newtype b :<-- a = M (Map a b) deriving Show

instance (Monoid a, Ord a, Semiring b) => Semiring (b :<-- a) where
  zero = M empty
  one = single mempty
  -- one = M (singleton mempty one)
  M p <+> M q = M (unionWith (<+>) p q)
  M p <.> M q = M (fromListWith (<+>)
                     [(u <> v, s <.> t) | (u,s) <- toList p, (v,t) <- toList q])

instance Semiring b => HasSingle (b :<-- a) a where
  single a = M (singleton a one)

instance (Ord c, Semiring s) => Decomposable (s :<-- [c]) (Map c) s where
  b <: d = M (insert [] b (unionsWith (<+>)
                            [ mapKeys (c:) css | (c,M css) <- toList d ]))
  atEps (M p) = p ! []
              -- findWithDefault zero [] p
  deriv (M p) = fromListWith (<+>) [(c, M (singleton cs s)) | (c:cs,s) <- toList p]

instance Semiring b => FunctorC ((:<--) b) where
  type Ok ((:<--) b) a = Ord a
  fmapC h (M p) = M (fromListWith (<+>) [(h a, b) | (a,b) <- toList p])

instance Semiring b => ApplicativeC ((:<--) b) where
  pureC b = M (singleton b one)
  liftA2C h (M p) (M q) =
    M (fromListWith (<+>) [(h a b, s <.> t) | (a,s) <- toList p, (b,t) <- toList q])

-- >>> zero :: Bool :<-- String
-- M (fromList [])
-- >>> one :: Bool :<-- String
-- M (fromList [("",True)])
-- >>> single "cat" :: Bool :<-- String
-- M (fromList [("cat",True)])

-- >>> cat = single "cat" :: Bool :<-- String

-- >>> zero <+> single "cat" :: Bool :<-- String
-- M (fromList [("cat",True)])
-- >>> one <+> single "cat" :: Bool :<-- String
-- M (fromList [("",True),("cat",True)])

-- >>> (one <+> cat) <.> cat
-- M (fromList [("cat",True),("catcat",True)])

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

instance Decomposable (Resid s) s Bool where
  (<:) = ??
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

-- instance (Functor f, Foldable f, Semiring s) => HasSingle (RegExp c s) (f c) where
--   single = product . fmap Char

instance Semiring s => HasSingle (RegExp c s) [c] where
  single = product . map Char

scaleRE :: DetectableZero s => s -> RegExp c s -> RegExp c s
scaleRE s e | isZero s  = zero
            | otherwise = Value s <.> e

#if 0

instance (Ord c, StarSemiring s, DetectableZero s) => Decomposable (RegExp c s) (Map c) s where
  e <: d = Value e <+> sum [ single [c] <.> dc | (c,dc) <- toList d ]
  atEps (Char _)    = zero
  atEps (Value s)   = s
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Closure p) = closure (atEps p)
  
  deriv (Char c')  = single c'
  deriv (Value _)  = empty
  deriv (p :<+> q) = unionWith (<+>) (deriv p) (deriv q)

  deriv (p :<.> q) =
    unionWith (<+>) (fmap (<.> q) (deriv p)) (fmap (scaleRE (atEps p)) (deriv q))

  -- deriv (p :<.> q) c  = -- deriv p c <.> q <+> Value (atEps p) <.> deriv q c
  --                       atEps p `scaleRE` deriv q c <+> deriv p c <.> q

  -- deriv (p :<.> q) c  = -- deriv p c <.> q <+> Value (atEps p) <.> deriv q c
  --                       Value (atEps p) <.> deriv q c <+> deriv p c <.> q

  -- deriv (Closure p) =
  --   fmap (\ d -> Value (closure (atEps p)) <.> d <.> Closure p) (deriv p)

  -- Testing hangs on a^nb^n.

  deriv (Closure p) = fmap (\ d -> pc <.> d <.> Closure p) (deriv p)
   where
     pc = Value (closure (atEps p))

#else

instance (Eq c, StarSemiring s) => Decomposable (RegExp c s) ((->) c) s where
  e <: d = Value e <+> sum [ single [c] <.> d c | c <- allVals ]

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

#endif

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

-- -- Identity:
-- deFun :: ([c] -> b) -> ([c] -> b)
-- deFun f = f [] <: \ c cs -> f (c:cs)

infix 1 :<:
data Decomp c s = s :<: (c -> Decomp c s) deriving Show

scaleD :: DetectableZero s => s -> Decomp c s -> Decomp c s
scaleD s _ | isZero s = zero
scaleD s (e :<: ts) = (s <.> e) :<: (scaleD s . ts)

decompFun :: Semiring s => Decomp c s -> ([c] -> s)
decompFun (e :<: ds) = e <: decompFun . ds

funDecomp :: Semiring s => ([c] -> s) -> Decomp c s
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

decompF :: Semiring s => Decomp c s -> (s <-- [c])
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

instance DetectableZero s => Decomposable (Decomp c s) ((->) c) s where
  (<:) = (:<:)
  atEps (a :<: _) = a
  deriv (_ :<: d) = d

{--------------------------------------------------------------------
    List trie with finite maps
--------------------------------------------------------------------}

infix 1 :<
data Trie c b = b :< Map c (Trie c b) deriving Show

#if 0

instance FunctorC ((Trie c)) where
  fmapC h (s :< ts) = h s :< (fmapC.fmapC) h ts

instance ApplicativeC (Trie c) where
  pureC a = a :< empty
  liftA2C h (a :< us) (b :< vs) = h a b :< (liftA2C.liftA2C) h us vs

-- Hm. I need Applicative (Map c). Define in Semiring.

-- Maybe we don't want these instances. Return to this question.

instance FunctorC (Map k)

instance ApplicativeC (Map k) where
  pureC v = singleton one v  -- ??
  liftA2C h u v =
    fromListWith (<+>)
      [h (u!k) (v!k) | k <- S.toList (keysSet u `S.union` keysSet v)]

-- TODO: use these instances!

#endif

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

-- (!) :: (Ord c, Semiring s) => Map c s -> c -> s
-- m ! c = findWithDefault zero c m

trieF :: OD c s => Trie c s -> (s <-- [c])
trieF = F . trieFun

instance OD c s => Semiring (Trie c s) where
  zero = zero :< empty
  one  = one  :< empty
  ~(a :< dp) <+> ~(b :< dq) = (a <+> b) :< unionWith (<+>) dp dq
  -- (a :< dp) <+> (b :< dq) = (a <+> b) :< (dp <+> dq)
  -- c would have to be a monoid, though we could eliminate by introducing an
  -- Additive superclass of Semiring.
#if 0
  -- Wedges for the recursive anbn examples even with the lazy pattern.
  (a :< dp) <.> ~q@(b :< dq) =
    (a <.> b) :< unionWith (<+>) (fmap (<.> q) dp) (fmap (scaleT a) dq)
#elif 0
  -- Wedges for recursive anbn examples even with the lazy pattern.
  (a :< dp) <.> ~q@(b :< dq) = (a <.> b) :< unionWith (<+>) us vs
   where
     us = fmap (<.> q) dp
     vs = fmap (scaleT a) dq
#elif 1
  -- Works even for recursive anbn examples.
  ~(a :< ps) <.> q = a `scaleT` q <+> (zero :< fmap (<.> q) ps)
#else
  -- Works even for recursive anbn examples.
  (a :< dp) <.> ~q@(b :< dq)
    | isZero a  = zero :< fmap (<.> q) dp
    | otherwise = a <.> b :< unionWith (<+>) (fmap (<.> q) dp) (fmap (scaleT a) dq)
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
  single w = product [zero :< singleton c one | c <- w]
  -- single = product . map symbol
  --  where
  --    symbol c = zero :< singleton c one

instance OD c s => Decomposable (Trie c s) (Map c) s where
  (<:) = (:<)
  atEps (a :< _) = a
  deriv (_ :< d) = d

{--------------------------------------------------------------------
    Temporary for testing
--------------------------------------------------------------------}

type T = Trie Char Bool
