{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Languages as functions to semirings

module Fun where

import Prelude hiding (sum,product)

import Control.Applicative (liftA2)
import Data.Map (Map)
import qualified Data.Map as M

import Misc
import Semiring

{--------------------------------------------------------------------
    Generalized predicates
--------------------------------------------------------------------}

-- The unique 'Semiring' homomorphism from 'Bool'.
boolVal :: Semiring s => Bool -> s
boolVal False = zero
boolVal True  = one

newtype FunTo s a = FunTo (a -> s)

instance Semiring s => Semiring (FunTo s [c]) where
  zero = FunTo (const zero)
  one = FunTo (boolVal . null)
  FunTo f <+> FunTo g = FunTo (\ w -> f w <+> g w)
  FunTo f <.> FunTo g = FunTo (\ w -> sum [ f u <.> g v | (u,v) <- splits w ] )

instance Semiring s => ClosedSemiring (FunTo s [c])

instance (Semiring s, Eq b) => HasSingle (FunTo s b) b where
  single x = FunTo (boolVal . (== x))

instance HasDecomp (FunTo s [c]) c s where
  atEps (FunTo f) = f []
  deriv c (FunTo f) = FunTo (f . (c :))

{--------------------------------------------------------------------
    Classic list-of-successes
--------------------------------------------------------------------}

-- Match a prefix of given string and yield corresponding suffixes for all
-- successful matches.
newtype Resid c s = Resid ([c] -> [([c], s)])

residFunTo :: Semiring s => Resid c s -> FunTo s [c]
residFunTo (Resid f) = FunTo (\ w -> sum [ s | (w',s) <- f w, null w' ])

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

instance Semiring s => ClosedSemiring (RegExp c s) where
  closure = Closure

instance (Functor f, Foldable f, Semiring s) => HasSingle (RegExp c s) (f c) where
  single = product . fmap Char

instance (Eq c, ClosedSemiring s) => HasDecomp (RegExp c s) c s where
  atEps (Char _)    = zero
  atEps (Value s)   = s
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Closure p) = closure (atEps p)
  
  deriv c (Char c')   = boolVal (c == c')
                        -- if c == c' then one else zero
  deriv _ (Value _)   = zero
  deriv c (p :<+> q)  = deriv c p <+> deriv c q
  deriv c (p :<.> q)  = Value (atEps p) <.> deriv c q <+> deriv c p <.> q
  deriv c (Closure p) = deriv c (p <.> Closure p) -- since deriv c one = zero
                                  -- deriv c (one <+> p <.> Closure p)

-- | Interpret a regular expression
regexp :: (ClosedSemiring s, HasSingle s [c]) => RegExp c s -> s
regexp (Char c)      = single [c]
regexp (Value s)     = s
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Closure u)   = closure (regexp u)

{--------------------------------------------------------------------
    Decomposition as language
--------------------------------------------------------------------}

infix 1 :<:
data Decomp c s = s :<: (c -> Decomp c s)

scaleD :: DetectableZero s => s -> Decomp c s -> Decomp c s
scaleD s _ | isZero s = zero
scaleD s (e :<: ts) = (s <.> e) :<: (scaleD s . ts)

inDecomp :: Decomp c s -> ([c] -> s)
inDecomp (e :<: _ ) [] = e
inDecomp (_ :<: ds) (c:cs) = inDecomp (ds c) cs

-- A hopefully temporary hack for testing.
-- (Some of the tests show the language representation.)
instance Show (Decomp c s) where show _ = "<Decomp>"

decompFunTo :: Decomp c s -> FunTo s [c]
decompFunTo = FunTo . inDecomp

instance DetectableZero s => Semiring (Decomp c s) where
  zero = zero :<: const zero
  one  = one  :<: const zero
  (a :<: ps') <+> (b :<: qs') = (a <+> b) :<: liftA2 (<+>) ps' qs'
  (a :<: ps') <.> ~q@(b :<: qs') = (a <.> b) :<: liftA2 h ps' qs'
   where
     h p' q' = scaleD a q' <+> p' <.> q

instance DetectableZero s => ClosedSemiring (Decomp c s)

instance (DetectableZero s, Eq c) => HasSingle (Decomp c s) [c] where
  single = product . map symbol
   where
     symbol c = zero :<: (\ c' -> if c'==c then one else zero)

instance HasDecomp (Decomp c s) c s where
  atEps (a :<: _) = a
  deriv c (_ :<: ds) = ds c

{--------------------------------------------------------------------
    List trie with finite maps
--------------------------------------------------------------------}

infix 1 :|
data Trie c s = s :| Map c (Trie c s) deriving Show

type OD c s = (Ord c, DetectableZero s)

scaleT :: OD c s => s -> Trie c s -> Trie c s
scaleT s _ | isZero s = zero
scaleT s (e :| ts) = (s <.> e) :| fmap (scaleT s) ts

inTrie :: OD c s => Trie c s -> [c] -> s
inTrie (e :| _ ) [] = e
inTrie (_ :| ds) (c:cs) = inTrie (ds `mat` c) cs

mat :: (Ord c, Semiring a) => Map c a -> c -> a
m `mat` c = M.findWithDefault zero c m

trieFunTo :: OD c s => Trie c s -> FunTo s [c]
trieFunTo = FunTo . inTrie

instance OD c s => Semiring (Trie c s) where
  zero = zero :| M.empty
  one  = one  :| M.empty
  (a :| ps') <+> (b :| qs') = (a <+> b) :| M.unionWith (<+>) ps' qs'
#if 0
  -- Wedges for the recursive anbn examples even with the lazy pattern.
  (a :| ps') <.> ~q@(b :| qs') =
    (a <.> b) :| M.unionWith (<+>) (fmap (<.> q) ps') (fmap (scaleT a) qs')
#elif 0
  -- Wedges for recursive anbn examples even with the lazy pattern.
  (a :| ps') <.> ~q@(b :| qs') = (a <.> b) :| M.unionWith (<+>) us vs
   where
     us = fmap (<.> q) ps'
     vs = fmap (scaleT a) qs'
#elif 1
  -- Works even for recursive anbn examples.
  (a :| ps') <.> q = scaleT a q <+> (zero :| fmap (<.> q) ps')
#else
  -- Works even for recursive anbn examples.
  (a :| ps') <.> ~q@(b :| qs')
    | isZero a = zero :| fmap (<.> q) ps'
    | otherwise = a <.> b :| M.unionWith (<+>) (fmap (<.> q) ps') (fmap (scaleT a) qs')
#endif

-- TODO: Map as semiring

instance OD c s => ClosedSemiring (Trie c s) where
  closure (_ :| ds) = q where q = one :| fmap (<.> q) ds

instance OD c s => HasSingle (Trie c s) [c] where
  single = product . map symbol
   where
     symbol c = zero :| M.singleton c one

instance OD c s => HasDecomp (Trie c s) c s where
  atEps (a :| _) = a
  deriv c (_ :| ds) = ds `mat` c
