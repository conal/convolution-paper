{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Languages as functions to semirings

module Fun where

import Prelude hiding (sum,product)

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

newtype FunTo b a = FunTo (a -> b)

instance Semiring s => Semiring (FunTo s [c]) where
  zero = FunTo (const zero)
  one = FunTo (boolVal . null)
  FunTo f <+> FunTo g = FunTo (\ x -> f x <+> g x)
  FunTo f <.> FunTo g = FunTo (\ x -> sum [ f u <.> g v | (u,v) <- splits x ] )

instance Semiring s => ClosedSemiring (FunTo s [c])

instance (Semiring s, Eq b) => HasSingle (FunTo s b) b where
  single x = FunTo (boolVal . (== x))

instance HasDecomp (FunTo s [c]) c s where
  atEps (FunTo f) = f []
  deriv c (FunTo f) = FunTo (f . (c :))

{--------------------------------------------------------------------
    Regular expressions
--------------------------------------------------------------------}

infixl 6 :<+>
infixl 7 :<.>

-- | Regular expression
data RegExp c a =
    Char c
  | Value a
  | RegExp c a :<+> RegExp c a
  | RegExp c a :<.> RegExp c a
  | Closure (RegExp c a)
 deriving (Show,Eq)

instance Semiring a => Semiring (RegExp c a) where
  zero  = Value zero
  one   = Value one
  (<+>) = (:<+>)
  (<.>) = (:<.>)

instance Semiring a => ClosedSemiring (RegExp c a) where
  closure = Closure

instance (Functor f, Foldable f, Semiring a) => HasSingle (RegExp c a) (f c) where
  single = product . fmap Char

instance (Eq c, ClosedSemiring a) => HasDecomp (RegExp c a) c a where
  atEps (Char _)    = zero
  atEps (Value a)   = a
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Closure p) = closure (atEps p)
  
  deriv c (Char c') | c == c'   = one
                    | otherwise = zero
  deriv _ (Value _)             = zero
  deriv c (p :<+> q)            = deriv c p <+> deriv c q
  deriv c (p :<.> q)            = Value (atEps p) <.> deriv c q <+> deriv c p <.> q
  deriv c (Closure p)           = deriv c (p <.> Closure p) -- since deriv c one = zero
                                  -- deriv c (one <+> p <.> Closure p)

-- | Interpret a regular expression
regexp :: (ClosedSemiring a, HasSingle a [c]) => RegExp c a -> a
regexp (Char c)      = single [c]
regexp (Value a)     = a
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Closure u)   = closure (regexp u)

{--------------------------------------------------------------------
    List trie with finite maps
--------------------------------------------------------------------}

infix 1 :|
data Trie c s = s :| Map c (Trie c s) deriving Show

scaleT :: (Ord c, DetectableZero s) => s -> Trie c s -> Trie c s
scaleT s _ | isZero s = zero
scaleT s (e :| ts) = (s <.> e) :| fmap (scaleT s) ts

inTrie :: (Ord c, DetectableZero s) => Trie c s -> [c] -> s
inTrie (e :| _ ) [] = e
inTrie (_ :| ds) (c:cs) = inTrie (ds `mat` c) cs

mat :: (Ord c, Semiring a) => Map c a -> c -> a
m `mat` c = M.findWithDefault zero c m

trieFunTo :: (Ord c, DetectableZero s) => Trie c s -> FunTo s [c]
trieFunTo = FunTo . inTrie

instance (Ord c, DetectableZero s) => Semiring (Trie c s) where
  zero = zero :| M.empty
  one  = one  :| M.empty
  (a :| ps') <+> (b :| qs') = (a <+> b) :| M.unionWith (<+>) ps' qs'
  -- Wedges for recursive anbn examples with the lazy pattern. (??)
  (a :| ps') <.> ~q@(b :| qs') = (a <.> b) :| M.unionWith (<+>) us vs
   where
     us = fmap (<.> q) ps'
     vs = fmap (scaleT a) qs'

instance (Ord c, DetectableZero s) => ClosedSemiring (Trie c s) where
  closure (_ :| ds) = q where q = one :| fmap (<.> q) ds

instance (Ord c, DetectableZero s) => HasSingle (Trie c s) [c] where
  single = product . map symbol
   where
     symbol c = zero :| M.singleton c one

instance (Ord c, DetectableZero s) => HasDecomp (Trie c s) c s where
  atEps (a :| _) = a
  deriv c (_ :| ds) = ds `mat` c
