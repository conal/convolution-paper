#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | List tries using Convo

module Cofree where

import Prelude hiding (sum,product)

import Data.Functor.Classes (Show1(..),showsPrec1)
import GHC.Exts (coerce)
import Data.Map (Map)
import qualified Data.Map as M

import Misc
import Constrained
import Semi

#ifdef EXAMPLES
import Examples
import ShareMap (ShareMap)
import Data.Set (Set)
import qualified Data.Set as S
#endif

-- #include "GenInstances.inc"

-- TODO: maybe rename Cofree to "Cofree". I'd use Ed's Cofree from the "free" library,
-- but he defined Key (Cofree f) = Seq (Key f), and I want [Key f]. Oh well.

-- Move elsewhere

infix 1 <:
(<:) :: b -> (c -> ([c] -> b)) -> ([c] -> b)
b <: h = \ case { [] -> b ; c:cs  -> h c cs }

-- -- Experiment
-- infix 1 <#
-- (<#) :: (Indexable ([c] -> b) h, Key h ~ c)
--      => b -> h ([c] -> b) -> ([c] -> b)
-- b <# h = \ case { [] -> b ; c:cs  -> (h ! c) cs }

-- | List trie, denoting '[c] -> b'
infix 1 :<
data Cofree h b = b :< h (Cofree h b) deriving Functor

#if 0
-- Swiped from Control.Comonad.Cofree
instance (Show1 f, Show a) => Show (Cofree f a) where showsPrec = showsPrec1
instance Show1 f => Show1 (Cofree f) where
  liftShowsPrec sp sl = go
    where
      goList = liftShowList sp sl
      go d (a :< ds) = showParen (d > 5) $
        sp 6 a . showString " :< " . liftShowsPrec go goList 5 ds
#else
instance (ConF Show h, Show b) => Show (Cofree h b) where
  showsPrec p (a :< ds) = showParen (p > 5) $
    showsPrec 1 a . showString " :< " . showsPrec 1 ds
#endif


-- instance Functor h => Functor (Cofree h) where
--   fmap f = go where go (a :< dp) = f a :< fmap go dp
--   -- fmap f (a :< dp) = f a :< (fmap.fmap) f dp
--   -- fmap f (a :< dp) = f a :< fmap (fmap f) dp

-- TODO: I probably want FunctorC h, and inherit Ok.
instance Functor h => FunctorC (Cofree h)

instance Indexable c (Cofree h b) (h (Cofree h b)) => Indexable [c] b (Cofree h b) where
  -- (b :< _ ) ! [] = b
  -- (_ :< ts) ! (k:ks) = ts ! k ! ks
  -- (b :< dp) ! w = case w of { [] -> b ; c:cs -> dp ! c ! cs }
  -- (!) (b :< dp) = b <: (!) (fmap (!) dp)
  (!) (b :< dp) = b <: (!) . (!) dp

instance Listable c (Cofree h b) (h (Cofree h b)) =>  Listable [c] b (Cofree h b) where
  toList = go []
   where
     go cs (a :< dp) =
       (cs,a) : concatMap (\ (c,t) -> go (c:cs) t) (toList dp)

instance (Additive (h (Cofree h b)), Additive b) => Additive (Cofree h b) where
  zero = zero :< zero
  (a :< dp) <+> (b :< dq) = a <+> b  :<  dp <+> dq

-- FunctorSemimodule(Cofree h)

-- instance (Functor h, Semiring b) => LeftSemimodule b (Cofree h b) where scale s = fmap (s <.>)

-- instance (Functor h, Semiring b) => LeftSemimodule b (Cofree h b) where
--   s `scale` (b :< dp) = s <.> b :< fmap (s `scale`) dp

instance (Functor h, Semiring b) => LeftSemimodule b (Cofree h b) where
  scale s = fmap (s <.>)
  -- scale s = go where go (b :< dp) = s <.> b :< fmap go dp

instance (Functor h, Additive (h (Cofree h b)), Semiring b, DetectableZero b, DetectableOne b) => Semiring (Cofree h b) where
  one = one :< zero
  (a :< dp) <.> q = a .> q <+> (zero :< fmap (<.> q) dp)

instance (Functor h, Additive (h (Cofree h b)), StarSemiring b, DetectableZero b, DetectableOne b) => StarSemiring (Cofree h b) where
  star (a :< dp) = q where q = star a .> (one :< fmap (<.> q) dp)

instance ( HasSingle c (Cofree h b) (h (Cofree h b)), Additive (h (Cofree h b))
         , Ord c, Semiring b )
      => HasSingle [c] b (Cofree h b) where
  w +-> b = foldr (\ c t -> zero :< c +-> t) (b :< zero) w
#if 0
  ws *-> b = fromBool eps
             <+> zero :< sum [ c +-> ws' *-> b | (c,ws') <- M.toList ders]
   where
     (eps,ders) = unconsSet ws
#else
  ws *-> b =
    fromBool eps <+>
    zero :< sum [ prefixes *-> suffix +-> b | (suffix,prefixes) <- M.toList ders']
   where
     (eps,ders') = unconsSet' ws
#endif

-- preimageM :: (Ord a, Ord b) => Map a b -> Map b (Set a)
-- preimageM m = sum [M.singleton b (S.singleton a) | (a,b) <- M.toList m]

-- unconsSet :: Ord c => Set [c] -> Bool :* Map c (Set [c])

-- unconsSet' :: Ord c => Set [c] -> Bool :* Map [c] (Set c)


instance (Additive (h (Cofree h b)), DetectableZero (h (Cofree h b)), DetectableZero b)
      => DetectableZero (Cofree h b) where
  isZero (a :< dp) = isZero a && isZero dp

instance (Functor h, Additive (h (Cofree h b)), DetectableZero b, DetectableZero (h (Cofree h b)), DetectableOne b)
      => DetectableOne (Cofree h b) where
  isOne (a :< dp) = isOne a && isZero dp

-- | Trim to a finite depth, for examination.
trim :: (Functor h, Additive (h (Cofree h b)), Additive b, DetectableZero b) => Int -> Cofree h b -> Cofree h b
trim 0 _ = zero
trim n (c :< ts) = c :< fmap (trim (n-1)) ts

-- To remove
unconsSet :: Ord c => Set [c] -> Bool :* Map c (Set [c])
unconsSet s =
  ( [] `S.member` s
  , sum [M.singleton c (S.singleton cs) | (c:cs) <- S.toList s]
  )

-- >>> unconsSet (S.fromList ["a","b","c","d"])
-- (False,fromList [('a',fromList [""]),('b',fromList [""]),('c',fromList [""]),('d',fromList [""])])

-- >>> unconsSet (S.fromList ["act","art","cat","car","","cart"])
-- (True,fromList [('a',fromList ["ct","rt"]),('c',fromList ["ar","art","at"])])

preimageM :: (Ord a, Ord b) => Map a b -> Map b (Set a)
preimageM m = sum [M.singleton b (S.singleton a) | (a,b) <- M.toList m]

-- Similar to Brzozowski's derivative-based decomposition, but with inverted
-- derivatives.
unconsSet' :: Ord c => Set [c] -> Bool :* Map [c] (Set c)
#if 0
unconsSet' s = ( [] `S.member` s
               , sum [M.singleton cs (S.singleton c) | (c:cs) <- S.toList s] )
#else
unconsSet' s = ( [] `S.member` s
               , preimageM (M.fromList [(c,cs) | c:cs <- S.toList s]) )
#endif

-- >>> preimageM


#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L = Cofree (Map Char) Bool

type LS = Cofree (ShareMap Char) Bool

-- >>> singleChar "abcd" :: LS
-- False :< SM (fromList [('a','d'),('b','d'),('c','d'),('d','d')]) (fromList [('d',(fromList "abcd",True :< SM (fromList []) (fromList [])))])

-- >>> letter :: LS
-- False :< SM (fromList [('a','z'),('b','z'),('c','z'),('d','z'),('e','z'),('f','z'),('g','z'),('h','z'),('i','z'),('j','z'),('k','z'),('l','z'),('m','z'),('n','z'),('o','z'),('p','z'),('q','z'),('r','z'),('s','z'),('t','z'),('u','z'),('v','z'),('w','z'),('x','z'),('y','z'),('z','z')]) (fromList [('z',(fromList "abcdefghijklmnopqrstuvwxyz",True :< SM (fromList []) (fromList [])))])

-- >>> pig :: LS
-- False :< SM (fromList [('p','p')]) (fromList [('p',(fromList "p",False :< SM (fromList [('i','i')]) (fromList [('i',(fromList "i",False :< SM (fromList [('g','g')]) (fromList [('g',(fromList "g",True :< SM (fromList []) (fromList [])))])))])))])
-- >>> pink :: LS
-- False :< SM (fromList [('p','p')]) (fromList [('p',(fromList "p",False :< SM (fromList [('i','i')]) (fromList [('i',(fromList "i",False :< SM (fromList [('n','n')]) (fromList [('n',(fromList "n",False :< SM (fromList [('k','k')]) (fromList [('k',(fromList "k",True :< SM (fromList []) (fromList [])))])))])))])))])
-- >>> pp :: LS
-- False :< SM (fromList [('p','p')]) (fromList [('p',(fromList "p",False :< SM (fromList [('i','i')]) (fromList [('i',(fromList "i",False :< SM (fromList [('g','g'),('n','n')]) (fromList [('g',(fromList "g",True :< SM (fromList []) (fromList []))),('n',(fromList "n",False :< SM (fromList [('k','k')]) (fromList [('k',(fromList "k",True :< SM (fromList []) (fromList [])))])))])))])))])

-- >>> pig :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< [])])])]
-- >>> pink :: L
-- False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])]
-- >>> pp :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])]

-- >>> pig :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< [])])])]
-- >>> pink :: L
-- False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])]
-- >>> pp :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])]

-- >>> trimT 3 as :: L
-- True :< [('a',True :< [('a',True :< [])])]
-- >>> trimT 3 ass :: L
-- True :< [('a',True :< [('a',True :< [])])]

-- >>> trimT 7 anbn :: L
-- True :< [('a',False :< [('a',False :< [('a',False :< [('b',False :< [('b',False :< [('b',True :< [])])])]),('b',False :< [('b',True :< [])])]),('b',True :< [])])]

-- >>> (pig :: L) ! ""
-- False
-- >>> (pig :: L) ! "pi"
-- False
-- >>> (pig :: L) ! "pig"
-- True
-- >>> (pig :: L) ! "piggy"
-- False

-- >>> (anbn :: L) ! ""
-- True
-- >>> (anbn :: L) ! "a"
-- False
-- >>> (anbn :: L) ! "ab"
-- True
-- >>> (anbn :: L) ! "aabb"
-- True
-- >>> (anbn :: L) ! "aaaaabbbbb"
-- True

#endif
