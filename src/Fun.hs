{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -Wno-orphans #-} -- TEMP for Stream

-- | Languages as functions to semirings

module Fun where

import Prelude hiding (sum,product)

import Control.Applicative (liftA2)
import Control.Arrow (second,(***))
import Text.Show.Functions ()  -- for Decomp
import GHC.Natural (Natural)
import Data.Map
  ( Map,toList,fromListWith,empty,singleton,insert,unionWith
  , unionsWith,mapKeys,findWithDefault,keysSet )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor.Identity (Identity(..))

import Misc
import Language
import Constrained

{--------------------------------------------------------------------
    Flipped functions / generalized predicates
--------------------------------------------------------------------}

infixl 1 <--
newtype b <-- a = F { unF :: a -> b }

instance Show (b <-- a) where show = const "<F>"

instance (Splittable a, Semiring s) => Semiring (s <-- a) where
  zero = F (const zero)
  one = F (fromBool . isEmpty)
  F f <+> F g = F (\ w -> f w <+> g w)
  F f <.> F g = F (\ w -> sum [ f u <.> g v | (u,v) <- splits w ] )

instance Semiring s => StarSemiring (s <-- [c])

instance (Semiring b, Eq a) => HasSingle a b (b <-- a) where
  single a = F (equal a)

instance Semiring s => Semimodule s (s <-- a) where
  s `scale` F f = F (\ a -> s <.> f a) 
  -- s `scale` F f = F ((s <.>) . f) 

instance Semiring b => Decomposable (b <-- [c]) ((->) c) b where
  -- b <: h = F (b <: unF . h)

  -- b <: h = F f where  f []      = b
  --                     f (c:cs)  = unF (h c) cs

  -- b <: h = F f
  --   where
  --     f []   = b
  --     f (c:cs) = unF (h c) cs

  b <: h = F (\ case []   -> b
                     c:cs -> unF (h c) cs)

  atEps (F f) = f mempty
  deriv (F f) = \ c -> F (\ cs -> f (c:cs))

instance Semiring b => Decomposable (b <-- N) Identity b where
  b <: Identity (F f) = F (\ i -> if i == 0 then b else f (i - 1))
  atEps (F f) = f 0
  deriv (F f) = Identity (F (f . (1 +)))

-- The Functor and Applicative instances exist but are not computable.

instance Semiring b => FunctorC ((<--) b) where
  type Ok ((<--) b) a = Eq a
  fmapC h (F f) = F (\ w -> undefined h f w)

instance Semiring b => ApplicativeC ((<--) b) where
  pureC = single
  liftA2C h (F f) (F g) = F (\w -> undefined h f g w)

-- Move elsewhere:

-- value :: (Monoid a, Eq a) => b -> (b <-- a)
-- value b = F (\ x -> if x == mempty then b else zero)

-- infix 1 +->
-- (+->) :: (DetectableZero s, Eq w, Splittable w) => s -> w -> (s <-- w)
-- a +-> b = a .> single b


{--------------------------------------------------------------------
    Flipped finite maps
--------------------------------------------------------------------}

newtype b :<-- a = M (Map a b) deriving Show

mapTo :: (Ord a, Semiring b) => (b :<-- a) -> (b <-- a)
mapTo (M m) = F (\ a -> M.findWithDefault zero a m)

instance Semiring s => Semimodule s (s :<-- a) where
  s `scale` M m = M (fmap (s <.>) m)

type SRM b = DetectableZero b

instance (Monoid a, Ord a, SRM b) => Semiring (b :<-- a) where
  zero = M empty
  one = single mempty
  -- one = M (singleton mempty one)
  M p <+> M q = M (unionWith (<+>) p q)

  -- M p <.> M q = M (fromListWith (<+>)
  --                    [(u <> v, s <.> t) | (u,s) <- toList p, (v,t) <- toList q])

  M p <.> M q = sum [u <> v +-> s <.> t | (u,s) <- toList p, (v,t) <- toList q]

instance Semiring s => HasSingle a s (s :<-- a) where
  single a = M (singleton a one)

instance (Ord c, SRM s) => Decomposable (s :<-- [c]) (Map c) s where
  b <: d = M (insert [] b (unionsWith (<+>)
                            [ mapKeys (c:) css | (c,M css) <- toList d ]))
  atEps (M p) = p ! []
              -- findWithDefault zero [] p
  deriv (M p) = fromListWith (<+>) [(c, M (singleton cs s)) | (c:cs,s) <- toList p]

instance SRM b => FunctorC ((:<--) b) where
  type Ok ((:<--) b) a = (Ord a, Monoid a)
  fmapC h (M p) = sum [h a +-> b | (a,b) <- toList p]
  -- fmapC h (M p) = M (fromListWith (<+>) [(h a, b) | (a,b) <- toList p])

-- The Monoid constraint here is for Semiring (b :<-- a), but really just for
-- one and (<.>), which we're not using. TODO: factor Additive out of Semiring,
-- and drop the Monoid requirement here and for Additive (b :<-- a). I'll have
-- to return to defining my own classes. Tip my hat to semiring-num.

instance SRM b => ApplicativeC ((:<--) b) where
  pureC = single
  liftA2C h (M p) (M q) =
    sum [ h a b +-> s <.> t | (a,s) <- toList p, (b,t) <- toList q]
  -- liftA2C h (M p) (M q) =
  --   M (fromListWith (<+>) [(h a b, s <.> t) | (a,s) <- toList p, (b,t) <- toList q])

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

instance Semiring s => Semimodule s (Resid c s) where
  s `scale` Resid f = Resid (map (second (s <.>)) . f)

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

instance Eq s => HasSingle [s] (Resid s) where
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
  | Star (RegExp c s)
 deriving (Show,Eq)

instance Semiring s => Semimodule s (RegExp c s) where
  scale s = go
   where
     go (Char c) = Char c
     go (Value s') = Value (s <.> s')
     go (u :<+> v) = go u <+> go v
     go (u :<.> v) = go u <.> go v
     go (Star u)   = star (go u)

instance Semiring s => Semiring (RegExp c s) where
  zero  = Value zero
  one   = Value one
  (<+>) = (:<+>)
  (<.>) = (:<.>)

instance Semiring s => StarSemiring (RegExp c s) where
  star = Star

instance Semiring s => HasSingle [c] s (RegExp c s) where
  single = product . map Char

#if 0

scaleRE :: DetectableZero s => s -> RegExp c s -> RegExp c s
scaleRE s e | isZero s  = zero
            | otherwise = Value s <.> e

instance (Ord c, StarSemiring s, DetectableZero s) => Decomposable (RegExp c s) (Map c) s where
  e <: d = Value e <+> sum [ single [c] <.> dc | (c,dc) <- toList d ]
  atEps (Char _)    = zero
  atEps (Value s)   = s
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Star p) = star (atEps p)
  
  deriv (Char c')  = single c'
  deriv (Value _)  = empty
  deriv (p :<+> q) = unionWith (<+>) (deriv p) (deriv q)

  deriv (p :<.> q) =
    unionWith (<+>) (fmap (<.> q) (deriv p)) (fmap (scaleRE (atEps p)) (deriv q))

  -- deriv (p :<.> q) c  = -- deriv p c <.> q <+> Value (atEps p) <.> deriv q c
  --                       atEps p `scaleRE` deriv q c <+> deriv p c <.> q

  -- deriv (p :<.> q) c  = -- deriv p c <.> q <+> Value (atEps p) <.> deriv q c
  --                       Value (atEps p) <.> deriv q c <+> deriv p c <.> q

  -- deriv (Star p) =
  --   fmap (\ d -> Value (star (atEps p)) <.> d <.> Star p) (deriv p)

  -- Testing hangs on a^nb^n.

  deriv (Star p) = fmap (\ d -> pc <.> d <.> Star p) (deriv p)
   where
     pc = Value (star (atEps p))

#else

instance (Eq c, StarSemiring s) => Decomposable (RegExp c s) ((->) c) s where
  e <: d = Value e <+> sum [ single [c] <.> d c | c <- allVals ]

  atEps (Char _)    = zero
  atEps (Value s)   = s
  atEps (p :<+> q)  = atEps p <+> atEps q
  atEps (p :<.> q)  = atEps p <.> atEps q
  atEps (Star p) = star (atEps p)
  
  deriv (Char c') c   = equal c' c
                        -- fromBool (c == c')
                        -- if c == c' then one else zero
  deriv (Value _) _   = zero
  deriv (p :<+> q) c  = deriv p c <+> deriv q c
  deriv (p :<.> q) c  = -- deriv p c <.> q <+> Value (atEps p) <.> deriv q c
                        Value (atEps p) <.> deriv q c <+> deriv p c <.> q
  deriv (Star p) c = -- The following version works even if the atEps term
                        -- comes first in deriv (p :<.> q) c
                        Value (star (atEps p)) <.> deriv p c <.> star p
                        -- See 2018-01-13 journal.
                        -- The following version converges if the atEps term
                        -- comes second in deriv (p :<.> q) c
                        -- deriv (p <.> Star p) c -- since deriv c one = zero
                        -- deriv c (one <+> p <.> Star p)

#endif

-- TODO: fix deriv c (Star p) to compute deriv p c and deriv c (Star p)
-- just once. Do a bit of inlining and simplification.

-- | Interpret a regular expression
regexp :: (StarSemiring x, Semiring s, HS x c s) => RegExp c s -> x
regexp (Char c)      = -- [c] +-> one
                       single [c]
regexp (Value s)     = value s
regexp (u  :<+>  v)  = regexp u <+> regexp v
regexp (u  :<.>  v)  = regexp u <.> regexp v
regexp (Star u)   = star (regexp u)

{--------------------------------------------------------------------
    Decomposition as language
--------------------------------------------------------------------}

-- -- Identity:
-- deFun :: ([c] -> b) -> ([c] -> b)
-- deFun f = f [] <: \ c cs -> f (c:cs)

infix 1 :<:
data Decomp c s = s :<: (c -> Decomp c s) deriving Show

scaleD :: (DetectableZero s, Eq c) => s -> Decomp c s -> Decomp c s
scaleD s = go
 where
   go (e :<: ts) = (s <.> e) :<: (go . ts)

instance (DetectableZero s, Eq c) => Semimodule s (Decomp c s) where
  scale = scaleD

-- instance Semiring s => Semimodule s (Decomp c s) where
--   scale s = go
--    where
--      go (s' :<: f) = (s <.> s') :<: go . f

-- TODO: remove Eq c constraints from the signature of scaleD and Decomp
-- instances below if I stop needing it.

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

instance (DetectableZero s, Eq c) => Semiring (Decomp c s) where
#if 0
  -- For the paper
  zero = zero :<: \ _c -> zero
  one  = one  :<: \ _c -> zero
  (a :<: dp) <+> (b :<: dq) = (a <+> b) :<: \ c -> dp c <+> dq c
  (a :<: dp) <.> ~q@(b :<: dq) = (a <.> b) :<: \ c -> a .< dq c <+> dp c <.> q
#elif 1
  zero = zero :<: zero
  one  = one  :<: zero
  (a :<: dp) <+> (b :<: dq) = a <+> b :<: dp <+> dq
#else
  zero = zero :<: const zero
  one  = one  :<: const zero
  (a :<: dp) <+> (b :<: dq) = (a <+> b) :<: liftA2 (<+>) dp dq
#endif
#if 1
  (a :<: dp) <.> q = a .> q <+> (zero :<: (<.> q) . dp)
#else
  (a :<: dp) <.> ~q@(b :<: dq) = (a <.> b) :<: liftA2 h dp dq
   where
     h u v = a .> v <+> u <.> q
#endif

instance (StarSemiring s, DetectableZero s, Eq c) => StarSemiring (Decomp c s) where
#if 1
  star (a :<: dp) = q where q = star a .> (one :<: (<.> q) .  dp)
#else
  -- See 2019-01-13 joural
  star (a :<: dp) = q
    where
      q = as :<: fmap h dp
      as = star a
      h d = as .> d <.> q
#endif

instance (DetectableZero s, Eq c) => HasSingle [c] s (Decomp c s) where
  single = foldr cons one
   where
     cons c x = zero :<: (\ c' -> if c' == c then x else zero)

instance (DetectableZero s, Eq c) => Decomposable (Decomp c s) ((->) c) s where
  (<:) = (:<:)
  atEps (a :<: _) = a
  deriv (_ :<: d) = d

type DC = Decomp Char Bool

-- >>> zero :: DC
-- False :<: <function>

-- >>> single "" :: DC
-- False :<: <function>

-- >>> single "pig" :: DC
-- <interactive>:908:2-7: error:
--     Variable not in scope: single :: [Char] -> DC

{--------------------------------------------------------------------
    List trie with finite maps
--------------------------------------------------------------------}

infix 1 :<
data Trie c b = b :< Map c (Trie c b) deriving Show

#if 0

instance FunctorC (Trie c) where
  fmapC h (s :< ts) = h s :< (fmapC.fmapC) h ts

instance ApplicativeC (Trie c) where
  pureC = single
  liftA2C h (a :< us) (b :< vs) = h a b :< (liftA2C.liftA2C) h us vs

-- Hm. I need Applicative (Map c). Define in Semiring.

-- Maybe we don't want these instances. Return to this question.

instance FunctorC (Map k)

instance ApplicativeC (Map k) where
  pureC = single
  liftA2C h u v =
    fromListWith (<+>)
      [h (u!k) (v!k) | k <- S.toList (keysSet u `S.union` keysSet v)]

-- TODO: use these instances!

#endif

type OD c s = (Ord c, DetectableZero s)

trimT :: OD c s => Int -> Trie c s -> Trie c s
trimT 0 _ = zero
trimT n (c :< ts) = c :< fmap (trimT (n-1)) ts

instance OD c s => Semimodule s (Trie c s) where

  scale s = go
   where
     go ~(e :< ts) = (s <.> e) :< fmap go ts

  -- s `scale` (b :< dq) = (s <.> b) :< fmap (s `scale`) dq

  -- s `scale` t = go t
  --  where
  --    go ~(e :< ts) = (s <.> e) :< fmap go ts

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
    (a <.> b) :< unionWith (<+>) (fmap (<.> q) dp) (fmap (a .>) dq)
#elif 0
  -- Wedges for recursive anbn examples even with the lazy pattern.
  (a :< dp) <.> ~q@(b :< dq) = (a <.> b) :< unionWith (<+>) us vs
   where
     us = fmap (<.> q) dp
     vs = fmap (a .>) dq
#elif 1
  -- Works even for recursive anbn examples.
  (a :< dp) <.> q = a .> q <+> (zero :< fmap (<.> q) dp)
#else
  -- Works even for recursive anbn examples.
  (a :< dp) <.> ~q@(b :< dq)
    | isZero a  = zero :< fmap (<.> q) dp
    | otherwise = a <.> b :< unionWith (<+>) (fmap (<.> q) dp) (fmap (a .>) dq)
#endif

-- instance OD c s => StarSemiring (Trie c s) where
--   -- Wrong
--   star (_ :< ds) = q where q = one :< fmap (<.> q) ds

instance (Ord c, StarSemiring s, DetectableZero s) => StarSemiring (Trie c s) where
#if 1
  -- Works
  star (a :< dp) = q where q = star a .> (one :< fmap (<.> q) dp)
#else
  -- Works
  -- See 2019-01-13 journal
  star (a :< dp) = q
    where
      q = as :< fmap h dp
      as = star a
      h d = as .> d <.> q
#endif

instance OD c s => HasSingle [c] s (Trie c s) where
#if 1
  single w = product (map symbol w) where symbol c = zero <: singleton c one
  -- single = product . map symbol
  --  where
  --    symbol c = zero :< singleton c one
#else
  -- More streamlined
  single = foldr cons one
   where
     cons c x = zero :< singleton c x
#endif


instance OD c s => Decomposable (Trie c s) (Map c) s where
  (<:) = (:<)
  atEps (a :< _) = a
  deriv (_ :< d) = d

{--------------------------------------------------------------------
    Streams
--------------------------------------------------------------------}

-- TODO: introduce a newtype wrapper, saving Stream b for behaving like N -> b.

streamF :: Stream b -> (b <-- N)
streamF bs = F (bs !)

-- TODO: give real instances for b <-- a, in terms of Splittable.

instance DetectableZero b => Semiring (Stream b) where
  zero = q where q = zero :# q
  one = one :# zero
  (u :# us') <+> (v :# vs') = (u <+> v) :# (us' <+> vs')
  (u :# us') <.> vs = (u .> vs) <+> (zero :# us' <.> vs)
  -- (u :# us') <.> vs@(v :# vs') = u <.> v :# u .> vs' <+> us' <.> vs

instance (StarSemiring b, DetectableZero b) => StarSemiring (Stream b) where
  star (a :# as) = q where q = star a .> (one :# as <.> q)

instance DetectableZero s => Semimodule s (Stream s) where
  s `scale` (b :# dq) = (s <.> b) :# (s `scale` dq)

{--------------------------------------------------------------------
    Polynomials
--------------------------------------------------------------------}

-- Polynomial represented by coefficient stream
type PS b = Stream b

-- Polynomial represented as a finite map
type PMN b = b :<-- N

type PFN b = b <-- N

pow :: Semiring b => b -> N -> b
pow b (Sum n) = product [b | _i <- [0 .. n-1]]

-- pow _ 0 = one
-- pow x n = x <.> pow x (n-1)

assocsPoly :: (Semiring p, Semimodule s p, HasSingle N s p, DetectableZero s)
           => [(Natural,s)] -> p
assocsPoly l = sum [Sum i +-> s | (i,s) <- l]

coeffsPoly :: (Semiring p, Semimodule s p, HasSingle N s p, DetectableZero s)
           => [s] -> p
coeffsPoly bs = assocsPoly ([0 ..] `zip` bs)

polyMap :: Semiring b => (b :<-- N) -> (b -> b)
polyMap (M m) x = sum [b <.> pow x i | (i, b) <- M.toList m]

-- TODO: efficient exponentiations via scan. Also generalizes nicely.

-- listToS :: ...
-- listToS bs x    = go one
--  where
--    go _  []     = zero
--    go xk (c:cs) = b * xk + go (

{--------------------------------------------------------------------
    Orphans
--------------------------------------------------------------------}

{--------------------------------------------------------------------
    Temporary for testing
--------------------------------------------------------------------}

-- type T = Trie Char Bool
