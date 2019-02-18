{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples

-- | Streams (infinite lists) with Decomposable

module DStream where

import Control.Applicative (Applicative(..))
import Data.Functor.Identity (Identity(..))

import Constrained
import Semi

#include "GenInstances.inc"

infixr 1 :#
data Stream b = b :# Stream b

instance Decomposable b Identity (Stream b) where
  b <: Identity bs = b :# bs
  decomp (b :# bs) = (b, Identity bs)

instance Functor Stream where fmap f (b :# bs) = f b :# fmap f bs

instance Applicative Stream where
#if 1
  pure b = q where q = b :# q
  liftA2 h = go where go (a :# as) (b :# bs) = h a b :# go as bs
#else
  pure b = b :# pure b
  liftA2 h (a :# as) (b :# bs) = h a b :# liftA2 h as bs
#endif

instance Monad Stream where
  -- (s :# ss') >>= f = let (b :# _) = f s in b :# (ss' >>= f)
  ss >>= f = joinS (fmap f ss)
   where
     joinS ((a :# _) :# ss') = a :# joinS ss'

instance FunctorC     Stream
instance ApplicativeC Stream
instance MonadC       Stream

-- {-# COMPLETE (:<:) :: Stream #-} -- won't parse
-- 
-- • Orphan COMPLETE pragmas not supported
--   A COMPLETE pragma must mention at least one data constructor
--   or pattern synonym defined in the same module.

ApplSemi(Stream)

instance Indexable N b (Stream b) where
  (b :# bs) ! n = if n == 0 then b else bs ! (n-1)

-- instance Indexable N b (Stream b) where
--   (b :# _)  ! 0 = b
--   (_ :# bs) ! n = bs ! (n-1)

-- instance Indexable N b (Stream b) where
--   (b :# _)  ! Sum 0 = b
--   (_ :# bs) ! Sum n = bs ! Sum (n-1)

type Stream' b = Decomp (Stream b)

-- instance Indexable N b (Stream' b) where
--   (b :# bs) ! n = if n == 0 then b else bs ! (n-1)

-- Functional dependency conflict with a definition in Semi:
--
-- instance (Decomposable b h x, Indexable c (Decomp x) (h (Decomp x)))
--       => Indexable [c] b (Decomp x) where
--   -- (b :<: dp) ! w = case w of { [] -> b ; c:cs -> dp ! c ! cs }
--   (!) = accept
