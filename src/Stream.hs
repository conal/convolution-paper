-- | Streams (infinite lists)

module Stream where

import Control.Applicative (liftA2)

import Constrained

infixr 1 :#
data Stream b = b :# Stream b

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
