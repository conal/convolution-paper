{-# LANGUAGE CPP #-}

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Miscellany

module Misc where

import Control.Applicative (liftA2)

infixl 7 :*
infixl 6 :+

type (:*)  = (,)
type (:+)  = Either

type Unop a = a -> a

bool :: a -> a -> Bool -> a
bool t e b = if b then t else e


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
  ss >>= f = joinS (fmap f ss)
  -- (s :# ss') >>= f = let (b :# _) = f s in b :# (ss' >>= f)

joinS :: Stream (Stream a) -> Stream a
joinS ((a :# _) :# ss') = a :# joinS ss'
