-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Miscellany

module Misc where

infixl 7 :*
infixl 6 :+

type (:*)  = (,)
type (:+)  = Either

type Unop a = a -> a

bool :: a -> a -> Bool -> a
bool t e b = if b then t else e

-- All ways of splitting a given list (inverting |(<>)|).
splits :: [a] -> [([a],[a])]
splits []     = [([],[])]
splits (a:as) = ([],a:as) : [((a:l),r) | (l,r) <- splits as]

-- splits as@(a:as') = ([],as) : map (first (a:)) (splits as')

-- Equivalently
splits' :: [a] -> [([a],[a])]
splits' as = ([],as) : go as
 where
   go []       = []
   go (a:as')  = [((a:l),r) | (l,r) <- splits' as']
