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
