-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Generalized "languages", which is mostly Semiring & friends

#NOTUSED

module Language where

import Semi

oneBool :: Additive x => (a -> x) -> a -> Bool -> x
oneBool _ _ False = zero
oneBool f a True  = f a

equal' :: (Eq a, Additive b) => a -> b -> a -> b
equal' a b a' = if a == a' then b else zero

equal :: (Eq a, Semiring b) => a -> a -> b
equal a = equal' a one

-- >>> splits (4 :: N)
-- [(Sum 0,Sum 4),(Sum 1,Sum 3),(Sum 2,Sum 2),(Sum 3,Sum 1),(Sum 4,Sum 0)]

{--------------------------------------------------------------------
    Temporary hack
--------------------------------------------------------------------}

-- allVals :: [c]
-- allVals = error "allVals not defined"
