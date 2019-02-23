{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import GHC.Natural (Natural)
import Data.Map (Map)
import qualified Data.Map as M
import Data.List (intercalate,intersperse)

import Misc ((:*))
import Semi

newtype Poly1 b = Poly1 (Map N b) deriving
  (Additive, Semiring, Functor, Indexable n, HasSingle n)

instance (DetectableOne b, Show b) => Show (Poly1 b) where
  showsPrec d (Poly1 m) = showParen (d >= 6) $
     foldr (.) id (intersperse (showString " + ") (term <$> M.toDescList m))
   where
     term :: (N,b) -> ShowS
     term (Sum i, b)
       | i == 0    = showsPrec 6 b
       | isOne b   = xs
       | otherwise = shows b . showString "*" . xs
      where
        xs | i == 0    = id
           | i == 1    = showString "x"
           | otherwise = showString "x^" . showsPrec 8 i

eval1 :: Semiring b => Poly1 b -> b -> b
eval1 (Poly1 m) x = sum [b <.> x^i | (i,b) <- M.toList m]

type P1 = Poly1 Int

-- >>> single 1 <+> value 3 :: P1  -- x+3
-- x + 3
-- >>> (single 1 <+> value 3)^2 :: P1
-- x^2 + 6*x + 9

type P2 = Map (N :* N)

x2,y2 :: P2 Int
x2 = M.singleton (1,0) one
y2 = M.singleton (0,1) one

-- >>> x2
-- fromList [((Sum 1,Sum 0),1)]
-- >>> y2
-- fromList [((Sum 0,Sum 1),1)]
-- >>> x2 <+> y2
-- fromList [((Sum 0,Sum 1),1),((Sum 1,Sum 0),1)]
-- >>> (x2 <+> y2)^2
-- fromList [((Sum 0,Sum 2),1),((Sum 1,Sum 1),2),((Sum 2,Sum 0),1)]

type P2' = Map (Map Bool N)

-- showPoly :: Map n String -> Map (Map n N) -> String
-- showPoly names m = intercalate " + " (term <$> M.toList m)
--  where
--    term 

-- Polynomials with named "variables"
type PolyS = Map String


-- type Vars = Map 

-- >>> 
