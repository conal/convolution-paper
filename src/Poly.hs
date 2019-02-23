{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import GHC.Natural (Natural)
import Data.Map (Map)
import qualified Data.Map as M
import Data.List (intercalate)

import Misc ((:*))
import Semi

newtype Poly1 b = Poly1 (Map N b) deriving
  (Additive, Semiring, HasSingle)

eval1 :: Semiring b => Poly1 b -> b -> b
eval1 (Poly1 m) x = sum [b <.> x^i | (i,b) <- M.toList m]

type P1 = Poly1 Int

showPoly1 :: (DetectableOne b, Show b) => Poly1 b -> String
showPoly1 (Poly1 m) = intercalate " + " (term <$> M.toDescList m)
 where
   term (Sum i, b)
     | i == 0    = show b
     | isOne b   = xs
     | otherwise = show b ++ "*" ++ xs
    where
      xs | i == 0    = ""
         | i == 1    = "x"
         | otherwise = "x^" ++ show i

-- >>> single 1 <+> value 3 :: P1  -- x+3
-- fromList [(Sum 0,3),(Sum 1,1)]
-- >>> (single 1 <+> value 3)^2 :: P1
-- fromList [(Sum 0,9),(Sum 1,6),(Sum 2,1)]

-- >>> showPoly1 ((single 1 <+> value 3)^2 :: P1)
-- "x^2 + 6*x + 9"

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
