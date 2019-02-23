{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import GHC.Natural (Natural)
-- import Data.Map (Map)
-- import qualified Data.Map as M
import Data.List (intercalate,intersperse)

import Misc ((:*))
import Semi

import MMap (Map)  -- like Data.Map but better Monoid instance
import qualified MMap as M

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
       | otherwise = showsPrec 6 b . {- showString "*" . -} xs
      where
        xs | i == 0    = id
           | i == 1    = showString "x"
           | otherwise = showString "x^" . showsPrec 8 i

eval1 :: Semiring b => Poly1 b -> b -> b
eval1 (Poly1 m) z = sum [b <.> z^i | (i,b) <- M.toList m]

type P1 = Poly1 Int

-- >>> single 1 <+> value 3 :: P1  -- x+3
-- x + 3
-- >>> (single 1 <+> value 3)^2 :: P1
-- x^2 + 6x + 9

type P2 = Map (N :* N)

x2,y2 :: P2 Int
x2 = single (1,0)
y2 = single (0,1)

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

#if 0

type Term k b = (b, Map k N)

showsPrecTerm :: forall k b. (Ord k, Show b, DetectableOne b)
              => Map k String -> Int -> Term k b -> ShowS
showsPrecTerm names d (b,m) = showParen (d >= 7) $
  (if isOne b then id else showsPrec 7 b . showString " ") .
  foldr (.) id (intersperse (showString " ") (factor <$> M.toList m))
 where
   factor :: (k,N) -> ShowS
   factor (k,n) | n == 0    = id
                | n == 1    = name
                | otherwise = name . showString "^" . showsPrec 8 n
    where
      name = showsPrec 9 (M.findWithDefault "?" k names)

-- newtype Poly n b = Poly (Map (Map n N) b) deriving
--   (Additive, Semiring, Functor, Indexable n, HasSingle n)

-- instance (DetectableOne b, Show b) => Show (Poly n b) where
--   showsPrec d (Poly m) = showParen (d >= 6) $
--      foldr (.) id (intersperse (showString " + ") (term <$> M.toDescList m))
--    where
--      term :: (N,b) -> ShowS
--      term (Sum i, b)
--        | i == 0    = showsPrec 6 b
--        | isOne b   = xs
--        | otherwise = shows b . showString "*" . xs
--       where
--         xs | i == 0    = id
--            | i == 1    = showString "x"
--            | otherwise = showString "x^" . showsPrec 8 i


#endif

-- Polynomials with named "variables"
newtype Poly b = Poly { unPoly :: Map (Map String N) b } deriving
  (Additive, Semiring, Functor, Indexable n, HasSingle n)

instance (DetectableOne b, Show b) => Show (Poly b) where
  showsPrec d (Poly m) = showParen (d >= 6) $
     foldr (.) id (intersperse (showString " + ") (term <$> M.toDescList m))
   where
     term :: (Map String N,b) -> ShowS
     term (pows, b)
       | all (== 0) pows = showsPrec 6 b
       | isOne b = xs
       | otherwise = showsPrec 6 b . {- showString "*" . -} xs
      where
        xs = foldr (.) id (factor <$> M.toAscList pows)
        factor (name,Sum i)
          | i == 0    = id
          | i == 1    = showString name
          | otherwise = showString name . showString "^" . showsPrec 8 i

-- TODO: try changing isZero for Map to be 'all isZero'. Might wedge on recursive examples.

x,y :: Poly Int
x = single (single "x")
y = single (single "y")

-- >>> x <+> y
-- y + x
-- >>> (x <+> y)^2
-- y^2 + x^2 + 2xy
-- >>> (x <+> y)^5
-- y^5 + x^5 + 5x^4y + 10x^3y^2 + 10x^2y^3 + 5xy^4

