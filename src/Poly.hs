{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import GHC.Natural (Natural)
-- import Data.Map (Map)
-- import qualified Data.Map as M
import Data.List (intercalate,intersperse,sortOn)
import qualified Data.Foldable as F

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

-- newtype PolyM n b = PolyM (Map (Map n N) b) deriving
--   (Additive, Semiring, Functor, Indexable n, HasSingle n)

-- instance (DetectableOne b, Show b) => Show (PolyM n b) where
--   showsPrec d (PolyM m) = showParen (d >= 6) $
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
newtype PolyM b = PolyM { unPolyM :: Map (Map String N) b } deriving
  (Additive, Semiring, Functor, Indexable n, HasSingle n)

instance (DetectableOne b, Show b) => Show (PolyM b) where
  showsPrec d (PolyM m) = showParen (d >= 6) $
     foldr (.) id (intersperse (showString " + ")
                    -- TODO: better ordering
                    (term <$> sortOn (M.keys . fst) (M.toDescList m)))
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

-- m :: Map (Map String N) b
-- M.toList m :: [(Map String N, b)]

-- fst :: (Map String N, b) -> Map String N
-- keys . fst

-- M.toList m :: [(Map String N, b)]

-- TODO: try changing isZero for Map to be 'all isZero'. Might wedge on recursive examples.

-- >>> x = single (single "x") :: PolyM Int
-- >>> y = single (single "y") :: PolyM Int
-- >>> x <+> y
-- x + y
-- >>> (x <+> y)^2
-- x^2 + 2xy + y^2
-- >>> (x <+> y)^5
-- x^5 + 5x^4y + 10x^3y^2 + 10x^2y^3 + 5xy^4 + y^5

-- >>> x = single (single "x") :: PolyM Int
-- >>> y = single (single "y") :: PolyM Int
-- >>> z = single (single "z") :: PolyM Int
-- >>> x <+> y <+> z
-- x + y + z
-- >>> (x <+> y <+> z)^2
-- x^2 + 2xy + 2xz + y^2 + 2yz + z^2
-- >>> (x <+> y <+> z)^5
-- x^5 + 5x^4y + 10x^3y^2 + 10x^2y^3 + 5xy^4 + 20x^3yz + 30x^2y^2z + 30x^2yz^2 + 20xy^3z + 30xy^2z^2 + 20xyz^3 + 5x^4z + 10x^3z^2 + 10x^2z^3 + 5xz^4 + y^5 + 5y^4z + 10y^3z^2 + 10y^2z^3 + 5yz^4 + z^5


newtype PolyF h b = PolyF { unPolyF :: Map (h N) b } deriving Functor

deriving instance (Ord (h N), Additive b) => Additive (PolyF h b)
deriving instance (Ord (h N), Monoid (h N), Semiring b) => Semiring (PolyF h b)
deriving instance (Ord (h N), Additive k) => Indexable k (PolyF h)
deriving instance (Ord (h N), Additive k) => HasSingle k (PolyF h)

instance (Foldable h, DetectableOne b, Show b) => Show (PolyF h b) where
  showsPrec d (PolyF m) = showParen (d >= 6) $
     foldr (.) id (intersperse (showString " + ") (term <$> M.toDescList m))
   where
     term :: (h N,b) -> ShowS
     term (pows, b)
       | all (== 0) pows = showsPrec 6 b
       | isOne b = xs
       | otherwise = showsPrec 6 b . {- showString "*" . -} xs
      where
        xs :: ShowS
        xs = foldr (.) id (factor <$> F.toList pows)
        factor (Sum i)
          | i == 0    = id
          | i == 1    = showString name
          | otherwise = showString name . showString "^" . showsPrec 8 i
        name = "?"

-- >>> x = single (single "x") :: PolyF (Map String) Int
-- >>> y = single (single "y") :: PolyF (Map String) Int
-- >>> x <+> y
-- ? + ?
-- >>> (x <+> y)^2
-- ?^2 + ?^2 + 2??
-- >>> (x <+> y)^5
-- ?^5 + ?^5 + 5?^4? + 10?^3?^2 + 10?^2?^3 + 5??^4

