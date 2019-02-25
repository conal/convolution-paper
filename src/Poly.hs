-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import Data.List (intersperse,sortOn) -- intercalate,
import GHC.Exts(IsString(..))
-- import GHC.Natural (Natural)
-- import Data.Map (Map)
-- import qualified Data.Map as M
-- import qualified Data.Foldable as F

import Misc ((:*))
import Semi

import MMap (Map)  -- like Data.Map but better Monoid instance
import qualified MMap as M

newtype Name = Name String deriving (Eq,Ord)

instance Show Name where show (Name s) = s
instance IsString Name where fromString = Name

newtype Poly1 b = Poly1 (Map N b) deriving
  (Additive, Semiring, Functor, Indexable N b, HasSingle N b)

-- data Pow b n = Pow b n  -- b * x^n

-- instance Show (Pow b n) where
--   showsPrec d (Pow b n) =
--   | isZero n  = id
--   | isOne  n  = showsPrec d b
--   | otherwise = showsPrec 8 b . showString "^" . showsPrec 8 n


-- TODO: eliminate in favor of Show (Pow b n)
showPow :: (Show b, Show n, DetectableZero n, DetectableOne n) => b -> n -> ShowS
showPow b n
  | isZero n  = id
  | isOne  n  = showsPrec 7 b
  | otherwise = showsPrec 8 b . showString "^" . showsPrec 8 n

instance (DetectableZero b, DetectableOne b, Show b) => Show (Poly1 b) where
  showsPrec d (Poly1 m) = showParen (d >= 6) $
     foldr (.) id (intersperse (showString " + ") (term <$> M.toDescList m))
   where
     term :: (N,b) -> ShowS
     -- term (Sum i, b) = b `showTimes'` Pow (Name "x") i
     term (Sum i, b)  -- b * x^i
       | isZero i  = sb
       | isZero b  = sb -- zero
       | isOne  b  = xs
       | otherwise = sb . showTimes . xs
      where
        sb = showsPrec 6 b
        xs = showPow (Name "x") i

showTimes :: ShowS
showTimes = showString " * "
-- showTimes = showString " "
-- Always generate "*", but suppress it in the paper. Looks great.

showTimes' :: (Show b, Show x, DetectableOne x, DetectableZero b, DetectableOne b)
           => b -> x -> ShowS
showTimes' b x  -- b * x
  | isZero b  = b' -- zero
  | isOne  x  = b'
  | isOne  b  = x'
  | otherwise = b' . showTimes . x'
 where
   b' = showsPrec 6 b
   x' = showsPrec 6 x

eval1 :: Semiring b => Poly1 b -> b -> b
eval1 (Poly1 m) z = sum [b <.> z^i | (i,b) <- M.toList m]

-- >>> let p = single 1 <+> value 3 :: Poly1 Z
-- >>> p
-- x + 3
-- 
-- >>> p^3
-- x^3 + 9 * x^2 + 27 * x + 27
-- 
-- >>> p^5
-- x^5 + 15 * x^4 + 90 * x^3 + 270 * x^2 + 405 * x + 243

type P2 = Map (N :* N)

x2,y2 :: P2 Int
x2 = single (1,0)
y2 = single (0,1)

-- >>> x2
-- M (fromList [((Sum 1,Sum 0),1)])
-- >>> y2
-- M (fromList [((Sum 0,Sum 1),1)])
-- >>> x2 <+> y2
-- M (fromList [((Sum 0,Sum 1),1),((Sum 1,Sum 0),1)])
-- >>> (x2 <+> y2)^2
-- M (fromList [((Sum 0,Sum 2),1),((Sum 1,Sum 1),2),((Sum 2,Sum 0),1)])

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
newtype PolyM b = PolyM { unPolyM :: Map (Map Name N) b } deriving
  (Additive, Semiring, Functor, Indexable (Map Name N) b, HasSingle (Map Name N) b)

instance (DetectableZero b, DetectableOne b, Show b) => Show (PolyM b) where
  showsPrec d (PolyM m) = showParen (d >= 6) $
     foldr (.) id (intersperse (showString " + ")
                    -- TODO: better ordering
                    (term <$> sortOn (M.keys . fst) (M.toDescList m)))
   where
     term :: (Map Name N,b) -> ShowS
     term (pows, b)
       | all (== 0) pows = sb
       | isZero b        = sb
       | isOne b         = xs
       | otherwise       = sb . showTimes . xs
      where
        sb = showsPrec 6 b
        xs = foldr (.) id (intersperse showTimes (factor <$> M.toAscList pows))
        factor (name,Sum i) = showPow name i

-- TODO: try changing isZero for Map to be 'all isZero'. Might wedge on recursive examples.

-- varM :: Name -> PolyM Z
varM :: Semiring b => Name -> PolyM b
varM = single . single

-- >>> let { x = varM @Z "x" ; y = varM @Z "y" ; z = varM @Z "z" }
-- >>> let { p = x <+> y ; q = p <+> z }
-- 
-- >>> p
-- x + y
-- >>> p^2
-- x^2 + 2 * x * y + y^2
-- >>> p^5
-- x^5 + 5 * x^4 * y + 10 * x^3 * y^2 + 10 * x^2 * y^3 + 5 * x * y^4 + y^5
-- 
-- >>> q
-- x + y + z
-- >>> q^2
-- x^2 + 2 * x * y + 2 * x * z + y^2 + 2 * y * z + z^2
-- >>> q^3
-- x^3 + 3 * x^2 * y + 3 * x * y^2 + 6 * x * y * z + 3 * x^2 * z + 3 * x * z^2 + y^3 + 3 * y^2 * z + 3 * y * z^2 + z^3

-- >>> p <.> q
-- x^2 + 2 * x * y + x * z + y^2 + y * z

#if 0

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

-- TODO: supply variable names from a default list

#endif
