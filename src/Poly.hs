-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import Data.List (intersperse,sortOn) -- intercalate,
import GHC.Exts(IsString(..))

import Misc ((:*))
import Semi

import MMap (Map)  -- like Data.Map but better Monoid instance
import qualified MMap as M

{--------------------------------------------------------------------
    Show utilities
--------------------------------------------------------------------}

compose :: [a -> a] -> (a -> a)
compose = foldr (.) id

showIter :: Show b => Int -> String -> Int -> [b] -> ShowS
showIter inner op outer bs =
  showParen (outer > inner) $
  compose (intersperse (showString op) (showsPrec inner <$> bs))

-- TODO: check for empty bs and for singleton bs

showSum, showProd :: Show b => Int -> [b] -> ShowS
showSum  = showIter 6 " + "
showProd = showIter 7 " * "

{--------------------------------------------------------------------
    Syntactic representations
--------------------------------------------------------------------}

newtype Name = Name String deriving (Eq,Ord)

instance DetectableZero Name where isZero = const False
instance DetectableOne  Name where isOne  = const False

instance Show     Name where show (Name s) = s
instance IsString Name where fromString = Name

data Pow b n = Pow b n  -- b * x^n

instance (DetectableOne b, DetectableZero n) => DetectableOne (Pow b n) where
  isOne (Pow b n) = isOne b || isZero n

instance (Show n, Show b, DetectableZero n, DetectableOne n, DetectableOne b)
      => Show (Pow b n) where
  showsPrec d p@(Pow b n)
    | isOne p   = showString "1"
    | isOne n   = showsPrec d b
    | otherwise = showParen (d >= 8) $
                  showsPrec 8 b . showString "^" . showsPrec 8 n

-- >>> Pow (Name "z") 5 :: Pow Name N
-- z^5

data Pows a = Pows (Map a N)

instance DetectableOne (Pows a) where
  isOne (Pows m) = all isZero m

-- TODO: try changing isZero for Map to be 'all isZero'. Might wedge on recursive examples.

instance (Show b, DetectableZero b, DetectableOne b) => Show (Pows b) where
  showsPrec d p@(Pows m)
    | isOne p   = showString "1"
    | otherwise = showProd d (uncurry Pow <$> M.toList m)

-- >>> Pows ((Name "x" +-> 2) <+> (Name "y" +-> 3) :: Map Name N)
-- x^2 * y^3

data Term b x = Term b x  -- b * x

instance (Show b, Show x, DetectableOne x, DetectableZero b, DetectableOne b)
      => Show (Term b x) where
  showsPrec d (Term b x)
    | isZero b || isOne x = showsPrec d b
    | isOne  b  = showsPrec d x
    | otherwise = showParen (d > 6) $
                  showsPrec 6 b . showString " * " . showsPrec 6 x

-- >>> Term 7 (Pows ((Name "x" +-> 2) <+> (Name "y" +-> 3))) :: Term Z (Pows Name)
-- 7 * x^2 * y^3

data Terms b = Terms [b]

instance Show b => Show (Terms b) where showsPrec d (Terms bs) = showSum d bs

{--------------------------------------------------------------------
    Polynomials
--------------------------------------------------------------------}

newtype Poly1 b = Poly1 (Map N b) deriving
  (Additive, Semiring, Functor, Indexable N b, HasSingle N b)

instance (DetectableZero b, DetectableOne b, Show b) => Show (Poly1 b) where
  showsPrec d (Poly1 m) = showsPrec d (Terms (term <$> M.toDescList m))
   where
     term (i,b) = Term b (Pow (Name "x") i)

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
-- M (fromList [((1,0),1)])
-- >>> y2
-- M (fromList [((0,1),1)])
-- >>> x2 <+> y2
-- M (fromList [((0,1),1),((1,0),1)])
-- >>> (x2 <+> y2)^2
-- M (fromList [((0,2),1),((1,1),2),((2,0),1)])

type P2' = Map (Map Bool N)

-- Polynomials with named "variables"
newtype PolyM b = PolyM { unPolyM :: Map (Map Name N) b } deriving
  (Additive, Semiring, Functor, Indexable (Map Name N) b, HasSingle (Map Name N) b)

instance (DetectableZero b, DetectableOne b, Show b) => Show (PolyM b) where
  showsPrec d (PolyM m) =
    showsPrec d (Terms (term <$> sortOn (M.keys . fst) (M.toDescList m)))
   where
     term (p,b) = Term b (Pows p)

-- TODO: improve the sorting criterion

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
