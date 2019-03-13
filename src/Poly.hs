-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import Data.List (intersperse,sortOn) -- intercalate,
import GHC.Exts(IsString(..))
import Data.Functor.Identity (Identity(..))

-- import Misc ((:*))
import Semi
import Cofree (Cofree(..))

import MMap (Map)  -- like Data.Map but better Monoid instance
import qualified MMap as M

{--------------------------------------------------------------------
    Univariate polynomials
--------------------------------------------------------------------}

newtype Poly1 z = Poly1 z deriving
  ( Additive, Semiring, Indexable n b, Listable n b, HasSingle n b
  , Num )  -- , Functor

instance ( Show b, Ord b, Num b, D01 b, Listable n b z
         , Show n, DetectableZero n, DetectableOne n )
      => Show (Poly1 z) where
  showsPrec d (Poly1 m) = showsPrec d (Terms (term <$> toList m))
   where
     term (i,b) = Term b (Pow (Name "x") i)

-- instance ( DetectableZero b, DetectableOne b, Show b, Listable n b z
--          , Show n, DetectableZero n, DetectableOne n )
--       => Show (Poly1 z) where
--   showsPrec d (Poly1 m) = showsPrec d (Terms (term <$> toList m))
--    where
--      term (i,b) = Term b (Pow (Name "x") i)

type P1 b = Poly1 (Map N b)

poly1 :: (Listable N b z, Semiring b) => Poly1 z -> b -> b
poly1 (Poly1 m) z = sum [b <.> z^i | (i,b) <- toList m]

-- >>> let p = single 1 <+> value 3 :: Poly1 (Map N Z)
-- >>> p
-- 3 + x
-- 
-- >>> p^3
-- 27 + 27 * x + 9 * x^2 + x^3
-- 
-- >>> p^4
-- 81 + 108 * x + 54 * x^2 + 12 * x^3 + x^4
-- 
-- >>> p^5
-- 243 + 405 * x + 270 * x^2 + 90 * x^3 + 15 * x^4 + x^5
-- 
-- >>> p^9
-- 19683 + 59049 * x + 78732 * x^2 + 61236 * x^3 + 30618 * x^4 + 10206 * x^5 + 2268 * x^6 + 324 * x^7 + 27 * x^8 + x^9
-- 
-- >>> poly1 p 10
-- 13
-- >>> poly1 (p^3) 10
-- 2197
-- >>> (poly1 p 10)^3
-- 2197
-- 
-- >>> poly1 (p^5) 17 == (poly1 p 17)^5
-- True

-- >>> let p = 1 <+> value 3 :: Poly1 [Z]
-- >>> p
-- 3 + x
-- >>> p^3
-- 27 + 27 * x + 9 * x^2 + x^3
-- 
-- >>> p^4
-- 27 + 27 * x + 9 * x^2 + x^3
-- 
-- >>> p^5
-- 243 + 405 * x + 270 * x^2 + 90 * x^3 + 15 * x^4 + x^5
-- 
-- >>> p^9
-- 19683 + 59049 * x + 78732 * x^2 + 61236 * x^3 + 30618 * x^4 + 10206 * x^5 + 2268 * x^6 + 324 * x^7 + 27 * x^8 + x^9
-- 
-- >>> poly1 p 10
-- 13
-- >>> poly1 (p^3) 10
-- 2197
-- >>> (poly1 p 10)^3
-- 2197
-- 
-- >>> poly1 (p^5) 17 == (poly1 p 17)^5
-- True

-- >>> let p = single 1 <+> value 3 :: Poly1 (Cofree Maybe Z)
-- >>> p
-- 3 + x
-- >>> p^3
-- 27 + 27 * x + 9 * x^2 + x^3
-- 
-- >>> p^5
-- 243 + 405 * x + 270 * x^2 + 90 * x^3 + 15 * x^4 + x^5
-- 
-- >>> poly1 p 10
-- 13
-- >>> poly1 (p^3) 10
-- 2197
-- >>> (poly1 p 10)^3
-- 2197

-- poly :: (Listable n b x, HasPow x n b, Semiring b) => Poly1 x -> x -> b

poly :: (Listable n b x, Semiring b, HasPow z n b) => Poly1 x -> z -> b
poly (Poly1 m) z = sum [b <.> z^#i | (i,b) <- toList m]

-- >>> take 50 $ show (single 1 :: Cofree Identity Z)
-- "0 :< Identity (1 :< Identity (0 :< Identity (0 :< "

type PS1 b = Poly1 (Cofree Identity b) -- streams

type PL1 b = Poly1 (Cofree Maybe b)  -- nonempty lists

-- >>> let p = single 1 <+> value 3 :: PL1 Z
-- >>> p
-- 3 + x
-- >>> p^3
-- 27 + 27 * x + 9 * x^[(),()] + x^[(),(),()]

-- >>> single 3 :: Cofree Maybe Z
-- 0 :< Just (0 :< Just (0 :< Just (1 :< Nothing)))

-- >>> p
-- <interactive>:1088:2: error: Variable not in scope: p
-- 
-- >>> p^3
-- <interactive>:1089:2: error: Variable not in scope: p
-- 
-- >>> p^5
-- <interactive>:1090:2: error: Variable not in scope: p

-- type PolyL b = Poly1 [b]

-- As in Doug McIlroy's "The Music of Streams"
integralL :: Fractional b => Poly1 [b] -> Poly1 [b]
-- integralL (Poly1 []) = Poly1 []  -- Breaks ODE termination.
integralL (Poly1 bs0) = Poly1 (0 : go 1 bs0)
 where
   go _ [] = []
   go n (b : d) = b/n : go (n+1) d

derivativeL :: (Additive b, Fractional b) => Poly1 [b] -> Poly1 [b]
derivativeL (Poly1 []) = zero
derivativeL (Poly1 (_ : bs0)) = Poly1 (go 1 bs0)
 where
   go _ [] = []
   go n (b : bs) = n * b : go (n+1) bs

-- integralL generalizes beyond Maybe, but derivativeL doesn't. TODO: fix.

sinL, cosL, expL :: Poly1 [Rational]
sinL = integralL cosL
cosL = 1 - integralL sinL
expL = 1 + integralL expL

lop :: Show a => a -> IO ()
lop = putStrLn . (++ " ...") . take 115 . show

-- >>> lop sinL
-- x - 1 % 6 * x^3 + 1 % 120 * x^5 - 1 % 5040 * x^7 + 1 % 362880 * x^9 - 1 % 39916800 * x^11 + 1 % 6227020800 * x^13 - ...
-- >>> lop cosL
-- 1 % 1 - 1 % 2 * x^2 + 1 % 24 * x^4 - 1 % 720 * x^6 + 1 % 40320 * x^8 - 1 % 3628800 * x^10 + 1 % 479001600 * x^12 -  ...
-- >>> lop expL
-- 1 % 1 + x + 1 % 2 * x^2 + 1 % 6 * x^3 + 1 % 24 * x^4 + 1 % 120 * x^5 + 1 % 720 * x^6 + 1 % 5040 * x^7 + 1 % 40320 * ...

-- >>> lop (derivativeL sinL)  -- |== cosL|
-- 1 % 1 - 1 % 2 * x^2 + 1 % 24 * x^4 - 1 % 720 * x^6 + 1 % 40320 * x^8 - 1 % 3628800 * x^10 + 1 % 479001600 * x^12 -  ...
-- >>> lop (derivativeL cosL)  -- |== - sinL|
-- (-1) % 1 * x + 1 % 6 * x^3 - 1 % 120 * x^5 + 1 % 5040 * x^7 - 1 % 362880 * x^9 + 1 % 39916800 * x^11 - 1 % 62270208 ...
-- >>> lop (derivativeL expL)  -- |== expL|
-- 1 % 1 + x + 1 % 2 * x^2 + 1 % 6 * x^3 + 1 % 24 * x^4 + 1 % 120 * x^5 + 1 % 720 * x^6 + 1 % 5040 * x^7 + 1 % 40320 * ...

-- >>> lop (2 * expL)
-- 2 % 1 + 2 % 1 * x + x^2 + 1 % 3 * x^3 + 1 % 12 * x^4 + 1 % 60 * x^5 + 1 % 360 * x^6 + 1 % 2520 * x^7 + 1 % 20160 * x^8 + ...

-- >>> lop (sinL * cosL)
-- x - 2 % 3 * x^3 + 2 % 15 * x^5 - 4 % 315 * x^7 + 2 % 2835 * x^9 - 4 % 155925 * x^11 + 4 % 6081075 * x^13 - 8 % 638512875 ...

-- TODO: multivariate power series
-- Can I generalize Poly1 and PolyM?

{--------------------------------------------------------------------
    Multivariate polynomials
--------------------------------------------------------------------}

-- Polynomials with named "variables"
newtype PolyM b = PolyM { unPolyM :: Map (Map Name N) b } deriving
  (Additive, Semiring, Functor, Indexable (Map Name N) b, HasSingle (Map Name N) b)

instance (Show b, Ord b, Num b, D01 b) => Show (PolyM b) where
  showsPrec d (PolyM m) =
    showsPrec d (Terms (term <$> sortOn (M.keys . fst) (M.toDescList m)))
   where
     term (p,b) = Term b (Pows p)

-- instance (DetectableZero b, DetectableOne b, Show b) => Show (PolyM b) where
--   showsPrec d (PolyM m) =
--     showsPrec d (Terms (term <$> sortOn (M.keys . fst) (M.toDescList m)))
--    where
--      term (p,b) = Term b (Pows p)

-- TODO: improve the sorting criterion

-- varM :: Name -> PolyM Z
varM :: Semiring b => Name -> PolyM b
varM = single . single

-- >>> let p = varM "x" <+> varM "y" <+> varM "z" :: PolyM Z
-- >>> p
-- x + y + z
-- 
-- >>> p^2
-- x^2 + 2 * x * y + 2 * x * z + y^2 + 2 * y * z + z^2
-- 
-- >>> p^3
-- x^3 + 3 * x^2 * y + 3 * x * y^2 + 6 * x * y * z + 3 * x^2 * z + 3 * x * z^2 + y^3 + 3 * y^2 * z + 3 * y * z^2 + z^3

-- TODO: use the generalized Poly1 in place of PolyM. I'll have to tweak
-- something, since the Poly1 Show instance wants to insert "x".

type PM b = Poly1 (Map (Map Name N) b)

-- >>> let p = single 1 <+> value 3 :: Poly1 [Z]
-- >>> p
-- 3 + x
-- >>> p^3
-- 27 + 27 * x + 9 * x^2 + x^3
-- 
-- >>> p^5
-- 243 + 405 * x + 270 * x^2 + 90 * x^3 + 15 * x^4 + x^5
--
-- >>> poly1 p 10
-- 13
-- >>> poly1 (p^3) 10
-- 2197
-- >>> (poly1 p 10)^3
-- 2197

{--------------------------------------------------------------------
    Show utilities
--------------------------------------------------------------------}

compose :: [a -> a] -> (a -> a)
compose = foldr (.) id

showIter :: Show b => Int -> String -> (b -> Bool) -> Int -> [b] -> ShowS
showIter inner op omit outer bs =
  showParen (outer > inner) $
  compose (intersperse (showString op) (showsPrec inner <$> filter (not . omit) bs))

-- TODO: check for empty bs and for singleton bs

showSum :: (Show b, DetectableZero b) => Int -> [b] -> ShowS
showSum  = showIter 6 " + " isZero

showProd :: (Show b, DetectableOne b) => Int -> [b] -> ShowS
showProd = showIter 7 " * " isOne

-- Cleverer showSum that uses subtraction for negative coefficients
showSum' :: (Show x, Show b, Ord b, Num b, D01 b, D01 x) 
         => Int -> [Term b x] -> ShowS
showSum' p terms = go (filter (not . isZero) terms)
 where
   go [] = showString "0"  -- I don't think we'll get this case
   go (b0:bs0) = showParen (p > 6) $
                 showsPrec 6 b0 . compose (term <$> bs0)
    where
      term (Term b x) | b < 0 = showString (" - ") . showsPrec 6 (Term (-b) x)
                      | otherwise = showString (" + ") . showsPrec 6 (Term b x)


{--------------------------------------------------------------------
    Syntactic representations
--------------------------------------------------------------------}

newtype Name = Name String deriving (Eq,Ord)

instance DetectableZero Name where isZero = const False
instance DetectableOne  Name where isOne  = const False

instance Show     Name where show (Name s) = s
instance IsString Name where fromString = Name

data Pow b n = Pow b n  -- b * x^n

instance DetectableZero b => DetectableZero (Pow b n) where
  isZero (Pow b _) = isZero b

instance (DetectableOne b, DetectableZero n) => DetectableOne (Pow b n) where
  isOne (Pow b n) = isOne b || isZero n

instance (Show n, Show b, DetectableZero n, DetectableOne n, DetectableOne b)
      => Show (Pow b n) where
  showsPrec d p@(Pow b n)
    | isOne p   = showString "1"
    | isOne n   = showsPrec d b
    | otherwise = showParen (d >= 8) $
                  showsPrec 8 b . showString "^" . showsPrec 8 n

-- >>> Pow "z" 5 :: Pow Name N
-- z^5

newtype Pows b = Pows (Map b N) -- deriving (Semiring,Monoid)

instance DetectableZero b => DetectableZero (Pows b) where
  isZero = const False

instance DetectableOne (Pows b) where
  isOne (Pows m) = all isZero m

-- TODO: try changing isZero for Map to be 'all isZero'. Might wedge on recursive examples.

instance (Show b, DetectableZero b, DetectableOne b) => Show (Pows b) where
  showsPrec d p@(Pows m)
    | isOne p   = showString "1"
    | otherwise = showProd d (uncurry Pow <$> M.toList m)

-- >>> Pows (("x" +-> 2) <+> ("y" +-> 3)) :: Pows Name
-- x^2 * y^3

data Term b x = Term b x  -- b * x

instance (DetectableZero b, DetectableZero x) => DetectableZero (Term b x) where
  isZero (Term b x) = isZero b || isZero x

instance (Show b, Show x, DetectableOne x, DetectableZero b, DetectableOne b)
      => Show (Term b x) where
  showsPrec d (Term b x)
    | isZero b || isOne x = showsPrec d b
    | isOne  b  = showsPrec d x
    | otherwise = showParen (d > 6) $
                  showsPrec 6 b . showString " * " . showsPrec 6 x

-- >>> Term 7 (Pows (("x" +-> 2) <+> ("y" +-> 3))) :: Term Z (Pows Name)
-- 7 * x^2 * y^3

data Terms b = Terms [b]

-- instance (Show b, DetectableZero b) => Show (Terms b) where
--   showsPrec d (Terms bs) = showSum d bs

instance (Show b, Show x, Ord b, Num b, D01 b, D01 x)
      => Show (Terms (Term b x)) where
  showsPrec d (Terms bs) = showSum' d bs
