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

data Pows b = Pows (Map b N)

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

instance (Show b, DetectableZero b) => Show (Terms b) where
  showsPrec d (Terms bs) = showSum d bs

{--------------------------------------------------------------------
    Univariate polynomials
--------------------------------------------------------------------}

newtype Poly1 h b = Poly1 (h b) deriving
  (Additive, Semiring, Functor) -- , Indexable n b, HasSingle n b)

-- TODO: try combining h & b

deriving instance Indexable n b (h b) => Indexable n b (Poly1 h b)
deriving instance HasSingle n b (h b) => HasSingle n b (Poly1 h b)

instance ( DetectableZero b, DetectableOne b, Show b, Listable n b (h b)
         , Show n, DetectableZero n, DetectableOne n )
      => Show (Poly1 h b) where
  showsPrec d (Poly1 m) = showsPrec d (Terms (term <$> toList m))
   where
     term (i,b) = Term b (Pow (Name "x") i)

type P1 = Poly1 (Map N)

eval1 :: (Listable N b (h b), Semiring b) => Poly1 h b -> b -> b
eval1 (Poly1 m) z = sum [b <.> z^i | (i,b) <- toList m]

-- eval :: (Listable n b (h b), HasPow (h b) n b, Semiring b) => Poly1 h b -> h b -> b
-- eval (Poly1 m) z = sum [b <.> z^#i | (i,b) <- toList m]

-- TODO: generalize (^) so that this definition works in general.

-- >>> let p = single 1 <+> value 3 :: P1 Z
-- >>> p
-- 3 + x
-- >>> p^3
-- 27 + 27 * x + 9 * x^2 + x^3
-- 
-- >>> p^5
-- 243 + 405 * x + 270 * x^2 + 90 * x^3 + 15 * x^4 + x^5
-- 
-- >>> eval1 p 10
-- 13
-- >>> eval1 (p^3) 10
-- 2197
-- >>> (eval1 p 10)^3
-- 2197

-- TODO: generalize from Map N to any functor f with Key f = N. I'll need to get
-- indices as well, as in the Keyed class from the keys library.
-- 
-- -- * Keyed
-- class Functor f => Keyed f where
--   mapWithKey :: (Key f -> a -> b) -> f a -> f b

-- >>> 1 :: Peano
-- [()]

-- >>> take 50 $ show (single 1 :: Cofree Identity Z)
-- "0 :< Identity (1 :< Identity (0 :< Identity (0 :< "

type PS1 = Poly1 (Cofree Identity) -- streams

type List = Cofree Maybe

type PL1 = Poly1 (Cofree Maybe)  -- nonempty lists

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

{--------------------------------------------------------------------
    Multivariate polynomials
--------------------------------------------------------------------}

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

-- >>> q^4
-- x^4 + 4 * x^3 * y + 6 * x^2 * y^2 + 4 * x * y^3 + 12 * x^2 * y * z + 12 * x * y^2 * z + 12 * x * y * z^2 + 4 * x^3 * z + 6 * x^2 * z^2 + 4 * x * z^3 + y^4 + 4 * y^3 * z + 6 * y^2 * z^2 + 4 * y * z^3 + z^4
-- >>> p <.> q
-- x^2 + 2 * x * y + x * z + y^2 + y * z

{--------------------------------------------------------------------
    Try PolyM via Poly1
--------------------------------------------------------------------}

type PM = Poly1 (Map (Map Name N))

{--------------------------------------------------------------------
    Univariate power series
--------------------------------------------------------------------}

type Stream = Cofree Identity

infixr 5 :#
pattern (:#) :: b -> Stream b -> Stream b
pattern b :# bs = b :< Identity bs
{-# COMPLETE (:#) :: Cofree #-}

streamList :: Stream b -> [b]
streamList (b :# bs) = b : streamList bs

listStream :: [b] -> Stream b
listStream [] = error "listStream: oops! empty"
listStream (b : bs) = b :# listStream bs

takeS :: N -> Stream b -> [b]
takeS 0 _ = []
takeS n (b :# bs) = b : takeS (n-1) bs

newtype Series1 b = Series1 (Stream b) deriving
  (Additive, Semiring, Functor, Indexable [()] b, HasSingle [()] b)

instance (DetectableZero b, DetectableOne b, Show b) => Show (Series1 b) where
  showsPrec d (Series1 bs) = lopString .
    showsPrec d (Terms (term <$> zip [0::N ..] (lopStream bs)))
   where
     term (i,b) = Term b (Pow (Name "x") i)
     lopStream s = takeS 100 s
     lopString s = take 80 s ++ " ..."

instance (Semiring b, Num b, DetectableZero b, DetectableOne b)
      => Num (Series1 b) where
  fromInteger = value . fromInteger
  negate = fmap negate
  (+) = (<+>)
  (*) = (<.>)
  abs = error "abs on Series1 undefined"
  signum = error "abs on Series1 undefined"

-- As in Doug McIlroy's "The Music of Streams"
integral :: Fractional b => Series1 b -> Series1 b
integral (Series1 bs0) = Series1 (0 :# go 1 bs0)
 where
   go n (b :# bs) = b/n :# go (n+1) bs

derivative :: Fractional b => Series1 b -> Series1 b
derivative (Series1 (_ :# bs0)) = Series1 (go 1 bs0)
 where
   go n (b :# bs) = n * b :# go (n+1) bs

sinS, cosS, expS :: Series1 Rational
sinS = integral cosS
cosS = 1 - integral sinS
expS = 1 + integral expS

-- >>> sinS
-- x + (-1) % 6 * x^3 + 1 % 120 * x^5 + (-1) % 5040 * x^7 + 1 % 362880 * x^9 + (-1) ...
-- >>> cosS
-- 1 % 1 + (-1) % 2 * x^2 + 1 % 24 * x^4 + (-1) % 720 * x^6 + 1 % 40320 * x^8 + (-1 ...
-- >>> expS
-- 1 % 1 + x + 1 % 2 * x^2 + 1 % 6 * x^3 + 1 % 24 * x^4 + 1 % 120 * x^5 + 1 % 720 * ...

-- >>> derivative sinS  -- == cosS
-- 1 % 1 + (-1) % 2 * x^2 + 1 % 24 * x^4 + (-1) % 720 * x^6 + 1 % 40320 * x^8 + (-1 ...
-- >>> derivative cosS  -- == - sinS
-- (-1) % 1 * x + 1 % 6 * x^3 + (-1) % 120 * x^5 + 1 % 5040 * x^7 + (-1) % 362880 * ...
-- >>> derivative expS  -- == expS
-- 1 % 1 + x + 1 % 2 * x^2 + 1 % 6 * x^3 + 1 % 24 * x^4 + 1 % 120 * x^5 + 1 % 720 * ...

-- >>> 2 * expS
-- 2 % 1 + 2 % 1 * x + x^2 + 1 % 3 * x^3 + 1 % 12 * x^4 + 1 % 60 * x^5 + 1 % 360 *  ...

-- >>> sinS * cosS
-- x + (-2) % 3 * x^3 + 2 % 15 * x^5 + (-4) % 315 * x^7 + 2 % 2835 * x^9 + (-4) % 1 ...

-- TODO: multivariate power series
-- Can I generalize Poly1 and PolyM?

-- Try lists as Cofree Maybe.
-- Generalize my `Poly1` and `PolyM` definitions.
-- Maybe even unify them.

