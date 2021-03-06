{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some polymorphic language examples

module Examples where

import Prelude hiding (sum,product)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Char (toUpper)

import Semi

a1, b1, pink, pig :: (HasSingle String b x, Semiring b) => x
a1   = single "a"
b1   = single "b"
pink = single "pink"
pig  = single "pig"

pp :: (HasSingle String b x, Additive x, Semiring b) => x
pp   = pink <+> pig

as, ass, pps, asbs, asbas, asas, fishy :: (HasSingle String b x, StarSemiring x, StarSemiring b) => x
as  = star a1
ass = star as
pps = star pp
asbs = star a1 <.> star b1
asbas = star a1 <.> b1 <.> star a1
asas = star a1 <.> star a1
fishy = star letter <.> single "fish" <.> star letter

anbn :: (HasSingle String b x, Semiring x, Semiring b) => x
anbn = one <+> a1 <.> anbn <.> b1

singleChar :: (Ord c, HasSingle [c] b x, Semiring b) => [c] -> x
singleChar cs = singles (S.fromList [[c] | c <- cs])

letter :: (HasSingle String b x, Semiring x, Semiring b) => x
letter = singleChar ['a' .. 'z']
-- letter = singles (S.fromList [[c] | c <- ['a' .. 'z']])  -- Should be much more efficient for SharedMap
-- letter = sum [single [c] | c <- ['a' .. 'z']]

-- Balanced brackets <https://en.wikipedia.org/wiki/Dyck_language>
dyck :: (HasSingle String b x, StarSemiring x, Semiring b) => x
dyck = star (single "[" <.> dyck <.> single "]")

-- Will dyck get repeatedly reconstructed, considering polymorphism?

-- TODO: try other formulations, including an explicit local recursion and star.

starL :: Semiring b => b -> b
starL b = one <+> starL b <.> b

starR :: Semiring b => b -> b
starR b = one <+> b <.> starR b
