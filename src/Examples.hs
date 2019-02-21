{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some polymorphic language examples

module Examples where

import Prelude hiding (sum,product)

import Data.Char (toUpper)

import Semi

type Stringy f b = (Key f ~ String, HasSingle f b)

sa, sb, pink, pig :: (Stringy f b, Semiring b) => f b
sa   = single "a"
sb   = single "b"
pink = single "pink"
pig  = single "pig"

pp :: (Stringy f b, Additive (f b), Semiring b) => f b
pp   = pink <+> pig

as, ass, pps :: (Stringy f b, StarSemiring (f b), StarSemiring b) => f b
as  = star sa
ass = star as
pps = star pp

anbn :: (Stringy f b, Semiring (f b), Semiring b) => f b
anbn  = one <+> (sa <.> anbn <.> sb)

sumSingle :: (HasSingle f b, Semiring b, Additive (f b), Key f ~ [a]) => [a] -> f b
sumSingle bs = sum [single [c] | c <- bs]

char, letterL, letterU, letter, digit :: (Stringy f b, Semiring (f b), Semiring b) => f b
char    = sumSingle [' ' .. '~']
letterL = sumSingle ['a' .. 'z']
letterU = sumSingle ['A' .. 'Z']
letter  = letterL <+> letterU
digit   = sumSingle ['0' .. '9']

-- Balanced brackets <https://en.wikipedia.org/wiki/Dyck_language>
dyck :: (Stringy f b, Semiring (f b), Semiring b) => f b
dyck = one <+> single "[" <.> dyck <.> single "]" <.> dyck

-- Will dyck get repeatedly reconstructed, considering polymorphism?

-- TODO: try other formulations, including an explicit local recursion and star.
