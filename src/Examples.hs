{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some polymorphic language examples

module Examples where

import Prelude hiding (sum,product)

import Data.Char (toUpper)

import Semi

type Stringy b x = HasSingle String b x

sa, sb, pink, pig :: (Stringy b x, Semiring b) => x
sa   = single "a"
sb   = single "b"
pink = single "pink"
pig  = single "pig"

pp :: (Stringy b x, Additive x, Semiring b) => x
pp   = pink <+> pig

as, ass, pps :: (Stringy b x, StarSemiring x, StarSemiring b) => x
as  = star sa
ass = star as
pps = star pp

anbn :: (Stringy b x, Semiring x, Semiring b) => x
anbn = one <+> (sa <.> anbn <.> sb)

sumSingle :: (HasSingle [a] b x, Semiring b, Additive x) => [a] -> x
sumSingle bs = sum [single [c] | c <- bs]

char, letterL, letterU, letter, digit :: (Stringy b x, Semiring x, Semiring b) => x
char    = sumSingle [' ' .. '~']
letterL = sumSingle ['a' .. 'z']
letterU = sumSingle ['A' .. 'Z']
letter  = letterL <+> letterU
digit   = sumSingle ['0' .. '9']

-- Balanced brackets <https://en.wikipedia.org/wiki/Dyck_language>
dyck :: (Stringy b x, Semiring x, Semiring b) => x
dyck = one <+> single "[" <.> dyck <.> single "]" <.> dyck

-- Will dyck get repeatedly reconstructed, considering polymorphism?

-- TODO: try other formulations, including an explicit local recursion and star.

starL :: Semiring b => b -> b
starL b = one <+> starL b <.> b

starR :: Semiring b => b -> b
starR b = one <+> b <.> starR b
