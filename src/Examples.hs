{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some polymorphic language examples

module Examples where

import Prelude hiding (sum,product)

import Data.Char (toUpper)

import Semi

type Stringy h b = (Key h ~ String, HasSingle h b)

sa, sb, pink, pig :: (Stringy h b, Semiring b) => h b
sa   = single "a"
sb   = single "b"
pink = single "pink"
pig  = single "pig"

pp :: (Stringy h b, Additive (h b), Semiring b) => h b
pp   = pink <+> pig

as, ass, pps :: (Stringy h b, StarSemiring (h b), StarSemiring b) => h b
as  = star sa
ass = star as
pps = star pp

anbn :: (Stringy h b, Semiring (h b), Semiring b) => h b
anbn  = one <+> (sa <.> anbn <.> sb)

sumSingle :: (HasSingle h b, Semiring b, Additive (h b), Key h ~ [a]) => [a] -> h b
sumSingle bs = sum [single [c] | c <- bs]

char, letterL, letterU, letter, digit :: (Stringy h b, Semiring (h b), Semiring b) => h b
char    = sumSingle [' ' .. '~']
letterL = sumSingle ['a' .. 'z']
letterU = sumSingle ['A' .. 'Z']
letter  = letterL <+> letterU
digit   = sumSingle ['0' .. '9']

-- Balanced brackets <https://en.wikipedia.org/wiki/Dyck_language>
dyck :: (Stringy h b, Semiring (h b), Semiring b) => h b
dyck = one <+> single "[" <.> dyck <.> single "]" <.> dyck

-- Will dyck get repeatedly reconstructed, considering polymorphism?

-- TODO: try other formulations, including an explicit local recursion and star.
