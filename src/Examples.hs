{-# LANGUAGE RankNTypes #-}

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some polymorphic language examples

module Examples where

import Semi

sa, sb, pink, pig :: (HasSingle String b x, Semiring b) => x
sa   = single "a"
sb   = single "b"
pink = single "pink"
pig  = single "pig"

pp :: (HasSingle String b x, Semiring b, Additive x) => x
pp   = pink <+> pig

as, ass, pps :: (HasSingle String b x, Semiring b, StarSemiring x) => x
as  = star sa
ass = star as
pps = star pp

anbn :: (HasSingle String b x, Semiring b, Semiring x) => x
anbn  = one <+> (sa <.> anbn <.> sb)
