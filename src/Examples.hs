{-# LANGUAGE RankNTypes #-}

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some polymorphic language examples

module Examples where

import Semi

type Stringy h = (Key h ~ String, HasSingle h)

sa, sb, pink, pig :: (Stringy h, Semiring b) => h b
sa   = single "a"
sb   = single "b"
pink = single "pink"
pig  = single "pig"

pp :: (Stringy h, Additive1 h, Semiring b) => h b
pp   = pink <+> pig

as, ass, pps :: (Stringy h, Additive1 h, StarSemiring1 h, StarSemiring b) => h b
as  = star sa
ass = star as
pps = star pp

anbn :: (Stringy h, Semiring1 h, Semiring b, Semiring b) => h b
anbn  = one <+> (sa <.> anbn <.> sb)
