{-# LANGUAGE RankNTypes #-}

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some polymorphic language examples

module Examples where

import Semi

type Stringy h b = (Key h ~ String, HasSingle h b)

sa, sb, pink, pig :: (Stringy h b, Semiring b) => h b
sa   = single "a"
sb   = single "b"
pink = single "pink"
pig  = single "pig"

pp :: (Stringy h b, Additive1 h, Semiring b) => h b
pp   = pink <+> pig

as, ass, pps :: (Stringy h b, Additive1 h, StarSemiring1 h, StarSemiring b) => h b
as  = star sa
ass = star as
pps = star pp

anbn :: (Stringy h b, Semiring1 h, Semiring b, Semiring b) => h b
anbn  = one <+> (sa <.> anbn <.> sb)
