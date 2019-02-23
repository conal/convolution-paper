{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Playing with polynomials

module Poly where

import Prelude hiding ((^),sum)

import GHC.Natural (Natural)
import Data.Map (Map)
import qualified Data.Map as M

import Semi

type Poly1 b = Map N b

eval1 :: Semiring b => Poly1 b -> b -> b
eval1 m x = sum [c <.> x^i | (i,c) <- M.toList m]

type P = Poly1 Int

x1 :: P
x1 = single 1

xp3 :: P
xp3 = x1 <+> value 3

xp3sq :: P
xp3sq = xp3 <.> xp3

-- Next, represent the collection of "variables" as Map String
