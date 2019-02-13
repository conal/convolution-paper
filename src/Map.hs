{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | A semiring wrapper for Map. Probably subsumed by Convo, but this one is
-- simpler for the paper.

module Map where

import Data.Map (Map)
import qualified Data.Map as M

import Semi

-- #include "GenInstances.inc"

newtype Map' a b = M (Map a b)
  deriving (Show, Additive, HasSingle a b, LeftSemimodule b)

mapFun' :: (Ord a, Additive b) => Map' a b -> (b <-- a)
mapFun' (M m) = C (m !)

instance (Ord a, Monoid a, Semiring b) => Semiring (Map' a b) where
  one = M (mempty +-> one)
  -- M p <.> M q = M (M.fromListWith (<+>)
  --                  [(kp <> kq, vp <.> vq) | (kp,vp) <- M.toList p, (kq,vq) <- M.toList q])
  M m <.> M m' =
    M (M.fromListWith (<+>)
        [(k <> k', v <.> v') | (k,v) <- M.toList m, (k',v') <- M.toList m'])

-- >>> x1 = single "a" <+> single "b"  :: Map' String Int
-- >>> x1 <+> x1
-- M (fromList [("a",2),("b",2)])
-- >>> x1 <.> x1
-- M (fromList [("aa",1),("ab",1),("ba",1),("bb",1)])
