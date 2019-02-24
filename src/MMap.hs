
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Finite maps with a more sensible Monoid instance

module MMap where

import qualified Data.Map as M

-- For now, but maybe use MMap in place of Map throughout
import Semi

newtype Map k v = M (M.Map k v) deriving
  (Eq,Ord,Show,Functor,Foldable,Additive,Semiring,Indexable k v,HasSingle k v)

instance (Ord k, Semigroup v) => Semigroup (Map k v) where
  M u <> M v = M (M.unionWith (<>) u v)

instance (Ord k, Monoid v) => Monoid (Map k v) where
  mempty = M mempty
  mappend = (<>)

toDescList :: Map k v -> [(k,v)]
toDescList (M m) = M.toDescList m

toAscList :: Map k v -> [(k,v)]
toAscList (M m) = M.toAscList m

toList :: Map k v -> [(k,v)]
toList (M m) = M.toList m

fromList :: Ord k => [(k,v)] -> Map k v
fromList ps = M (M.fromList ps)

keys :: Map k v -> [k]
keys (M m) = M.keys m
