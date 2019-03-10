{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Finite maps with sharing (for non-injectivity)

module ShareMap where

import Control.Arrow (second,(***))
import Data.Foldable (foldl')
import Data.Maybe (fromJust)

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Semi

-- Point each key to a canonical representative, and point each representative
-- to the equivalence class and the map value.
data ShareMap k v = SM (Map k k) (Map k (Set k, v)) deriving Show

instance Ord k => Semigroup (ShareMap k v) where
  SM rep m <> SM rep' m' = SM (M.union rep rep') (M.union m m')

instance Ord k => Monoid (ShareMap k v) where
  mempty = SM M.empty M.empty
  mappend = (<>)

-- I could instead newtype-wrap a pair, and derive Semigroup and Monoid

empty :: ShareMap k v
empty = SM M.empty M.empty

type instance Key (ShareMap k) = k

instance (Ord k, Additive v) => Indexable k v (ShareMap k v) where
  SM reps m ! k = case M.lookup k reps of
                    Nothing -> zero
                    Just k' -> (snd <$> m) ! k'  -- split second map

infixr 2 *->
(*->) :: Set k -> v -> ShareMap k v
ks *-> v = case S.minView ks of
             Nothing -> empty
             Just (k,_) -> SM (M.fromDistinctAscList ((,k) <$> S.toAscList ks))
                              (M.singleton k (ks,v))

-- TODO: move (*->) into HasSingle with defaults.
instance (Ord k, Additive v) => HasSingle k v (ShareMap k v) where
  k +-> v = S.singleton k *-> v

instance Functor (ShareMap k) where
  fmap f (SM reps m) = SM reps (fmap (second f) m)

-- Addition is trickier. See 2019-03-{05,06,09} journal notes.

type Chunk k v = (Set k, v)
type Chunks k v = [Chunk k v] -- disjoint k subsets

addChunks :: (Ord k, Additive v) => Chunks k v -> Chunks k v -> Chunks k v
addChunks p p' =
     [ (ks  `S.difference` support', x ) | (ks ,x ) <- p ]
  ++ [ (ks' `S.difference` support , x') | (ks',x') <- p']
  ++ [ (ks `S.intersection` ks', x <+> x') | (ks,x) <- p, (ks',x') <- p' ]
 where
   support  = chunksSupport p
   support' = chunksSupport p'

chunksSupport :: Ord k => Chunks k v -> Set k
chunksSupport = S.unions . map fst

-- data ShareMap k v = SM (Map k k) (Map k (Set k, v)) deriving Show

-- Build a ShareMap from disjoint chunks.
shareMap :: forall k v. (Ord k, Additive v) => Chunks k v -> ShareMap k v
shareMap (filter (not . null . fst) -> chunks) = foldMap h (chunks `zip` maxes)
 where
   maxes :: [k]
   maxes = (fromJust . S.lookupMax . fst) <$> chunks
   h :: (Chunk k v, k) -> ShareMap k v
   h ((ks,v),maxk) =
     SM (M.fromList ((,maxk) <$> S.elems ks)) (M.singleton maxk (ks,v))

instance (Ord k, Additive v) => Additive (ShareMap k v) where
  zero = SM M.empty M.empty
  SM _ (M.elems -> p) <+> SM _ (M.elems -> q) = shareMap (p `addChunks` q)

-- >>> let a2 = 'a' +-> 2 :: ShareMap Char Z
-- >>> a2
-- SM (fromList [('a','a')]) (fromList [('a',(fromList "a",2))])
-- >>> let b3 = 'b' +-> 3 :: ShareMap Char Z
-- >>> b3
-- SM (fromList [('b','b')]) (fromList [('b',(fromList "b",3))])
-- >>> a2 <+> b3
-- SM (fromList []) (fromList [])
-- >>> a2 <+> a2
-- SM (fromList [('a','a')]) (fromList [('a',(fromList "a",4))])
-- >>> b3 <+> b3
-- SM (fromList [('b','b')]) (fromList [('b',(fromList "b",6))])
-- 
-- >>> let a2c = [(S.fromList "a",2)] :: Chunks Char Z
-- >>> let b3c = [(S.fromList "b",3)] :: Chunks Char Z
-- >>> (a2c,b3c)
-- ([(fromList "a",2)],[(fromList "b",3)])
-- >>> addChunks a2c b3c
-- [(fromList "",2),(fromList "",5)]

-- TODO: Fix, probably adding missing explicit/implicit pairs
-- Add support :: ShareMap k v -> Set k
