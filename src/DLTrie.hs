#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | List tries via Decomp in Semi

module DLTrie where

import Prelude hiding (sum,product)

import Data.Map (Map)
import qualified Data.Map as M

import Semi

#ifdef EXAMPLES
import Examples
#endif

-- | List trie, denoting '[c] -> b'"
infix 1 :<
data LTrie c b = b :< (c ->* LTrie c b) -- deriving Show

instance (Show c, Show b) => Show (LTrie c b) where
  showsPrec p (a :< dp) = showParen (p >= 1) $ showsPrec 2 a . showString " :< " . showsPrec 2 (M.toList dp)

instance Decomposable b (Map c) (LTrie c b) where
  (<:) = (:<)
  decomp (b :< dp) = (b, dp)

#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L  = LTrie  Char Bool
type L' = Decomp L

-- >>> pig :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< [])])])]
-- >>> pink :: L
-- False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])]
-- >>> pp :: L
-- False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])]

-- >>> pig :: L'
-- D (False :< [('p',False :< [('i',False :< [('g',True :< [])])])])
-- >>> pink :: L'
-- D (False :< [('p',False :< [('i',False :< [('n',False :< [('k',True :< [])])])])])
-- >>> pp :: L'
-- D (False :< [('p',False :< [('i',False :< [('g',True :< []),('n',False :< [('k',True :< [])])])])])

-- >>> trimD 3 as :: L'
-- D (True :< [('a',True :< [('a',True :< [('a',False :< [])])])])
-- >>> trimD 3 ass :: L'
-- D (True :< [('a',True :< [('a',True :< [('a',False :< [])])])])

-- >>> trimD 7 anbn :: L'
-- D (True :< [('a',False :< [('a',False :< [('a',False :< [('a',False :< [('a',False :< [('a',False :< [('a',False :< []),('b',False :< [])]),('b',False :< [('b',False :< [])])]),('b',False :< [('b',False :< [('b',False :< [])])])]),('b',False :< [('b',False :< [('b',True :< [])])])]),('b',False :< [('b',True :< [])])]),('b',True :< [])])])

-- >>> (anbn :: L') ! ""
-- True
-- >>> (anbn :: L') ! "a"
-- False
-- >>> (anbn :: L') ! "ab"
-- True
-- >>> (anbn :: L') ! "aabb"
-- True
-- >>> (anbn :: L') ! "aaaaabbbbb"
-- True

#endif
