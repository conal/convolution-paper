#ifdef EXAMPLES
{-# OPTIONS_GHC -Wno-unused-imports #-} -- Examples
#endif

-- | List tries using functions from characters

module Decomp where  -- TODO: rename module

import Prelude hiding (sum,product)

import Semi

#ifdef EXAMPLES
import Examples
#endif

-- | List trie, denoting '[c] -> b'"
infix 1 :<
data LTrie c b = b :< (c -> LTrie c b)

instance Decomposable b ((->) c) (LTrie c b) where
  (<:) = (:<)
  decomp (b :< dp) = (b, dp)

#ifdef EXAMPLES

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type L  = LTrie  Char Bool
type L' = Decomp L

xpig,xpink,xpp,xanbn :: L'
xpig = pig
xpink = pink
xpp = pp
xanbn = anbn

-- >>> xpig ! "p"
-- False
-- >>> xpig ! "pig"
-- True
-- >>> xpig ! "piggy"
-- False

-- >>> xpp ! "pink"
-- True
-- >>> xpp ! "pig"
-- True
-- >>> xpp ! "ping"
-- False

-- >>> xanbn ! ""
-- True
-- >>> xanbn ! "a"
-- False
-- >>> xanbn ! "ab"
-- True
-- >>> xanbn ! "aabb"
-- True
-- >>> xanbn ! "aaaaabbbbb"
-- True

#endif

