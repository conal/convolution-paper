{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Benchmarks

module Main where

import Control.DeepSeq (NFData)
import Data.Map (Map)
import Criterion.Main
import Criterion.Types (Config(..),Verbosity(..))

import Misc (cats)
import Semi
import RegExp
import LTrie

import Examples

#if 1

main :: IO ()
-- main = return ()

main = do 

  group "letters" (star letter)
    [ ("asdf", cats 5 "asdf") ]

  group "dyck" dyck
    [ ("1", "[]")
    , ("2", "[[]]")
    , ("3", "[[a]]")
    , ("4", "[[]][]")
    ]

  group "anbn" anbn
    [ ("eps"     , "")
    , ("ab"      , "ab")
    , ("ba"      , "ba")
    , ("aabb"    , "aabb")
    , ("aacbb"   , "aacbb")
    , ("aaabbb"  , "aaabbb")
    , ("aaabbbb" , "aaabbbb")
    ]


type Ok f b = (HasSingle f b, StarSemiring (f b), StarSemiring b, NFData b, Key f ~ String)

group :: String -> (forall f b. Ok f b => f b) -> [(String,String)] -> IO ()
group groupName example dats =
  do putStrLn ("Group " ++ show groupName)
     defaultMainWith config (dat <$> dats)
 where
   config = defaultConfig
     { reportFile = Just ("test/Benchmarks/" ++ groupName ++ ".html")
     , timeLimit  = 1 -- 5
     }
   dat :: (String,String) -> Benchmark
   dat (dname,str) =
     bgroup dname
       [ style @(LTrie  ((->) Char)) @Bool "Function"
       , style @(LTrie  (Map  Char)) @Bool "Map"
       , style @(LTrie  CharMap    ) @Bool "IntMap"
       ]
    where
      style :: forall f b. Ok f b => String -> Benchmark
      style s = bench s (nf (example @f @b !) str)
     

#elif 0

type Ok f b = (HasSingle f b, StarSemiring (f b), StarSemiring b, NFData b{- , Key f ~ String-})

-- type Example f b = (String, f b, Key f)

-- data Group = Group String (forall f b. Ok f b => (String, [Example f b]))

type Example = forall f b. Ok f b => Example String (f b) (Key f)

-- -- TODO: revisit Ok
-- benchX :: forall f b. Ok f b => (String, f b, Key f) -> Benchmark
-- benchX (name,bs,k) = bgroup name [bench name (nf (bs !) k)]

data Style = forall f b. Ok f b => Style String

data Group = Group String [Style] Example

benchX :: forall f b. Ok f b => Example -> Style -> Benchmark
benchX (Example name bs k) (Style ) = bgroup name [bench name (nf (bs !) k)]

foo :: (String, forall f b. Ok f b => ))

-- benchG :: Group -> IO ()
-- benchG (Group name styles example) =
--   defaultMainWith config (benchX example <$> styles)
--  where
--    config = defaultConfig
--      { reportFile = Just name
--      , timeLimit  = 1 -- 5
--      }
   

-- example :: forall f b. Ok f b => String -> Example -> IO ()
-- example groupName (exampleName, x, a) =
--   defaultMainWith config $
--    [ bgroup group 
--      [ x @(LTrie  ((->) Char)  ) @Bool "Function"
--      , x @(LTrie  (Map Char)) @Bool "Map"
--      , x @(LTrie  CharMap   ) @Bool "IntMap"
--     ]
--   ]


 --     [ bench nm (nf (x !) k)] ]
 -- where
 --   config = defaultConfig
 --     { reportFile = Just name
 --     , timeLimit  = 1 -- 5
 --     }

-- lettersG :: Group
-- lettersG = Group "letters" $
--   [ lettersX @(LTrie  ((->) Char)) @Bool "Function"
--   , lettersX @(LTrie  (Map Char) ) @Bool "Map"
--   , lettersX @(LTrie  CharMap    ) @Bool "IntMap"
--   ]

-- lettersX :: 
-- lettersX = "letters" [("asdf-50", star letter, cats 50 "asdf")]

-- lettersX :: forall f b. Ok f b => IO ()
-- lettersX = example @f @b "letters" [("asdf-50", star letter, cats 50 "asdf")]

-- dyckX :: forall f b. Ok f b => IO ()
-- dyckX = example @f @b "dyck" 
--          [ ("1", dyck, "[]")
--          , ("2", dyck, "[[]]")
--          , ("3", dyck, "[[a]]")
--          , ("4", dyck, "[[]][]")
--          ]

-- anbnX :: forall f b. Ok f b => IO ()
-- anbnX = example @f @b "dyck" 
--          [ ("eps"    , anbn , "")
--          , ("ab"     , anbn , "ab")
--          , ("ba"     , anbn , "ba")
--          , ("aabb"   , anbn , "aabb")
--          , ("aacbb"  , anbn , "aacbb")
--          , ("aaabbb" , anbn , "aaabbb")
--          , ("aaabbbb", anbn , "aaabbbb")
--          ]

main :: IO ()
main =
  do -- lettersX 
     return ()


#else

config :: Config
config = defaultConfig
  {
    reportFile = Just "crunch.html"  -- for example
  , timeLimit  = 1  -- 5
  -- , verbosity  = Quiet  -- Normal
  }

main :: IO ()
main = defaultMainWith config
  [ bgroup "" []

  , matchers @((->) String       )      @Bool "Function"

  , bgroup "RegExp"
    [ matchers @(RegExp ((->) Char)   ) @Bool "Function"
    -- , matchers @(RegExp (M.Map  Char)) @Bool "Map"
    ]

  , bgroup "Trie"
    [ bgroup "" []
    -- , matchers @(LTrie  ((->) Char)  ) @Bool "Function"
    , matchers @(LTrie  (Map Char)) @Bool "Map"
    , matchers @(LTrie  CharMap   ) @Bool "IntMap"
    ]
  ]

matchers :: forall f b. (HasSingle f b, Key f ~ String, StarSemiring (f b), StarSemiring b, NFData b)
         => String -> Benchmark
matchers group =
  bgroup group
    [ bg

    , bgroup "letters"
       [ bg
       , bench "asdf-50"  $ star letter # cats 50  "asdf"
       ]

    , bgroup "dyck"
      [ bg
      , bench "1" $ dyck # "[]"
      , bench "2" $ dyck # "[[]]"
      , bench "3" $ dyck # "[[a]]"
      , bench "4" $ dyck # "[[]][]"
      ]

    , bgroup "anbn"
      [ bg
      , bench "eps"     $ anbn # ""
      , bench "ab"      $ anbn # "ab"
      , bench "ba"      $ anbn # "ba"
      , bench "aabb"    $ anbn # "aabb"
      , bench "aacbb"   $ anbn # "aacbb"
      , bench "aaabbb"  $ anbn # "aaabbb"
      , bench "aaabbbb" $ anbn # "aaabbbb"
      ]

    ]
 where
   infixl 2 #
   (#) :: f b -> String -> Benchmarkable
   x # s = nf (x !) s

bg :: Benchmark
bg = bgroup "" []

#endif
