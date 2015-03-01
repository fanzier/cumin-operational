{-# LANGUAGE LambdaCase #-}
module Cumin.Operational.Tree where

import           Control.Applicative
import           Control.Monad                (ap, liftM)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- * Computation Tree Representation

-- | Represents the nondeterministic result of a computation.
data Tree a
  = Leaf a -- ^ deterministic result
  | Branches [Tree a] -- ^ nondeterministic choice between computations
  deriving (Show)

instance Monad Tree where
  return = Leaf
  m >>= f = case m of
    Leaf a -> f a
    Branches ts -> Branches $ map (>>= f) ts

instance Functor Tree where
  fmap = liftM

instance Applicative Tree where
  pure = return
  (<*>) = ap

-- | Given a list of alternatives, wrap them in a nondeterministic computation.
branch :: [a] -> Tree a
branch = Branches . map return

-- | Creates a nondeterministic computation that fails.
-- I.e. there are no child nodes.
failure :: Tree a
failure = branch []

-- * Tree traversals

-- | Traverse the tree using breadth-first search.
bfsTraverse :: Maybe Int -> Tree a -> [(Int, a)]
bfsTraverse depth tree = go 0 [tree] []
  where
  go _ [] [] = []
  go i [] nextLevel = go (i + 1) nextLevel []
  go i (t:ts) nextLevel = case t of
    Leaf a -> (i,a):go i ts nextLevel
    Branches branches -> case branches of
      [] -> go i ts nextLevel
      _ -> go i ts (if limitExceeded depth (i + 1) then [] else nextLevel ++ branches) -- TODO: This is inefficient!

-- | Traverse the tree using depth-first search.
dfsTraverse :: Maybe Int -> Tree a -> [(Int, a)]
dfsTraverse depth = go 0
  where
  go i | limitExceeded depth i = const []
       | otherwise = \case
    Leaf a -> return (i, a)
    Branches ts -> ts >>= go (i + 1)

-- | Checks whether the depth limit prevents deeper searching.
limitExceeded :: Maybe Int -> Int -> Bool
limitExceeded = \case
  Nothing -> const False
  Just depth -> (> depth)
