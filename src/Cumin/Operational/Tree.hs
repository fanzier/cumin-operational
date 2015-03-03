{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Rank2Types #-}
module Cumin.Operational.Tree where

import           Control.Applicative
import           Control.Monad       (ap, liftM)

-- * General Computation Tree Representation

-- | Represents a general monad that can be converted to a tree.
class (Functor t, Applicative t, Monad t) => TreeLike t where
  -- | Given a list of alternatives, wrap them in a nondeterministic computation.
  branch :: [a] -> t a
  -- | Convert the computation tree to a Tree.
  toTree :: t a -> Tree a

-- | Creates a nondeterministic computation that fails.
-- I.e. there are no child nodes.
failure :: TreeLike t => t a
failure = branch []

-- | Default choice for the nondeterministic computation tree.
type TreeM = CTree

-- * Standard tree data type

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

instance TreeLike Tree where
  branch = Branches . map return
  toTree = id

-- * Codensity transformed tree

-- | Tree data type with the codensity transformation applied.
newtype CTree a = CTree (forall r. (a -> Tree r) -> Tree r)

instance Functor CTree where
  fmap = liftM

instance Applicative CTree where
  pure = return
  (<*>) = ap

instance Monad CTree where
  return x = CTree ($ x)
  (CTree p) >>= f = CTree (\h -> p (\a -> let CTree q = f a in q h))

treeAbs :: CTree a -> Tree a
treeAbs (CTree p) = p Leaf

instance TreeLike CTree where
  branch xs = CTree (\h -> Branches (map h xs))
  toTree = treeAbs

-- * Tree traversals

-- | Traverse the tree using breadth-first search.
bfsTraverse :: Maybe Int -> Tree a -> [(Int, a)]
bfsTraverse depth tree = go 0 [tree]
  where
  go _ [] = []
  go i ts = map (\a -> (i,a)) thisLevel ++ nextCutOff
    where
    (thisLevel, nextLevel) = split ts
    nextCutOff = if limitExceeded depth (i + 1) then [] else go (i + 1) nextLevel
  split [] = ([],[])
  split (t:ts) = let (this, next) = split ts in case t of
    Leaf a -> (a:this, next)
    Branches bs -> (this, bs ++ next)

-- | Traverse the tree using depth-first search.
dfsTraverse :: Maybe Int -> Tree a -> [(Int, a)]
dfsTraverse depth = go 0
  where
  go i = \case
    Leaf a -> return (i, a)
    Branches ts
      | limitExceeded depth (i + 1) -> []
      | otherwise -> ts >>= go (i + 1)

-- | Checks whether the depth limit prevents deeper searching.
limitExceeded :: Maybe Int -> Int -> Bool
limitExceeded = \case
  Nothing -> const False
  Just depth -> (> depth)
