{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TemplateHaskell            #-}
module Cumin.Operational.EvalMonad where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.Map                     as M
import           Data.Maybe
import           FunLogic.Core.AST
import           FunLogic.Core.Pretty
import           Language.CuMin.AST
import           Language.CuMin.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- * Types for evaluation

-- | A heap is a mapping from variable names to heap items.
type Heap = M.Map VarName HeapItem

-- | A heap item is a logic variable or an expression.
data HeapItem = LogicVar Type | HeapExp Exp
  deriving (Show)

-- | A heap expression pair.
type HeapExpPair = (Heap, Exp)

-- | Environment for evaluation.
data Env = Env
  { _envADTs  :: M.Map String ADT -- ^ ADTs of the program
  , _envBinds :: M.Map String Binding -- ^ function bindings of the program
  }
  deriving (Show)

-- | State of the evaluator.
data EvalState = EvalState
  { _stateCounter :: Int -- ^ counter for fresh variable names
  , _stateHeap :: M.Map String HeapItem -- ^ the heap for evaluation
  }
  deriving (Show)

$(makeLenses ''Env)
$(makeLenses ''EvalState)

-- | The evaluation transformer incorparates the environment and state of the evaluator.
newtype EvalT m a = EvalM { unEvalM :: StateT EvalState (ReaderT Env m) a }
  deriving (Functor, Applicative, Monad, MonadState EvalState, MonadReader Env, MonadPlus, Alternative)

instance MonadTrans EvalT where
  lift = EvalM . lift . lift

-- | Run the evaluation action in a given environment.
runEvalT :: Monad m => EvalT m a -> Env -> m a
runEvalT m = runReaderT (evalStateT (unEvalM m) emptyState)

-- | Run the evaluation action in a given environment and return the heap, too.
runEvalWithHeapT :: Monad m => EvalT m a -> Env -> m (a, Heap)
runEvalWithHeapT m = runEvalT ((,) `liftM` m `ap` getHeap)

-- | Return the current heap of an evaluation action.
getHeap :: Monad m => EvalT m Heap
getHeap = use stateHeap

-- * Default values

emptyState :: EvalState
emptyState = EvalState
  { _stateCounter = 0
  , _stateHeap = M.empty
  }

-- | Create an environment from a module.
makeEnv :: Module -> Env
makeEnv modul = Env
  { _envADTs = modul^.modADTs
  , _envBinds = modul^.modBinds
  }

-- * Fresh names

-- | Creates a fresh ID by increasing the state counter.
freshID :: Monad m => EvalT m Int
freshID = do
  stateCounter += 1
  use stateCounter

-- | Creates a fresh name by prepending a fresh ID.
freshName :: Monad m => VarName -> EvalT m VarName
freshName v = idToName `liftM` freshID
  where
  idToName i = "_" ++ show i ++ "_" ++ v

-- * Heap modifications

-- | Change the expression that a variable is bound to on the heap.
updateVarOnHeap :: Monad m => VarName -> Exp -> EvalT m ()
updateVarOnHeap v e = do
  currentItem <- use (stateHeap.at v)
  when (isNothing currentItem) $ error $ "Internal invariant violated: Variable " ++ v  ++ " should already be on the heap."
  stateHeap %= M.insert v (HeapExp e)

-- | Add a variable to the heap with an associated heap item (logic variable or expression).
-- The variable name is modified to ensure it is fresh on the heap and the new name is returned.
addToHeap :: Monad m => VarName -> HeapItem -> EvalT m VarName
addToHeap v e = do
  vName <- freshName v
  stateHeap %= M.insert vName e
  return vName

-- | Convenience function to add an expression to a heap, instead of a heap item.
addExpToHeap :: Monad m => VarName -> Exp -> EvalT m VarName
addExpToHeap v = addToHeap v . HeapExp

-- | Convenience function to add a logic variable to a heap, instead of a heap item.
addFreeToHeap :: Monad m => VarName -> Type -> EvalT m VarName
addFreeToHeap v = addToHeap v . LogicVar

-- | Look up the associated heap item of a variable in the heap.
lookupVar :: Monad m => VarName -> EvalT m (Maybe HeapItem)
lookupVar v = use (stateHeap.at v)

-- | Execute an action with a modified heap where one variable is removed.
withoutVar :: Monad m => VarName -> EvalT m a -> EvalT m a
withoutVar v m = do
  maybeItem <- lookupVar v
  let item = flip fromMaybe maybeItem . error $
        "Internal invariant violated: Variable " ++ v ++ " should be removed but doesn't exist in the first place."
  stateHeap %= M.delete v
  a <- m
  stateHeap %= M.insert v item
  return a

-- * Pretty printing

prettyHeapExpPair :: (Exp, Heap) -> PP.Doc
prettyHeapExpPair (e,heap) = prettyHeap heap PP.</> PP.text ": " PP.<> prettyExp e

prettyHeap :: Heap -> PP.Doc
prettyHeap heap = PP.list $ map (\(v,item) -> PP.text v PP.<> PP.text " ->" PP.</> prettyHeapItem item) $ M.toList heap

prettyHeapItem :: HeapItem -> PP.Doc
prettyHeapItem = \case
  LogicVar ty -> PP.text "free :: " PP.<> prettyType ty
  HeapExp e -> prettyExp e
