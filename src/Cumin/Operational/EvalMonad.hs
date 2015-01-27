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

type Heap = M.Map VarName HeapItem

data HeapItem = LogicVar Type | HeapExp Exp
  deriving (Show)

type HeapExpPair = (Heap, Exp)

data Env = Env
  { _envADTs  :: M.Map String ADT
  , _envBinds :: M.Map String Binding
  }
  deriving (Show)

data EvalState = EvalState
  { _stateCounter :: Int
  , _stateHeap :: M.Map String HeapItem
  }
  deriving (Show)

$(makeLenses ''Env)
$(makeLenses ''EvalState)

newtype EvalT m a = EvalM { unEvalM :: StateT EvalState (ReaderT Env m) a }
  deriving (Functor, Applicative, Monad, MonadState EvalState, MonadReader Env, MonadPlus, Alternative)

instance MonadTrans EvalT where
  lift = EvalM . lift . lift

runEvalT :: Monad m => EvalT m a -> Env -> m a
runEvalT m = runReaderT (evalStateT (unEvalM m) emptyState)

runEvalWithHeapT :: Monad m => EvalT m a -> Env -> m (a, Heap)
runEvalWithHeapT m = runEvalT ((,) `liftM` m `ap` getHeap)

getHeap :: Monad m => EvalT m Heap
getHeap = use stateHeap

-- * Default values

emptyState :: EvalState
emptyState = EvalState
  { _stateCounter = 0
  , _stateHeap = M.empty
  }

makeEnv :: Module -> Env
makeEnv modul = Env
  { _envADTs = modul^.modADTs
  , _envBinds = modul^.modBinds
  }

-- * Fresh names

freshID :: Monad m => EvalT m Int
freshID = do
  stateCounter += 1
  use stateCounter

freshName :: Monad m => VarName -> EvalT m VarName
freshName v = idToName `liftM` freshID
  where
  -- TODO: Technically, it's not guaranteed that the name isn't already used in the program
  idToName i = "_" ++ show i ++ "_" ++ v

-- * Heap modifications

updateVarOnHeap :: Monad m => VarName -> Exp -> EvalT m ()
updateVarOnHeap v e = do
  currentItem <- use (stateHeap.at v)
  when (isNothing currentItem) $ error $ "Internal invariant violated: Variable " ++ v  ++ " should already be on the heap."
  stateHeap %= M.insert v (HeapExp e)

addToHeap :: Monad m => VarName -> HeapItem -> EvalT m VarName
addToHeap v e = do
  vName <- freshName v
  stateHeap %= M.insert vName e
  return vName

addExpToHeap :: Monad m => VarName -> Exp -> EvalT m VarName
addExpToHeap v = addToHeap v . HeapExp

addFreeToHeap :: Monad m => VarName -> Type -> EvalT m VarName
addFreeToHeap v = addToHeap v . LogicVar

lookupVar :: Monad m => VarName -> EvalT m (Maybe HeapItem)
lookupVar v = use (stateHeap.at v)

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
prettyHeapExpPair (e,heap) = prettyHeap heap PP.</> PP.text "⊢ " PP.<> prettyExp e

prettyHeap :: Heap -> PP.Doc
prettyHeap heap = PP.list $ map (\(v,item) -> PP.text v PP.<> PP.text " →" PP.</> prettyHeapItem item) $ M.toList heap

prettyHeapItem :: HeapItem -> PP.Doc
prettyHeapItem = \case
  LogicVar ty -> PP.text "free :: " PP.<> prettyType ty
  HeapExp e -> prettyExp e
