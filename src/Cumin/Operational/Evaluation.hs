{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
module Cumin.Operational.Evaluation where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.Reader
import           Cumin.Operational.EvalMonad
import           Cumin.Operational.NormalForms
import           Cumin.Operational.Tree
import           Cumin.Operational.Util
import           Data.List                     (elemIndex)
import           Data.Maybe
import           FunLogic.Core.AST
import           Language.CuMin.AST
import           Language.CuMin.Pretty

-- * Logical evaluation

-- | Evaluates the given expression logically.
-- This means the result is a value,
-- i.e. in flat normal form or a logic variable.
evaluateLogically :: Exp -> EvalT Tree Value
evaluateLogically expr = do
  maybeFNF' <- convertToValue expr
  case maybeFNF' of
    Just fnf' -> return fnf' -- VAL rule
    Nothing -> go
  where
  go = case expr of
    EVar v -> lookupVar v >>= \case
       Just heapItem -> case heapItem of
        LogicVar ty -> return $ Logic v ty
        -- LOOKUP rule:
        HeapExp e -> do
          e' <- withoutVar v $ evaluateLogically e
          updateVarOnHeap v (valueToExp e')
          return e'
       Nothing -> error $ "Variable " ++ v ++ " not found."
    -- LET rule:
    ELet v e1 e2 -> do
      vName <- addExpToHeap v e1
      evaluateLogically $ substitute1 TVar v vName e2
    -- FREE rule:
    ELetFree v ty e -> do
      vName <- addFreeToHeap v ty
      evaluateLogically $ substitute1 TVar v vName e
    -- no rule for failed:
    EFailed _ -> lift failure
    -- Try FUN rule:
    EFun _ _ -> tryFunRule [] expr >>= \case
      Just expression -> evaluateLogically expression
      Nothing -> error $ "Expression" ++ show (prettyExp expr) ++ " is already in FNF."
    EApp f e
    -- First, try to use FUN rule:
      | EVar v <- e -> tryFunRule [v] f >>= \case
        Just expression -> evaluateLogically expression
    -- If FUN fails, try APPLY rule:
        Nothing -> do
          f' <- evaluateLogically f
          evaluateLogically $ EApp (valueToExp f') e
    -- If this fails too, use FLATTEN rule:
      | otherwise -> do
        vName <- addExpToHeap "arg" e
        evaluateLogically $ EApp f (EVar vName)
    ELit _ -> error "Literal is already in FNF."
    -- PRIM rule:
    EPrim oper es -> do
      let [e1, e2] = es
      Literal (LNat n1) <- evaluateFunctionally e1
      Literal (LNat n2) <- evaluateFunctionally e2
      return $ case oper of
        PrimEq -> Fnf $ if n1 == n2 then ConValue "True" [] [] else ConValue "False" [] []
        PrimAdd -> Fnf . Literal . LNat $ n1 + n2
    ECon _ _ -> error $ "Constructor is already in FNF: " ++ show (prettyExp expr)
    -- CASE rules:
    ECase scrutinee alts -> do
      scrutinee' <- evaluateFunctionally scrutinee
      case scrutinee' of
        ConValue conName _ argVars ->
          tryAlts scrutinee' conName argVars alts
        _ -> error "Scrutinee is not a constructor value."

-- | Tries the given alternatives in order.
-- Returns whenever the first one matches.
tryAlts :: FNF -> DataConName -> [VarName] -> [Alt] -> EvalT Tree Value
tryAlts scrutinee conName argVars = go
  where
  go = \case
    (Alt pat e:als) -> case pat of
      PVar v -> do
        -- This is handled like let bindings: LET rule:
        vName <- addExpToHeap v (fnfToExp scrutinee)
        evaluateLogically $ substitute1 TVar v vName e
      -- CASE rule:
      PCon c vs | c == conName ->
        evaluateLogically $ substituteMany TVar vs argVars e
      _ -> go als
    [] -> lift failure

-- | Tries to apply the FUN rule.
-- It checks if a function is applied to enough arguments to reduce
-- the expression and if that is possible, does so.
tryFunRule :: Monad m => [VarName] -> Exp -> EvalT m (Maybe Exp)
tryFunRule args expr = case expr of
  EFun bindName tys -> do
    Just binding <- view (envBinds.at bindName)
    if length (binding^.bindingArgs) == length args
      then
        let bindArgs = binding^.bindingArgs
            bindExp = binding^.bindingExpr
            TyDecl bindTyArgs _ _ = binding^.bindingType
            tyVarSubst tyVar = tys !! fromJust (tyVar `elemIndex` bindTyArgs)
        in return . Just $ substituteMany tyVarSubst bindArgs args bindExp
      else return Nothing
  EApp f (EVar arg) -> tryFunRule (arg:args) f
  _ -> return Nothing

-- * Functional evaluation

-- | Evaluates the given heap expression pair functionally.
-- This means the result is in flat normal form.
evaluateFunctionally :: Exp -> EvalT Tree FNF
evaluateFunctionally = evaluateLogically >=> handleLogicVars

handleLogicVars :: Value -> EvalT Tree FNF
handleLogicVars fnfOrLogic = case fnfOrLogic of
  -- FNF rule:
  Fnf fnfValue -> return fnfValue
  -- GUESS rules:
  Logic v ty -> case ty of
    TCon "Nat" [] -> lift (branchNatLongerThan 0) >>= \n -> do
      updateVarOnHeap v (ELit (LNat n))
      return $ Literal (LNat n)
    TCon tcon tys -> do
      maybeADT <- view (envADTs.at tcon)
      case maybeADT of
        Nothing -> error $ "Logic variable's type is not an ADT: " ++ tcon
        Just adt -> lift (branch (adt^.adtConstr)) >>= guessRule v (adt^.adtTyArgs) tys
    TVar _ -> error "Logic variable doesn't have a concrete type."

-- | Apply the GUESS rule to a specific constructor.
guessRule
  :: VarName -- ^ the logic variable that is being evaluated
  -> [TVName] -- ^ the type var names of the ADT
  -> [Type] -- ^ the type instantiations for the ADT type vars
  -> ConDecl -- ^ the constructor declaration of the chosen constructor
  -> EvalT Tree FNF
guessRule v tvNames tyArgs conDecl@(ConDecl con _) = do
  let Just types = instantiateConDecl tvNames tyArgs conDecl
  conArgs <- mapM (addFreeToHeap "conArg") types
  let fnfValue = ConValue con tyArgs conArgs
  updateVarOnHeap v (fnfToExp fnfValue)
  return fnfValue

-- | Generates all natural numbers whose binary representation is longer than
-- the given parameter.
branchNatLongerThan :: Integer -> Tree Integer
branchNatLongerThan i = do
  b <- branch [True, False]
  if b then natsOfLength i else branchNatLongerThan (succ i)

-- | Generates all natural numbers who have the given number of binary digits.
natsOfLength :: Integer -> Tree Integer
natsOfLength i | i <= 0 = return 0
               | otherwise = branch [2 ^ (i - 1) .. 2 ^ i - 1]

-- * Forcing expressions

-- | Forces the expression to normal form.
-- It fully evaluates all constructor and function arguments.
force :: Exp -> EvalT Tree NF
force = evaluateFunctionally >=> \case
  PartialApp fun tys vs -> NfPartial fun tys <$> forceList vs
  ConValue con tys vs -> NfCon con tys <$> forceList vs
  Literal lit -> return $ NfLiteral lit
  where
  forceList = mapM (force . EVar)
