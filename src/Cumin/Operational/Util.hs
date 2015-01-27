{-# LANGUAGE LambdaCase, PatternSynonyms #-}
module Cumin.Operational.Util where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Cumin.Operational.EvalMonad
import           Cumin.Operational.NormalForms
import           Data.List                     (elemIndex)
import qualified Data.Map                      as M
import           FunLogic.Core.AST
import           Language.CuMin.AST

-- * Substitutions with fresh variables

-- | This assumes that the substituted var name are fresh!
substitute1 :: (TVName -> Type) -> VarName -> VarName -> Exp -> Exp
substitute1 f v w = substitute f (\x -> if x == v then Just w else Nothing)

-- | This assumes that the substituted var names are fresh!
substituteMany :: (TVName -> Type) -> [VarName] -> [VarName] -> Exp -> Exp
substituteMany f vs ws = substitute f (\x -> (ws !!) <$> x `elemIndex` vs)

-- | This assumes that the substituted var names are fresh!
-- Otherwise variables can get captured
substitute :: (TVName -> Type) -> (VarName -> Maybe VarName) -> Exp -> Exp
substitute f subs e = case e of
  EVar v -> case subs v of
    Just w -> EVar w
    Nothing -> e
  ELet v e1 e2 -> ELet v (substitute f subs e1) (substitute f (\x -> if x == v then Nothing else subs x) e2)
  ELetFree v ty ex -> ELetFree v (substituteInType f ty) (substitute f (\x -> if x == v then Nothing else subs x) ex)
  EFailed ty -> EFailed (substituteInType f ty)
  EFun fun tys -> EFun fun (map (substituteInType f) tys)
  EApp e1 e2 -> EApp (substitute f subs e1) (substitute f subs e2)
  ELit _ -> e
  EPrim oper es -> EPrim oper (map (substitute f subs) es)
  ECon c tys -> ECon c (map (substituteInType f) tys)
  ECase scrutinee alts -> ECase (substitute f subs scrutinee) (map (substituteAlt f subs) alts)

-- | This assumes that the substituted var names are fresh!
substituteAlt :: (TVName -> Type) -> (VarName -> Maybe VarName) -> Alt -> Alt
substituteAlt f subs (Alt pat e) = case pat of
  PCon _ vs -> Alt pat (substitute f (\x -> if x `elem` vs then Nothing else subs x) e)
  PVar v -> Alt pat (substitute f (\x -> if x == v then Nothing else subs x) e)

substituteInType :: (TVName -> Type) -> Type -> Type
substituteInType f = \case
  TVar v -> f v
  TCon c tys -> TCon c $ map (substituteInType f) tys

-- * Conversions to normal forms if possible

convertToFNF :: Monad m => Exp -> EvalT m (Maybe FNF)
convertToFNF = go []
  where
  go args = \case
    ELit lit -> return . Just $ Literal lit
    EApp f (EVar v) -> go (v:args) f
    ECon c tys -> return . Just $ ConValue c tys args
    EFun f tys -> do
      Just numArgs <- fmap (length . _bindingArgs) `liftM` view (envBinds.at f)
      return $
        if numArgs > length args
        then Just $ PartialApp f tys args
        else Nothing
    _ -> return Nothing

convertToValue :: Monad m => Exp -> EvalT m (Maybe Value)
convertToValue expr = case expr of
  EVar v -> lookupVar v >>= \case
    Just (LogicVar ty) -> return . Just $ Logic v ty
    _ -> fnf
  _ -> fnf
  where
  fnf = fmap Fnf `liftM` convertToFNF expr

-- * Type helper

instantiateConDecl :: [String] -> [Type] -> ConDecl -> Maybe [Type]
instantiateConDecl tyVars tyArgs (ConDecl _ tys) = do
  let
    subst = M.fromList $ zip tyVars tyArgs
    replaceVar (TVar v) = M.lookup v subst
    replaceVar x = return x
  mapM (transformM replaceVar) tys
