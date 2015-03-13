{-# LANGUAGE LambdaCase #-}
module Cumin.Operational.NormalForms where

import           FunLogic.Core.AST
import           Language.CuMin.AST

-- | An expression that is in flat normal form
data FNF
  = PartialApp BindingName [Type] [VarName]
  | ConValue DataConName [Type] [VarName]
  | Literal Lit
  deriving (Show, Eq)

-- | An expression that is in flat normal form or a logic variable
data Value
  = Fnf FNF
  | Logic VarName Type
  deriving (Show, Eq)

-- | An expression that is in normal form, i.e. fully evaluated.
data NF
  = NfPartial BindingName [Type] [NF]
  | NfCon DataConName [Type] [NF]
  | NfLiteral Lit
  deriving (Show, Eq)

-- * Conversion functions

fnfToExp :: FNF -> Exp
fnfToExp = \case
  PartialApp fun tys es ->
    let go [] = EFun fun tys
        go (x:xs) = EApp (go xs) (EVar x)
    in go (reverse es)
  ConValue conName tys es ->
    let go [] = ECon conName tys
        go (x:xs) = EApp (go xs) (EVar x)
    in go (reverse es)
  Literal lit -> ELit lit

valueToExp :: Value -> Exp
valueToExp = \case
  Fnf fnf -> fnfToExp fnf
  Logic varName _ -> EVar varName

nfToExp :: NF -> Exp
nfToExp = \case
  NfPartial fun tys es ->
    let go [] = EFun fun tys
        go (x:xs) = EApp (go xs) (nfToExp x)
    in go (reverse es)
  NfCon conName tys es ->
    let go [] = ECon conName tys
        go (x:xs) = EApp (go xs) (nfToExp x)
    in go (reverse es)
  NfLiteral lit -> ELit lit
