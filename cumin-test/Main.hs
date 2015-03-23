{-# LANGUAGE LambdaCase, QuasiQuotes #-}
module Main where

import Test.Hspec
import Cumin.Operational
import Language.CuMin
import qualified Data.Map as M
import Data.Default.Class
import qualified Text.PrettyPrint.ANSI.Leijen  as PP
import Data.Function
import qualified FunLogic.Semantics.Search as Search
import qualified Language.CuMin.Semantics.Denotational as CD
import Data.Maybe (mapMaybe)
import qualified Control.Monad.Logic as Logic
import Control.Applicative
import Data.Traversable

-- | Monad with depth-first-search characteristics.
type DFSMonad = Search.UnFair Logic.Logic
-- | Monad with breadth-first-search characteristics.
type BFSMonad = Logic.Logic

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Prelude tests" $ do
    Just modul <- runIO $ checkFile "cumin-test-files/Empty.cumin"
    describe "maps not correctly" $
      let mapExp = [cuminExp| map<:Bool,Bool:> not<::> [True,False]<:Bool:>|]
      in shouldBeForcedTo modul mapExp [cuminExp|[False, True]<:Bool:>|]
    describe "short-circuits and" $
      let andExp = [cuminExp| and<:Bool,Bool:> False failed<:Bool:>|]
      in shouldBeForcedTo modul andExp [cuminExp|False|]
  describe "Nat tests" $ do
    Just modul <- runIO $ checkFile "cumin-test-files/Nat.cumin"
    describe "subtracts correctly" $
      shouldSatisfyForced modul [cuminExp|minus<::> 10000 5000|] [cuminExp|5000|]
        (shouldBe `on` head)
    describe "multiplies correctly" $
          shouldSatisfyForced modul [cuminExp|times<::> 3 3|] [cuminExp|9|]
            (shouldBe `on` head)

shouldBeForcedTo :: Module -> Exp -> Exp -> Spec
shouldBeForcedTo modul test expect =
  shouldSatisfyForced modul test expect shouldBe

shouldSatisfyForced :: Module -> Exp -> Exp -> ([NF] -> [NF] -> Expectation) -> Spec
shouldSatisfyForced modul test expect f = do
  it "evaluates as expected" $ f testForced expectForced
  it "matches the denotational semantics" $ f testForced denotational
  where
  [testForced, expectForced] = map (evalOperational modul) [test, expect]
  denotational = evalDenotational modul test

evalOperational :: Module -> Exp -> [NF]
evalOperational modul e = bfsTraverse Nothing . toTree $ runEvalT (force e) (makeEnv modul)

evalDenotational :: Module -> Exp -> [NF]
evalDenotational modul e = mapMaybe toNf $ Search.observeAll (CD.runEval (CD.eval e) modul CD.StepInfinity id :: BFSMonad (CD.Value BFSMonad))

toNf :: CD.Value n -> Maybe NF
toNf = \case
  CD.VCon c vs tys -> NfCon c tys <$> traverse toNf vs
  CD.VNat i -> Just $ NfLiteral (LNat i)
  _ -> Nothing

checkFile :: FilePath -> IO (Maybe Module)
checkFile cuminFile =
  buildModuleFromFile cuminFile >>= \case
      Left msg -> print msg >> return Nothing
      Right modul ->
        case importUnqualified modul preludeModule of
          Left (adtConflicts, functionConflicts) -> do
            putStrLn "Some names in the module conflict with prelude names:"
            mapM_ (putStrLn . fst) (M.toList adtConflicts)
            mapM_ (putStrLn . fst) (M.toList functionConflicts)
            return Nothing
          Right modulWithPrelude -> case evalTC (checkModule modulWithPrelude) def def of
            Left msg -> PP.putDoc (PP.pretty msg) >> return Nothing
            Right () -> return $ Just modulWithPrelude
