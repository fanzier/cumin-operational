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
  describe "Coin tests" $ do
    Just modul <- runIO $ checkFile "cumin-test-files/Coin.cumin"
    it "coin + coin gives right number of results" $
      length (evalOperational modul [cuminExp|coin<::> + coin<::>|]) `shouldBe` 4
    it "double coin gives right number of results" $
      length (evalOperational modul [cuminExp|double<::> coin<::>|]) `shouldBe` 2
    it "map maybeDouble1 gives right number of results" $
          length (evalOperational modul [cuminExp|map<:Nat,Nat:> maybeDouble1<::> [1,3]<:Nat:>|]) `shouldBe` 2
    it "map maybeDouble2 gives right number of results" $
          length (evalOperational modul [cuminExp|map<:Nat,Nat:> maybeDouble2<::> [1,3]<:Nat:>|]) `shouldBe` 4
  describe "List tests" $ do
    Just modul <- runIO $ checkFile "cumin-test-files/List.cumin"
    it "permute gives right number of results" $
      length (evalOperational modul [cuminExp|permute<:Nat:> [1,2,3,4]<:Nat:>|]) `shouldBe` 24
    describe "list sorting works" $
      shouldBeForcedTo modul [cuminExp|sort<::> [three<::>, two<::>, one<::>]<:Peano:>|] [cuminExp|[one<::>,two<::>,three<::>]<:Peano:>|]
    describe "last function works" $
      shouldSatisfyForced modul [cuminExp|last<:Bool:> [True, True, False, True]<:Bool:>|] [cuminExp|True|]
        (shouldBe `on` head)
  describe "Miscellaneous tests" $ do
    Just modul <- runIO $ checkFile "cumin-test-files/Misc.cumin"
    describe "right case semantics" $ do
      describe "test 1" $
        shouldBeForcedTo modul [cuminExp|caseFailure<:Bool:> []<:Bool:>|] [cuminExp|failed<:List Bool:>|]
      describe "test 2" $
        shouldBeForcedTo modul [cuminExp|caseFailure<:Bool:> [1]<:Bool:>|] [cuminExp|[1]<:Bool:>|]
      describe "test 3" $
        shouldBeForcedTo modul [cuminExp|caseFailure<:Bool:> failed<:List Bool:>|] [cuminExp|failed<:List Bool:>|]
    describe "let shadowing works correctly" $
      shouldBeForcedTo modul [cuminExp|letTest0<::>|] [cuminExp|0|]

-- | Specifies that the normal forms of the two given expressions should be the same.
shouldBeForcedTo :: Module -> Exp -> Exp -> Spec
shouldBeForcedTo modul test expect =
  shouldSatisfyForced modul test expect shouldBe

-- | Specifies that the normal forms of the two given expressions should satisfy a condition.
shouldSatisfyForced :: Module -> Exp -> Exp -> ([NF] -> [NF] -> Expectation) -> Spec
shouldSatisfyForced modul test expect f = do
  it "evaluates as expected" $ f testForced expectForced
  it "matches the denotational semantics" $ f testForced denotational
  where
  [testForced, expectForced] = map (evalOperational modul) [test, expect]
  denotational = evalDenotational modul test

-- | Force an expression to reduced normal form, operationally.
evalOperational :: Module -> Exp -> [NF]
evalOperational modul e = bfsTraverse Nothing . toTree $ runEvalT (force e) (makeEnv modul)

-- | Force an expression to reduced normal form, denotationally.
evalDenotational :: Module -> Exp -> [NF]
evalDenotational modul e = mapMaybe toNf $ Search.observeAll (CD.runEval (CD.eval e) modul CD.StepInfinity id :: BFSMonad (CD.Value BFSMonad))

-- | Transforms a Value to NF if it contains no bottoms are partial function applications.
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
