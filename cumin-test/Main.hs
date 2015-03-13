{-# LANGUAGE LambdaCase, QuasiQuotes #-}
module Main where

import Test.Hspec
import Cumin.Operational
import Language.CuMin
import qualified Data.Map as M
import Data.Default.Class
import qualified Text.PrettyPrint.ANSI.Leijen  as PP
import Data.Function

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Prelude tests" $ do
    Just modul <- runIO $ checkFile "cumin-test-files/Empty.cumin"
    it "maps not correctly" $
      let mapExp = [cuminExp| map<:Bool,Bool:> not<::> [True,False]<:Bool:>|]
      in shouldBeForcedTo modul mapExp [cuminExp|[False, True]<:Bool:>|]
    it "short-circuits and" $
      let andExp = [cuminExp| and<:Bool,Bool:> False failed<:Bool:>|]
      in shouldBeForcedTo modul andExp [cuminExp|False|]
  describe "Nat tests" $ do
    Just modul <- runIO $ checkFile "cumin-test-files/Nat.cumin"
    it "subtracts correctly" $
      shouldSatisfyForced modul [cuminExp|minus<::> 10000 5000|] [cuminExp|5000|]
        (shouldBe `on` head)
    it "multiplies correctly" $
          shouldSatisfyForced modul [cuminExp|times<::> 3 3|] [cuminExp|9|]
            (shouldBe `on` head)

shouldBeForcedTo :: Module -> Exp -> Exp -> Expectation
shouldBeForcedTo modul test expect =
  shouldSatisfyForced modul test expect shouldBe

shouldSatisfyForced :: Module -> Exp -> Exp -> ([NF] -> [NF] -> Expectation) -> Expectation
shouldSatisfyForced modul test expect f =
  f testForced expectForced
  where
  [testForced, expectForced] = map forceIt [test, expect]
  forceIt e = map snd . bfsTraverse Nothing . toTree $ runEvalT (force e) (makeEnv modul)

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
