{-# LANGUAGE LambdaCase, QuasiQuotes, RankNTypes #-}
module Main where

import Cumin.Operational
import Language.CuMin
import qualified Data.Map as M
import Data.Default.Class
import qualified Text.PrettyPrint.ANSI.Leijen  as PP
import Criterion.Main
import Control.DeepSeq (NFData (..))

instance NFData NF where
  rnf (NfPartial _ _ args) = rnf args
  rnf (NfCon _ _ args) = rnf args
  rnf (NfLiteral (LNat n)) = rnf n

main :: IO ()
main = do
  Just modul <- checkFile "cumin-test-files/Benchmark.cumin"
  defaultMain
    [ benchExp modul "PeanoSub" [cuminExp|benchSub<::>|]
    , benchExp modul "PeanoDiv" [cuminExp|benchDiv<::>|]
    , benchExp modul "Last" [cuminExp|benchLast<::>|]
    , benchExp modul "PermSort" [cuminExp|benchSort<::>|]
    , benchExpFirst modul "NatSub" [cuminExp|benchNatSub<::>|]
    , benchExpFirst modul "NatTimes" [cuminExp|benchNatTimes<::>|]
    ]
  where
  -- | Compute all values of the expression.
  benchExp modul name exp = bgroup name
    [ bench "DFS" $ nf (forceExp dfsTraverse modul) exp
    , bench "BFS" $ nf (forceExp bfsTraverse modul) exp
    ]
  -- | Compute the first value of the expression.
  benchExpFirst modul name exp = bgroup name
      [ bench "DFS" $ nf (head . forceExp dfsTraverse modul) exp
      , bench "BFS" $ nf (head . forceExp bfsTraverse modul) exp
      ]

forceExp :: (forall a. Maybe Int -> Tree a -> [a]) -> Module -> Exp -> [NF]
forceExp traversal modul e = traversal Nothing . toTree $ runEvalT (force e) (makeEnv modul)

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
