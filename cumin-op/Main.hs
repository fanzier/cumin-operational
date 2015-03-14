{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
module Main (main) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.State
import           Cumin.Operational
import           Data.Default.Class
import qualified Data.Map                      as M
import           Data.Monoid
import qualified Data.Set                      as Set
import           FunLogic.Core.TypeChecker
import           Language.CuMin.AST
import           Language.CuMin.ModBuilder
import qualified Language.CuMin.ModBuilder     as CM
import qualified Language.CuMin.Parser         as CP
import           Language.CuMin.Prelude        (preludeModule)
import           Language.CuMin.Pretty
import           Language.CuMin.TypeChecker
import           System.Console.Haskeline
import           System.CPUTime
import           System.Environment            (getArgs)
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen  as PP
import           Text.Printf
import           Text.Trifecta

-- * Types

-- | The state of the program
data ReplState = ReplState
  { _strategy :: SearchStrategy -- ^ how to search the computation tree, e.g. BFS
  , _depth    :: Maybe Int      -- ^ depth limit for the search
  , _file     :: String         -- ^ name of the loaded module
  , _replMod  :: Module         -- ^ currently loaded module
  }

data SearchStrategy
  = BFS
  | DFS

-- | A setting of the program
data Property = Property
  { _propertyP           :: Parser (ReplState -> ReplState)
  , _propertyName        :: String
  , _propertyDescription :: String
  , _propertyGet         :: ReplState -> String
  }

-- | A command is parsed user input.
data Command
  = Quit
  | Help
  | Reload
  | Eval Exp
  | Force Exp
  | SetProperty (ReplState -> ReplState)
  | GetProperties

makeLenses ''Property
makeLenses ''ReplState
makeLenses ''SearchStrategy

-- * Default values

defaultState :: ReplState
defaultState = ReplState
  { _strategy = BFS
  , _depth = Nothing
  , _file = ""
  , _replMod = preludeModule
  }

properties :: M.Map String Property
properties = M.fromList
  [ ("depth", Property
    { _propertyName = "depth"
    , _propertyP = set depth <$> ((Nothing <$ string "inf") <|> (Just . fromInteger <$> natural))
    , _propertyDescription = "The search depth limit. Values: inf, 0, 1, 2, ..."
    , _propertyGet = view depth >>= \case
        Just d -> return $ show d
        Nothing -> return "inf"
    })
  , ("strategy", Property
      { _propertyName = "strategy"
      , _propertyP = set strategy <$> ((BFS <$ string "bfs") <|> (DFS <$ string "dfs"))
      , _propertyDescription = "The search strategy: bfs, dfs"
      , _propertyGet = view strategy >>= \case
          BFS -> return "bfs"
          DFS -> return "dfs"
      })
  ]

-- * Parsers

commandP :: Parser Command
commandP
  = (do
      void $ char ':'
      cmd <- some letter
      void $ many space
      case cmd of
        "s" -> setPropertyP
        "set" -> setPropertyP
        "g" -> getPropertiesP
        "get" -> getPropertiesP
        "f" -> forceP
        "force" -> forceP
        "e" -> evalP
        "eval" -> evalP
        "q" -> quitP
        "r" -> reloadP
        "reload" -> reloadP
        "quit" -> quitP
        "help" -> helpP
        "h" -> helpP
        _ -> fail $ "Unknown command: " ++ cmd
    )
  <|> forceP

quitP :: Parser Command
quitP = pure Quit

helpP :: Parser Command
helpP = pure Help

reloadP :: Parser Command
reloadP = pure Reload

evalP :: Parser Command
evalP = Eval <$> expressionP

forceP :: Parser Command
forceP = Force <$> expressionP

setPropertyP :: Parser Command
setPropertyP = do
  prop <- some letter <* char '='
  case properties^.at prop of
    Just property -> SetProperty <$> property^.propertyP
    Nothing -> fail $ "Unknown property: " ++ prop

getPropertiesP :: Parser Command
getPropertiesP = GetProperties <$ spaces

expressionP :: Parser Exp
expressionP = CP.postProcessExp Set.empty <$> CP.runCuMinParser "<interactive>" CP.expression

-- * Actual program

main :: IO ()
main = getArgs >>= \case
  [cuminFile] -> do
    putStrLn "Type \":h\" (without quotes) for help."
    evalStateT (loadModule cuminFile >> repl) defaultState
  _ -> putStrLn "Usage: cumin-op Module.cumin\nExactly one input file must be specified."

loadModule :: MonadIO m => String -> StateT ReplState m ()
loadModule cuminFile = do
  m <- liftIO $ checkFile cuminFile
  file .= cuminFile
  case m of
    Just modul -> do
      replMod .= modul
      liftIO $ putStrLn $ "Loaded module `" ++ _modName modul ++ "`."
    Nothing -> liftIO $ putStrLn $ "Loading file `" ++ cuminFile ++ "` failed."

checkFile :: FilePath -> IO (Maybe Module)
checkFile cuminFile =
  CM.buildModuleFromFile cuminFile >>= \case
      Left msg -> PP.putDoc (PP.pretty msg) >> return Nothing
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

repl :: StateT ReplState IO ()
repl = mapStateT (runInputT defaultSettings) loop

loop :: StateT ReplState (InputT IO) ()
loop = do
  minput <- lift $ getInputLine "> "
  modul <- use replMod
  let env = makeEnv modul
  case minput of
    Nothing -> loop
    Just input -> case parseString (commandP <* eof) mempty input of
      Failure msg -> liftIO (PP.putDoc $ msg PP.<> PP.line) >> loop
      Success cmd -> case cmd of
        Quit -> liftIO $ putStrLn "Bye."
        Reload -> use file >>= loadModule >> loop
        Eval expr -> timedAndInterruptible (printExprTypeAndThen expr (evalExpr env)) >> loop
        Force expr -> timedAndInterruptible (printExprTypeAndThen expr (forceExpr env)) >> loop
        SetProperty f -> modify f >> loop
        GetProperties -> prettyProperties >>= liftIO . PP.putDoc >> loop
        Help -> liftIO (PP.putDoc $ prettyHelp PP.<> PP.line) >> loop
  where
  forceExpr env _ expr = do
    let forcedExp = runEvalT (force expr) env
    traverseStrategy <- whichTraversal
    liftIO $ printResults printNFResult traverseStrategy forcedExp
  printNFResult (_, nf) = do
    PP.putDoc $ PP.text " = " PP.<> (PP.hang 2 . prettyExp . nfToExp) nf <> PP.line
    hFlush stdout
  evalExpr env _ expr = do
    let expHeapPair = runEvalWithHeapT (evaluateFunctionally expr) env
    traverseStrategy <- whichTraversal
    liftIO $ printResults printFNFResult traverseStrategy expHeapPair
  printFNFResult (_, (fnf, heap)) = do
    PP.putDoc $ PP.text " ~> " PP.<> (PP.hang 2 . prettyHeapExpPair) (fnfToExp fnf, heap) PP.<> PP.line
    hFlush stdout
  whichTraversal = do
    traverseFunction <- use strategy >>= \case
      BFS -> return bfsTraverse
      DFS -> return dfsTraverse
    depthLimit <- use depth
    return $ traverseFunction depthLimit

timedAndInterruptible :: StateT ReplState (InputT IO) () -> StateT ReplState (InputT IO) ()
timedAndInterruptible action = do
  state <- get
  startTime <- liftIO getCPUTime
  let handler = do
        outputStrLn "Interrupted."
        liftIO $ printTimeElapsed startTime
  lift . withInterrupt . handleInterrupt handler . flip evalStateT state $ do
    action
    liftIO $ printTimeElapsed startTime
  where
  printTimeElapsed startTime = do
    endTime <- getCPUTime
    let elapsed = realToFrac (endTime - startTime) / (1e12 :: Double)
    putStrLn $ "\nCPU time elapsed: " ++ printf "%.3f s" elapsed


-- * Helper functions

printExprTypeAndThen :: Exp -> (Type -> Exp -> StateT ReplState (InputT IO) ()) -> StateT ReplState (InputT IO) ()
printExprTypeAndThen expr cont = checkInteractiveExpr expr >>= \case
  Left tyerr -> liftIO $ PP.putDoc $ PP.pretty tyerr PP.<> PP.line
  Right ty -> do
    liftIO $ PP.putDoc $ PP.text " :: " PP.<> prettyType ty PP.<> PP.line
    cont ty expr

checkInteractiveExpr :: MonadState ReplState m => Exp -> m (Either (TCErr CuMinErrCtx) Type)
checkInteractiveExpr expr = do
  interactiveMod <- use replMod
  return $ evalTC' $ do
    includeBuiltIns
    unsafeIncludeModule interactiveMod
    checkExp expr

-- | Print a tree using a pretty printer for leafs and a traversal function.
printResults :: ((Int, a) -> IO ()) -> (Tree a -> [(Int, a)]) -> TreeM a -> IO ()
printResults pp trav tree = mapM_ pp (trav (toTree tree))

prettyHelp :: PP.Doc
prettyHelp = PP.text "List of commands:" PP.<$>
  PP.vsep (map (PP.hang 8 . (PP.text " * " PP.<>))
    [ PP.text ":h, :help" PP.<$> PP.text "Show this help text."
    , PP.text ":q, :quit" PP.<$> PP.text "Quit the program."
    , PP.text ":r, :reload" PP.<$> PP.text "Reload the current module."
    , PP.text ":f <expr>, :force <expr>, <expr>" PP.<$> PP.text "Force the expression <expr> to reduced normal form."
    , PP.text ":e <expr>, :eval <expr>" PP.<$> PP.text "Evaluate the expression <expr> to flat normal form."
    , PP.text ":g, :get" PP.<$> PP.text "List all configurable properties and their current values."
    , PP.text ":s <prop>=<val>, :set <prop>=<val>" PP.<$> PP.text "Set property <prop> to value <val>. For details use ':get'."
    ]
  )

prettyProperties :: StateT ReplState (InputT IO) PP.Doc
prettyProperties =  ((PP.text "Current settings:" PP.<> PP.line) PP.<>) <$> do
  s <- get
  return $ PP.vsep (map (prettyProperty s) (M.elems properties)) PP.<> PP.line
  where
  prettyProperty s a =
    PP.text " * " PP.<> PP.align (
      PP.text (a^.propertyName) PP.<>
      PP.text "=" PP.<> PP.text (a^.propertyGet $ s) PP.<>
      PP.text ": " PP.</> PP.text (a^.propertyDescription)
    )
