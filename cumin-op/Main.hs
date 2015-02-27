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
import qualified Text.PrettyPrint.ANSI.Leijen  as PP
import           Text.Printf
import           Text.Trifecta

-- * Types

-- | The state of the program
data ReplState = ReplState
  { _strategy :: SearchStrategy -- ^ how to search the computation tree, e.g. BFS
  , _depth    :: Maybe Int      -- ^ depth limit for the search
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
  | Eval Exp
  | Force Exp
  | SetProperty (ReplState -> ReplState)
  | GetProperties

makeLenses ''Property
makeLenses ''ReplState
makeLenses ''SearchStrategy

-- * Default values

defaultState :: Module -> ReplState
defaultState modul = ReplState
  { _strategy = BFS
  , _depth = Nothing
  , _replMod = modul
  }

properties :: M.Map String Property
properties = M.fromList
  [ ("depth", Property
    { _propertyName = "depth"
    , _propertyP = set depth <$> ((Nothing <$ string "none") <|> (Just . fromInteger <$> natural))
    , _propertyDescription = "The search depth limit. Values: none, 0, 1, 2, ..."
    , _propertyGet = view depth >>= \case
        Just d -> return $ show d
        Nothing -> return "none"
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
    modul <- checkFile cuminFile
    putStrLn $ "Loaded module `" ++ _modName modul ++ "`."
    putStrLn "Type \":h\" (without quotes) for help."
    evalStateT repl (defaultState modul)
  _ -> putStrLn "Usage: cumin-op Module.cumin\nExactly one input file must be specified."

checkFile :: FilePath -> IO Module
checkFile cuminFile =
  CM.buildModuleFromFile cuminFile >>= \case
      Left msg -> error $ show msg
      Right modul ->
        case importUnqualified modul preludeModule of
          Left conflicts -> error $ show conflicts
          Right modulWithPrelude -> case evalTC (checkModule modulWithPrelude) def def of
            Left msg -> error $ show $ PP.pretty msg
            Right () -> return modulWithPrelude

repl :: StateT ReplState IO ()
repl = mapStateT (runInputT defaultSettings) loop

loop :: StateT ReplState (InputT IO) ()
loop = do
  minput <- lift $ getInputLine "> "
  modul <- use replMod
  let env = makeEnv modul
  case minput of
    Nothing -> loop
    Just input -> case parseString commandP mempty input of
      Failure msg -> liftIO (PP.putDoc $ msg PP.<> PP.line) >> loop
      Success cmd -> case cmd of
        Quit -> liftIO $ putStrLn "Bye."
        Eval expr -> timedAndInterruptible (printExprTypeAndThen expr (evalExpr env)) >> loop
        Force expr -> timedAndInterruptible (printExprTypeAndThen expr (forceExpr env)) >> loop
        SetProperty f -> modify f >> loop
        GetProperties -> prettyProperties >>= liftIO . PP.putDoc >> loop
        Help -> liftIO (PP.putDoc $ prettyHelp PP.<> PP.line) >> loop
  where
  forceExpr env _ expr = do
    let forcedExp = runEvalT (force expr) env
    traverseStrategy <- whichTraversal
    liftIO $ PP.putDoc $ prettyTraverse prettyNFResult traverseStrategy forcedExp
  prettyNFResult nf = PP.text " = " PP.<> (PP.hang 2 . prettyExp . nfToExp) nf
  evalExpr env _ expr = do
    let expHeapPair = runEvalWithHeapT (evaluateFunctionally expr) env
    traverseStrategy <- whichTraversal
    liftIO $ PP.putDoc $ prettyTraverse prettyFNFResult traverseStrategy expHeapPair
  prettyFNFResult (fnf, heap) = PP.text " ~> " PP.<> (PP.hang 2 . prettyHeapExpPair) (fnfToExp fnf, heap)
  whichTraversal = do
    traverseFunction <- use strategy >>= \case
      BFS -> return bfsTraverse
      DFS -> return dfsTraverse
    depthLimit <- use depth
    return $ traverseFunction depthLimit

timedAndInterruptible :: StateT ReplState (InputT IO) () -> StateT ReplState (InputT IO) ()
timedAndInterruptible action = do
  state <- get
  let handler = outputStrLn "Interrupted." >> evalStateT loop state
  lift . withInterrupt . handleInterrupt handler . flip evalStateT state $ do
    startTime <- liftIO getCPUTime
    action
    endTime <- liftIO getCPUTime
    let elapsed = realToFrac (endTime - startTime) / (1e12 :: Double)
    lift $ outputStrLn $ "CPU time elapsed: " ++ printf "%.3f s" elapsed


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

prettyHelp :: PP.Doc
prettyHelp = PP.text "List of commands:" PP.<$>
  PP.vsep (map (PP.hang 8 . (PP.text " * " PP.<>))
    [ PP.text ":h, :help" PP.<$> PP.text "Show this help text."
    , PP.text ":q, :quit" PP.<$> PP.text "Quit the program."
    , PP.text ":f <expr>, :force <expr>, <expr>" PP.<$> PP.text "Force the expression <expr> to head normal form."
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
