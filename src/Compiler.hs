{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Compiler (runCli) where

import Accounting (Acc (..), AccError)
import Codegen (Gen (..), JsStat, generateProgram, renderJsProg)
import Common
  ( Has (..),
    HasNameSupply (..),
    HasProjectFiles (getProjectFileContents),
    Loc (..),
    Logger (..),
    Name (..),
    Parent (..),
    Qty (Many),
    Try (..),
  )
import Control.Monad (void, when)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT, tryError)
import Control.Monad.Extra (unless)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState (..), StateT (..))
import Control.Monad.State.Class (gets)
import qualified Control.Monad.State.Class as ST
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq)
import Data.String
import Data.Text.IO (hPutStrLn)
import Elaboration (Elab (..), ElabError, elabProgram)
import Evaluation (Eval (..))
import Globals (Sig, emptySig)
import Meta (SolvedMetas, emptySolvedMetas)
import Options.Applicative (auto, execParser, option, value, (<**>), (<|>))
import Options.Applicative.Builder
  ( fullDesc,
    header,
    help,
    info,
    long,
    progDesc,
    short,
    strOption,
    switch,
  )
import Options.Applicative.Common (Parser)
import Options.Applicative.Extra (helper)
import Parsing (ParseError, parseProgram)
import Persistence (bootPath, preludePath)
import Presyntax (PProgram)
import Printing (Pretty (..))
import Representation (reprInfSig)
import System.Exit (exitFailure)
import System.IO (stderr)
import Typechecking
  ( Ctx,
    Goal,
    InPat (..),
    Problem,
    SolveAttempts (..),
    Tc (addGoal, tcError),
    TcError,
    emptyCtx,
    prettyGoal,
  )
import Unelaboration (Unelab, unelabSig)

-- import Resources.Prelude (preludePath, preludeContents)

-- | What mode to run in.
data Mode
  = -- | Typecheck a file.
    CheckFile String
  | -- | Parse a file
    ParseFile String
  | -- | Represent a file
    RepresentFile String
  | -- | Generate code
    GenerateCode String
  deriving (Show)

-- | Command-line flags.
data Flags = Flags
  { -- | Whether to dump the program.
    dump :: Bool,
    -- | Whether to be verbose.
    verbose :: Bool,
    -- | Normalise the program in the end.
    noNormalise :: Bool,
    -- | Amount of solve attempts for metas.
    attempts :: Int
  }
  deriving (Show)

-- | Command-line arguments.
data Args = Args
  { mode :: Mode,
    flags :: Flags
  }
  deriving (Show)

argsFile :: Args -> String
argsFile (Args (CheckFile f) _) = f
argsFile (Args (ParseFile f) _) = f
argsFile (Args (RepresentFile f) _) = f
argsFile (Args (GenerateCode f) _) = f

-- | Parse the command-line flags.
parseFlags :: Parser Flags
parseFlags =
  Flags
    <$> switch (long "dump" <> short 'd' <> help "Print the parsed program")
    <*> switch (long "verbose" <> short 'v' <> help "Be verbose")
    <*> switch (long "no-normalise" <> short 'n' <> help "Do not normalise the program (might cause weird things to happen)")
    <*> option auto (long "attempts" <> short 'a' <> help "Amount of solve attempts for metas" <> value 1)

-- | Parse the mode to run in.
parseMode :: Parser Mode
parseMode =
  (CheckFile <$> strOption (long "check" <> short 'c' <> help "File to check"))
    <|> (ParseFile <$> strOption (long "parse" <> short 'p' <> help "File to parse"))
    <|> (RepresentFile <$> strOption (long "represent" <> short 'r' <> help "File to represent"))
    <|> (GenerateCode <$> strOption (long "generate" <> short 'g' <> help "File to generate code for"))

-- | Parse the command line arguments.
parseArgs :: Parser Args
parseArgs = Args <$> parseMode <*> parseFlags

-- | Run the main CLI.
runCli :: IO ()
runCli = do
  args <- execParser opts
  runComp (compile args) emptyCompiler
  where
    opts =
      info
        (parseArgs <**> helper)
        ( fullDesc
            <> progDesc "Superfluid is a dependently typed programming language with customisable type representations"
            <> header "Superfluid"
        )

-- | Log a message to stderr and exit with an error code.
err :: String -> Comp a
err m = liftIO $ do
  hPutStrLn stderr $ fromString m
  exitFailure

data Compiler = Compiler
  { files :: Map String String,
    solvedMetas :: SolvedMetas,
    ctx :: Ctx,
    sig :: Sig,
    inPat :: InPat,
    currentLoc :: Loc,
    normaliseProgram :: Bool,
    goals :: [Goal],
    lastNameIdx :: Int,
    reduceUnfoldDefs :: Bool,
    solveAttempts :: SolveAttempts,
    problems :: Seq Problem,
    qty :: Qty,
    codegenStatements :: [JsStat]
  }

data CompilerError
  = TcCompilerError TcError
  | ParseCompilerError ParseError
  | ElabCompilerError ElabError
  | AccCompilerError AccError

instance Pretty Comp CompilerError where
  pretty e = do
    x <- case e of
      TcCompilerError a -> pretty a
      ParseCompilerError a -> pretty a
      ElabCompilerError a -> pretty a
      AccCompilerError a -> pretty a
    return $ ">> " ++ x

newtype Comp a = Comp {unComp :: ExceptT CompilerError (StateT Compiler IO) a}
  deriving (Functor, Applicative, Monad, MonadState Compiler, MonadError CompilerError, MonadIO)

instance Has Comp SolvedMetas where
  view = gets (\c -> c.solvedMetas)
  modify f = ST.modify (\s -> s {solvedMetas = f s.solvedMetas})

instance Has Comp Sig where
  view = gets (\c -> c.sig)
  modify f = ST.modify (\s -> s {sig = f s.sig})

instance HasNameSupply Comp where
  uniqueName = do
    n <- gets (\c -> c.lastNameIdx)
    ST.modify (\s -> s {lastNameIdx = n + 1})
    return . Name $ "x" ++ show n

instance Eval Comp where
  normaliseProgram = gets (\c -> c.normaliseProgram)
  setNormaliseProgram b = ST.modify (\s -> s {normaliseProgram = b})
  reduceUnfoldDefs = gets (\c -> c.reduceUnfoldDefs)
  setReduceUnfoldDefs b = ST.modify (\s -> s {reduceUnfoldDefs = b})

instance Has Comp (Seq Problem) where
  view = gets (\c -> c.problems)
  modify f = ST.modify (\s -> s {problems = f s.problems})

instance Has Comp SolveAttempts where
  view = gets (\c -> c.solveAttempts)
  modify :: (SolveAttempts -> SolveAttempts) -> Comp ()
  modify f = ST.modify (\s -> s {solveAttempts = f s.solveAttempts})

instance Unelab Comp

instance Logger Comp where
  msg m = liftIO $ putStrLn m

instance Has Comp Qty where
  view = gets (\c -> c.qty)
  modify q = ST.modify (\s -> s {qty = q s.qty})

instance Tc Comp where
  tcError = throwError . TcCompilerError

  addGoal g = ST.modify (\s -> s {goals = s.goals ++ [g]})

instance Parent Comp where
  child c = do
    s <- get
    a <- c
    put s
    return a

instance Acc Comp where
  accError = throwError . AccCompilerError

  catchAccErrorNoResume m = do
    x <- tryError m
    case x of
      Left (AccCompilerError e) -> return $ Left e
      Left e -> throwError e
      Right a -> return $ Right a

instance Elab Comp where
  elabError = throwError . ElabCompilerError
  shouldRunAccount = return True

instance Has Comp Ctx where
  view = gets (\c -> c.ctx)
  modify f = ST.modify (\s -> s {ctx = f s.ctx})

instance Has Comp InPat where
  view = gets (\c -> c.inPat)
  modify f = ST.modify (\s -> s {inPat = f s.inPat})

instance Has Comp Loc where
  view = gets (\c -> c.currentLoc)
  modify f = ST.modify (\s -> s {currentLoc = f s.currentLoc})

instance Try Comp where
  type E Comp = CompilerError
  try f = do
    c <- get
    x <- tryError f
    case x of
      Left e -> do
        put c
        return $ Left e
      Right a -> return $ Right a

  giveUp :: E Comp -> Comp a
  giveUp = throwError

instance HasProjectFiles Comp where
  getProjectFileContents f = do
    fs <- gets (\c -> c.files)
    return $ M.lookup f fs

instance Has Comp [JsStat] where
  view = gets (\c -> c.codegenStatements)
  modify f = ST.modify (\s -> s {codegenStatements = f s.codegenStatements})

instance Gen Comp where
  readBootFile = liftIO $ readFile bootPath

emptyCompiler :: Compiler
emptyCompiler =
  Compiler
    { files = M.empty,
      solvedMetas = emptySolvedMetas,
      ctx = emptyCtx,
      sig = emptySig,
      currentLoc = NoLoc,
      inPat = NotInPat,
      normaliseProgram = True,
      lastNameIdx = 0,
      reduceUnfoldDefs = False,
      goals = [],
      qty = Many,
      codegenStatements = [],
      problems = mempty,
      solveAttempts = SolveAttempts 10
    }

runComp :: Comp a -> Compiler -> IO ()
runComp c s = do
  let c' = void c `catchError` (\e -> pretty e >>= err)
  (_, _) <- runStateT (runExceptT c'.unComp) s
  return ()

showGoals :: Comp ()
showGoals = do
  gs <- gets (\s -> s.goals)
  unless (null gs) $ do
    msg "\n-- Goals --\n"
    mapM_ (\g -> prettyGoal g >>= msg) gs

-- | Common logic for compilation tasks
parseAnd :: Args -> (PProgram -> Comp ()) -> Comp ()
parseAnd args task = do
  ST.modify (\s -> s {solveAttempts = SolveAttempts args.flags.attempts})
  when args.flags.noNormalise $ setNormaliseProgram False
  parseAndCheckPrelude
  parsed <- parseFile (argsFile args)
  task parsed
  when args.flags.verbose $ msg "\nTask completed successfully"

-- | Run the compiler.
compile :: Args -> Comp ()
compile args = case args of
  Args (ParseFile file) flags -> do
    parsed <- parseFile file
    when flags.verbose $ msg $ "Parsing file " ++ file
    when flags.dump $ pretty parsed >>= msg
  Args (CheckFile _) _ -> do
    parseAnd args elabProgram `catchError` (\e -> showGoals >> throwError e)
    when args.flags.dump $ unelabSig >>= pretty >>= msg
    showGoals
  Args (RepresentFile _) _ ->
    parseAnd args $ \parsed -> do
      elabProgram parsed
      reprInfSig
      when args.flags.dump $ unelabSig >>= pretty >>= msg
  Args (GenerateCode file) flags ->
    parseAnd args $ \parsed -> do
      elabProgram parsed
      reprInfSig
      code <- generateProgram
      emitFile (file ++ ".js") (renderJsProg code)
      when flags.verbose $ msg "Generated code successfully"
      when flags.dump $ msg $ renderJsProg code

-- Other functions remain the same
parseAndCheckPrelude :: Comp ()
parseAndCheckPrelude = do
  parsed <- parseFile preludePath
  elabProgram parsed

parseFile :: String -> Comp PProgram
parseFile file = do
  contents <- liftIO $ readFile file
  ST.modify (\c -> c {files = M.insert file contents c.files})
  case parseProgram file contents of
    Left e -> throwError $ ParseCompilerError e
    Right p -> return p

emitFile :: String -> String -> Comp ()
emitFile file contents = do
  liftIO $ writeFile file contents
  msg $ "Wrote file " ++ file
