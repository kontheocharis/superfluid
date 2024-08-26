{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}

module Compiler (runCli) where

-- import Checking.Context (Tc, TcState)
-- import Checking.Normalisation (normaliseTermFully, normaliseProgram)
-- import Checking.Representation (representProgram)
-- import Checking.Typechecking (checkProgram, inferTerm)
-- import Checking.Utils (runTc)

-- import Interface.Pretty

-- import Codegen.Generate (Gen, runGen, generateProgram, JsProg, renderJsProg)

import Common (Has, HasNameSupply (..), HasProjectFiles (getProjectFileContents), Loc (..), Modify (..), Name (..), View (view))
import Control.Monad (void, when)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState (get, put), StateT (..))
import Control.Monad.State.Class (gets, modify)
import qualified Control.Monad.State.Class as ST
import Data.Map (Map)
import qualified Data.Map as M
import Data.String
import Data.Text.IO (hPutStrLn)
import Debug.Trace (trace, traceStack)
import Elaboration (Ctx, Elab (..), ElabError, InPat (NotInPat), checkProgram, emptyCtx)
import Evaluation (Eval (..), unelabSig)
import Globals (Sig, emptySig)
import Meta (HasMetas (..), SolvedMetas, emptySolvedMetas)
import Options.Applicative (execParser, (<**>), (<|>))
import Options.Applicative.Builder (fullDesc, header, help, info, long, progDesc, short, strOption, switch)
import Options.Applicative.Common (Parser)
import Options.Applicative.Extra (helper)
import Parsing (parseProgram)
import Persistence (preludePath)
import Presyntax (PProgram)
import Printing (Pretty (..))
import System.Console.Haskeline (InputT, defaultSettings, runInputT)
import System.Exit (exitFailure)
import System.IO (stderr)
import Unification (Unify)

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
    normalise :: Bool
  }
  deriving (Show)

-- | Command-line arguments.
data Args = Args
  { argsMode :: Mode,
    argsFlags :: Flags
  }
  deriving (Show)

-- | Parse the command-line flags.
parseFlags :: Parser Flags
parseFlags =
  Flags
    <$> switch (long "dump" <> short 'd' <> help "Print the parsed program")
    <*> switch (long "verbose" <> short 'v' <> help "Be verbose")
    <*> switch (long "normalise" <> short 'n' <> help "Normalise the program")

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

-- | Log a message.
msg :: String -> Comp ()
msg m = do
  liftIO $ putStrLn m
  return ()

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
    reduceUnderBinders :: Bool,
    lastNameIdx :: Int,
    reduceUnfoldDefs :: Bool
  }

data CompilerError = ElabCompilerError ElabError | ParseCompilerError String

instance Pretty Comp CompilerError where
  pretty (ElabCompilerError e) = pretty e
  pretty (ParseCompilerError e) = return e

newtype Comp a = Comp {unComp :: ExceptT CompilerError (StateT Compiler IO) a}
  deriving (Functor, Applicative, Monad, MonadState Compiler, MonadError CompilerError, MonadIO)

instance View Comp SolvedMetas where
  view = gets (\c -> c.solvedMetas)

instance Modify Comp SolvedMetas where
  modify f = ST.modify (\s -> s {solvedMetas = f s.solvedMetas})

instance Has Comp SolvedMetas

instance View Comp Sig where
  view = gets (\c -> c.sig)

instance Modify Comp Sig where
  modify f = ST.modify (\s -> s {sig = f s.sig})

instance Has Comp Sig

instance HasNameSupply Comp where
  uniqueName = do
    n <- gets (\c -> c.lastNameIdx)
    ST.modify (\s -> s {lastNameIdx = n + 1})
    return . Name $ "x" ++ show n

instance Eval Comp where
  reduceUnderBinders = gets (\c -> c.reduceUnderBinders)
  setReduceUnderBinders b = ST.modify (\s -> s {reduceUnderBinders = b})
  reduceUnfoldDefs = gets (\c -> c.reduceUnfoldDefs)
  setReduceUnfoldDefs b = ST.modify (\s -> s {reduceUnfoldDefs = b})

instance Unify Comp

instance Elab Comp where
  elabError = throwError . ElabCompilerError
  showMessage = msg

instance View Comp Ctx where
  view = gets (\c -> c.ctx)

instance Modify Comp Ctx where
  modify f = ST.modify (\s -> s {ctx = f s.ctx})

instance Has Comp Ctx

instance View Comp InPat where
  view = gets (\c -> c.inPat)

instance Modify Comp InPat where
  modify f = ST.modify (\s -> s {inPat = f s.inPat})

instance Has Comp InPat

instance View Comp Loc where
  view = gets (\c -> c.currentLoc)

instance Modify Comp Loc where
  modify f = ST.modify (\s -> s {currentLoc = f s.currentLoc})

instance Has Comp Loc

instance HasProjectFiles Comp where
  getProjectFileContents f = do
    fs <- gets (\c -> c.files)
    return $ M.lookup f fs

emptyCompiler :: Compiler
emptyCompiler =
  Compiler
    { files = M.empty,
      solvedMetas = emptySolvedMetas,
      ctx = emptyCtx,
      sig = emptySig,
      currentLoc = NoLoc,
      inPat = NotInPat,
      reduceUnderBinders = False,
      lastNameIdx = 0,
      reduceUnfoldDefs = False
    }

runComp :: Comp a -> Compiler -> IO ()
runComp c s = do
  let c' = do
        void c
          `catchError` ( \e -> do
                           e' <- pretty e
                           err e'
                       )
  (_, _) <- runStateT (runExceptT c'.unComp) s
  return ()

-- | Run the compiler.
compile :: Args -> Comp ()
compile args = do
  case args of
    Args (CheckFile file) flags -> do
      parseAndCheckPrelude
      parsed <- parseFile file
      checkProgram parsed
      when flags.verbose $ msg "\nTypechecked program successfully"
      prog <- unelabSig >>= pretty
      when flags.dump $ msg prog
    Args (ParseFile file) flags -> do
      parsed <- parseFile file
      when flags.verbose $ msg $ "Parsing file " ++ file
      printed <- pretty parsed
      when flags.dump . msg $ printed
    Args (RepresentFile file) flags -> error "unimplemented"
    -- represented <- andPotentiallyNormalise flags <$> representFile file
    -- when flags.verbose $ msg "\nTypechecked and represented program successfully"
    -- when flags.dump $ msg $ printVal represented
    Args (GenerateCode file) flags -> error "unimplemented"

-- code <- generateCode file
-- when flags.verbose $ msg "Generated code successfully"

-- when flags.dump $ msg $ renderJsProg code

parseAndCheckPrelude :: Comp ()
parseAndCheckPrelude = do
  parsed <- parseFile preludePath
  checkProgram parsed

-- | Parse a file with the given name and add it to the program
parseFile :: String -> Comp PProgram
parseFile file = do
  contents <- liftIO $ readFile file
  ST.modify (\c -> c {files = M.insert file contents c.files})
  case parseProgram file contents of
    Left e -> throwError $ ParseCompilerError e
    Right p -> return p

-- -- | Parse, check and represent a file.
-- representFile :: String -> InputT IO Program
-- representFile file = do
--   (parsed, _, st) <- parseFile' file
--   (checked, st') <- handleTc err (put st >> checkProgram parsed)
--   (represented, _) <- handleTc err (put st' >> representProgram checked)
--   return represented

-- -- | Parse, check and represent a file.
-- -- generateCode :: String -> InputT IO JsProg
-- -- generateCode file = do
-- --   (parsed, prelude, st) <- parseFile' file
-- --   (checked, st') <- handleTc err (put st >> checkProgram parsed)
-- --   (represented, _) <- handleTc err (put st' >> normaliseProgram <$> representProgram (prelude <> checked))
-- --   generated <- handleGen err (generateProgram represented)
-- --   emitFile (file ++ ".js") (renderJsProg generated)
-- --   return generated

-- -- | Emit a file.
-- emitFile :: String -> String -> InputT IO ()
-- emitFile file contents = do
--   liftIO $ writeFile file contents
--   msg $ "Wrote file " ++ file

-- -- | Handle a parsing result.
-- handleParse :: (String -> Comp a) -> Either String a -> Comp a
-- handleParse er res = do
--   case res of
--     Left e -> er $ "Failed to parse: " ++ e
--     Right p -> return p

-- -- | Handle a checking result.
-- handleTc :: (String -> InputT IO (a, Ctx)) -> Comp a -> InputT IO (a, Ctx)
-- handleTc er a = do
--   case runTc a of
--     Left e -> do
--       er $ "Typechecking error: " ++ show e
--     Right (p, s) -> return (p, s)

-- -- | Handle a generation result.
-- -- handleGen :: (String -> InputT IO a) -> Gen a -> InputT IO a
-- -- handleGen er a = do
-- --   case runGen a of
-- --     Left e -> do
-- --       er $ "Code generation error: " ++ show e
-- --     Right p -> return p
