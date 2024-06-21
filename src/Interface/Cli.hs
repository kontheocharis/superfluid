module Interface.Cli (runCli) where

import Checking.Context (Tc, TcState)
import Checking.Normalisation (normaliseTermFully, normaliseProgram)
import Checking.Representation (representProgram)
import Checking.Typechecking (checkProgram, inferTerm)
import Checking.Utils (runTc)
import Control.Monad (when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (MonadState (..))
import Data.Char (isSpace)
import Data.String
import Data.Text.IO (hPutStrLn)
import Interface.Pretty
import Lang (Program)
import Options.Applicative (execParser, (<**>), (<|>))
import Options.Applicative.Builder (fullDesc, header, help, info, long, progDesc, short, strOption, switch)
import Options.Applicative.Common (Parser)
import Options.Applicative.Extra (helper)
import Parsing.Parser (parseProgram, parseTerm)
import System.Console.Haskeline (InputT, defaultSettings, getInputLine, outputStrLn, runInputT)
import System.Exit (exitFailure)
import System.IO (stderr)
import Codegen.Generate (Gen, runGen, generateProgram, JsProg, renderJsProg)
import Language.C (CTranslUnit, Pretty (pretty))
import Language.JavaScript.Parser (JSAST, renderToString, renderJS)
import Resources.Prelude (preludePath, preludeContents)

-- | What mode to run in.
data Mode
  = -- | Typecheck a file.
    CheckFile String
  | -- | Parse a file
    ParseFile String
  | -- | Represent a file
    RepresentFile String
  | -- | Run a REPL
    Repl
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
    <|> pure Repl

-- | Parse the command line arguments.
parseArgs :: Parser Args
parseArgs = Args <$> parseMode <*> parseFlags

-- | Run the main CLI.
runCli :: IO ()
runCli = do
  args <- execParser opts
  runInputT defaultSettings $ runCompiler args
  where
    opts =
      info
        (parseArgs <**> helper)
        ( fullDesc
            <> progDesc "Superfluid is a dependently typed programming language with customisable type representations"
            <> header "Superfluid"
        )

-- | Log a message.
msg :: String -> InputT IO ()
msg m = do
  liftIO $ putStrLn m
  return ()

-- | Log a message to stderr and exit with an error code.
err :: String -> InputT IO a
err m = liftIO $ do
  hPutStrLn stderr $ fromString m
  exitFailure

-- | Log a message.
replErr :: String -> InputT IO a
replErr m = do
  msg m
  runRepl

-- | Potentially normalise a program.
andPotentiallyNormalise :: Flags -> Program -> Program
andPotentiallyNormalise flags p = if flags.normalise then normaliseProgram p else p

-- | Run the compiler.
runCompiler :: Args -> InputT IO ()
runCompiler (Args (CheckFile file) flags) = do
  checked <- andPotentiallyNormalise flags <$> checkFile file
  when flags.verbose $ msg "\nTypechecked program successfully"
  when flags.dump $ msg $ printVal checked
runCompiler (Args (ParseFile file) flags) = do
  when flags.verbose $ msg $ "Parsing file " ++ file
  parsed <- parseFile file
  when flags.dump $ msg $ printVal parsed
runCompiler (Args (RepresentFile file) flags) = do
  represented <- andPotentiallyNormalise flags <$> representFile file
  when flags.verbose $ msg "\nTypechecked and represented program successfully"
  when flags.dump $ msg $ printVal represented
runCompiler (Args (GenerateCode file) flags) = do
  code <- generateCode file
  when flags.verbose $ msg "Generated code successfully"
  when flags.dump $ msg $ renderJsProg code
runCompiler (Args Repl _) = runRepl

-- | Parse a file.
parseFile :: String -> InputT IO Program
parseFile file = do
  (p, _, _) <- parseFile' file
  return p

-- | Parse a file and return the current TC state.
parseFile' :: String -> InputT IO (Program, Program, TcState)
parseFile' file = do
  (prelude, st) <- parseAndCheckPrelude
  contents <- liftIO $ readFile file
  program <- handleParse err (parseProgram file contents (Just prelude))
  return (program, prelude, st)

-- | Parse and check a file.
checkFile :: String -> InputT IO Program
checkFile file = do
  (parsed, _, st) <- parseFile' file
  (checked, _) <- handleTc err (put st >> checkProgram parsed)
  return checked

-- | Parse, check and represent a file.
representFile :: String -> InputT IO Program
representFile file = do
  (parsed, _, st) <- parseFile' file
  (checked, st') <- handleTc err (put st >> checkProgram parsed)
  (represented, _) <- handleTc err (put st' >> representProgram checked)
  return represented

-- | Parse, check and represent a file.
generateCode :: String -> InputT IO JsProg
generateCode file = do
  (parsed, prelude, st) <- parseFile' file
  (checked, st') <- handleTc err (put st >> checkProgram parsed)
  (represented, _) <- handleTc err (put st' >> normaliseProgram <$> representProgram (prelude <> checked))
  generated <- handleGen err (generateProgram represented)
  emitFile (file ++ ".js") (renderJsProg generated)
  return generated

-- | Emit a file.
emitFile :: String -> String -> InputT IO ()
emitFile file contents = do
  liftIO $ writeFile file contents
  msg $ "Wrote file " ++ file

-- | Run the REPL.
runRepl :: InputT IO a
runRepl = do
  i <- getInputLine "> "
  case i of
    Nothing -> return ()
    Just ('@' : 't' : ' ' : inp) -> do
      t <- handleParse replErr (parseTerm inp)
      ((ty, _), _) <- handleTc replErr (inferTerm t)
      outputStrLn $ printVal ty
    Just inp | all isSpace inp -> return ()
    Just inp -> do
      t <- handleParse replErr (parseTerm inp)
      _ <- handleTc replErr (inferTerm t)
      (t', _) <- handleTc replErr (return $ normaliseTermFully mempty t)
      outputStrLn $ printVal t'
  runRepl

-- | Parse and check the Prelude, returning the final TC state and the parsed program.
parseAndCheckPrelude :: InputT IO (Program, TcState)
parseAndCheckPrelude = do
  parsed <- handleParse err (parseProgram preludePath preludeContents Nothing)
  (checked, st) <- handleTc err (checkProgram parsed)
  return (checked, st)

-- | Handle a parsing result.
handleParse :: (String -> InputT IO a) -> Either String a -> InputT IO a
handleParse er res = do
  case res of
    Left e -> er $ "Failed to parse: " ++ e
    Right p -> return p

-- | Handle a checking result.
handleTc :: (String -> InputT IO (a, TcState)) -> Tc a -> InputT IO (a, TcState)
handleTc er a = do
  case runTc a of
    Left e -> do
      er $ "Typechecking error: " ++ show e
    Right (p, s) -> return (p, s)

-- | Handle a generation result.
handleGen :: (String -> InputT IO a) -> Gen a -> InputT IO a
handleGen er a = do
  case runGen a of
    Left e -> do
      er $ "Code generation error: " ++ show e
    Right p -> return p
