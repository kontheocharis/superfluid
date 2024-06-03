module Interface.Cli (runCli) where

import Checking.Context (Tc, TcState, runTc)
import Checking.Typechecking (checkProgram, inferTerm, normaliseTermFully, representProgram)
import Control.Monad (void, when)
import Control.Monad.IO.Class (liftIO)
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

-- | What mode to run in.
data Mode
  = -- | Typecheck a file.
    CheckFile String
  | -- | Run a REPL
    Repl
  deriving (Show)

-- | How to apply changes to a file
data ApplyChanges = InPlace | Print | NewFile
  deriving (Show)

-- | Command-line flags.
data Flags = Flags
  { -- | Whether to dump the parsed program.
    dumpParsed :: Bool,
    -- | Whether to be verbose.
    verbose :: Bool
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
    <$> switch (long "dump-parsed" <> help "Print the parsed program")
    <*> switch (long "verbose" <> short 'v' <> help "Be verbose")

-- | Parse the mode to run in.
parseMode :: Parser Mode
parseMode =
  (CheckFile <$> strOption (long "check" <> short 'c' <> help "File to check"))
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

-- | Run the compiler.
runCompiler :: Args -> InputT IO ()
runCompiler (Args (CheckFile file) flags) = void (parseAndCheckFile file flags)
runCompiler (Args Repl _) = runRepl

-- | Parse a file.
parseFile :: String -> Flags -> InputT IO Program
parseFile file flags = do
  when flags.verbose $ msg $ "Parsing file " ++ file
  contents <- liftIO $ readFile file
  parsed <- handleParse err (parseProgram file contents)
  when flags.dumpParsed $ msg $ "Parsed program:\n" ++ printVal parsed
  return parsed

-- | Parse and check a file.
parseAndCheckFile :: String -> Flags -> InputT IO Program
parseAndCheckFile file flags = do
  parsed <- parseFile file flags
  (checked, _) <- handleTc err (checkProgram parsed)
  when flags.verbose $ msg "\nTypechecked program successfully"
  when flags.dumpParsed $ msg $ "Checked program:\n" ++ printVal checked
  (represented, state) <- handleTc err (representProgram checked)
  when flags.dumpParsed $ msg $ "Reepresented program:\n" ++ printVal represented
  when flags.verbose $ msg $ "\nEnding state:\n" ++ show state
  return checked

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
      (t', _) <- handleTc replErr (normaliseTermFully t)
      outputStrLn $ printVal t'
  runRepl

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
    Left e -> er $ "Error: " ++ show e
    Right (p, s) -> return (p, s)
