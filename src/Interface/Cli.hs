module Interface.Cli (runCli) where

import Checking.Context (Tc, TcState)
import Checking.Typechecking (checkProgram, runTc, inferTerm, normaliseTermFully, representProgram, fillAllMetasAndNormalise)
import Control.Monad (void, when)
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
  deriving (Show)

-- | How to apply changes to a file
data ApplyChanges = InPlace | Print | NewFile
  deriving (Show)

-- | Command-line flags.
data Flags = Flags
  { -- | Whether to dump the program.
    dump :: Bool,
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
    <$> switch (long "dump" <> short 'd' <> help "Print the parsed program")
    <*> switch (long "verbose" <> short 'v' <> help "Be verbose")

-- | Parse the mode to run in.
parseMode :: Parser Mode
parseMode =
  (CheckFile <$> strOption (long "check" <> short 'c' <> help "File to check"))
    <|> (ParseFile <$> strOption (long "parse" <> short 'p' <> help "File to parse"))
    <|> (RepresentFile <$> strOption (long "represent" <> short 'r' <> help "File to represent"))
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
runCompiler (Args (CheckFile file) flags) = do
  checked <- checkFile file
  when flags.verbose $ msg "\nTypechecked program successfully"
  when flags.dump $ msg $ printVal checked
runCompiler (Args (ParseFile file) flags) = do
  when flags.verbose $ msg $ "Parsing file " ++ file
  parsed <- parseFile file
  when flags.dump $ msg $ printVal parsed
runCompiler (Args (RepresentFile file) flags) = do
  represented <- representFile file
  when flags.verbose $ msg "\nTypechecked and represented program successfully"
  when flags.dump $ msg $ printVal represented
runCompiler (Args Repl _) = runRepl

-- | Parse a file.
parseFile :: String -> InputT IO Program
parseFile file = do
  contents <- liftIO $ readFile file
  handleParse err (parseProgram file contents)

-- | Parse and check a file.
checkFile :: String -> InputT IO Program
checkFile file = do
  parsed <- parseFile file
  (checked, _) <- handleTc err (checkProgram parsed)
  return checked

-- | Parse, check and represent a file.
representFile :: String -> InputT IO Program
representFile file = do
  parsed <- parseFile file
  (checked, s) <- handleTc err (checkProgram parsed)
  (represented, _) <- handleTc err (put s >> representProgram checked)
  return represented

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
      (t', _) <- handleTc replErr (return $ normaliseTermFully t)
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
    Left e -> do
      er $ "Error: " ++ show e
    Right (p, s) -> return (p, s)
