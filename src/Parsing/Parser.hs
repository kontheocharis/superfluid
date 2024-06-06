module Parsing.Parser (parseProgram, parseTerm) where

import Checking.Context (Signature (Signature))
import Data.Char (isSpace)
import Data.Maybe (fromMaybe)
import Data.String
import Data.Text (Text)
import Lang
  ( CtorItem (..),
    DataItem (..),
    DeclItem (..),
    GlobalName,
    Item (..),
    Loc (..),
    MapResult (..),
    Pat,
    PiMode (..),
    Pos (..),
    Program (..),
    ReprDataCaseItem (ReprDataCaseItem),
    ReprDataCtorItem (ReprDataCtorItem),
    ReprDataItem (ReprDataItem),
    ReprDeclItem (..),
    ReprItem (..),
    ReprSomeItem (..),
    Term (..),
    TermMappable (..),
    TermValue (..),
    Type,
    Var (..),
    genTerm,
    isValidPat,
    listToApp,
    mapTermM,
    termDataAt,
    termLoc,
  )
import Parsing.Resolution (resolveGlobalsRec)
import Text.Parsec
  ( Parsec,
    between,
    char,
    choice,
    eof,
    getPosition,
    getState,
    many,
    many1,
    modifyState,
    notFollowedBy,
    optionMaybe,
    optional,
    putState,
    runParser,
    satisfy,
    skipMany,
    skipMany1,
    sourceColumn,
    sourceLine,
    string,
    (<|>),
  )
import Text.Parsec.Char (alphaNum, letter)
import Text.Parsec.Combinator (sepEndBy1)
import Text.Parsec.Prim (try)
import Text.Parsec.Text ()
import Interface.Pretty (Print(printVal))

-- | Parser state, used for generating fresh variables.
data ParserState = ParserState
  { varCount :: Int,
    -- Keep track of the names of variables so we can resolve them when encountering them.
    names :: [(String, Var)]
  }

initialParserState :: ParserState
initialParserState =
  ParserState
    { varCount = 0,
      names = []
    }

-- | Get a new variable index and increment it.
newVarIndex :: Parser Int
newVarIndex = do
  s <- getState
  let i = s.varCount
  putState s {varCount = i + 1}
  return i

-- | Generate a new variable.
registerNewVar :: String -> Parser Var
registerNewVar n = do
  s <- getState
  let ns = s.names
  v <- Var n <$> newVarIndex
  modifyState $ \s' -> s' {names = (n, v) : ns}
  return v

-- | Get an already registered variable or generate a new one.
registerVar :: String -> Parser Var
registerVar n = do
  s <- getState
  let ns = s.names
  case lookup n ns of
    Just v -> return v
    Nothing -> do
      v <- Var n <$> newVarIndex
      modifyState $ \s' -> s' {names = (n, v) : ns}
      return v

-- | Parser type alias.
type Parser a = Parsec Text ParserState a

-- Some helper functions for the parser:

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

curlies :: Parser a -> Parser a
curlies = between (symbol "{") (symbol "}")

square :: Parser a -> Parser a
square = between (symbol "[") (symbol "]")

commaSep :: Parser a -> Parser [a]
commaSep p = p `sepEndBy1` comma

comment :: Parser ()
comment = do
  _ <- try (string "--")
  skipMany (satisfy (/= '\n'))

-- | Parse vertical whitespace (i.e. a new line) or horizontal whitespace or comments.
anyWhite :: Parser ()
anyWhite = skipMany (skipMany1 (satisfy isSpace) <|> comment)

-- | Reserved identifiers.
reservedIdents :: [String]
reservedIdents = ["data", "case", "repr", "as", "def", "let"]

anyIdentifier :: Parser String
anyIdentifier = try $ do
  first <- letter <|> char '_'
  rest <- many (alphaNum <|> char '_' <|> char '\'' <|> char '-')
  anyWhite
  return $ first : rest

identifier :: Parser String
identifier = try $ do
  name <- anyIdentifier
  if name `elem` reservedIdents
    then fail $ "Identifier " ++ name ++ " is reserved"
    else return name

symbol :: String -> Parser ()
symbol s = try $ do
  _ <- string s
  anyWhite
  return ()

reserved :: String -> Parser ()
reserved = symbol

reservedOp :: String -> Parser ()
reservedOp = symbol

comma :: Parser ()
comma = symbol ","

colon :: Parser ()
colon = try $ symbol ":" >> notFollowedBy (char '=')

-- | Get the current location in the source file.
getPos :: Parser Pos
getPos = do
  s <- getPosition
  return (Pos (sourceLine s) (sourceColumn s))

located :: Parser a -> Parser (a, Loc)
located p = do
  start <- getPos
  x <- p
  end <- getPos
  return (x, Loc start end)

locatedTerm :: Parser TermValue -> Parser Term
locatedTerm p = do
  (t, l) <- located p
  return $ Term t (termDataAt l)

-- | Parse a term from a string.
parseTerm :: String -> Either String Term
parseTerm contents = case runParser (term <* eof) initialParserState "" (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

-- | Parse a program from its filename and string contents.
parseProgram :: String -> String -> Either String Program
parseProgram filename contents = case runParser (program <* eof) initialParserState filename (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

-- | Parse a program.
program :: Parser Program
program = whiteWrap $ do
  ds <- many (Data <$> dataItem <|> Decl <$> declItem <|> Repr <$> reprItem)
  -- Resolve the globals after getting all the declarations.
  return $ mapTermMappable (resolveGlobalsRec (Signature ds)) (Program ds)

-- | Wrap a parser in whitespace.
whiteWrap :: Parser a -> Parser a
whiteWrap p = do
  anyWhite
  x <- p
  anyWhite
  return x

-- | Parse a data item.
reprItem :: Parser ReprItem
reprItem = whiteWrap $ do
  symbol "repr"
  name <- identifier
  ReprItem name <$> curlies reprItems -- Just a single clause for now

-- | Parse a series of repr items
reprItems :: Parser [ReprSomeItem]
reprItems = many1 $ choice [ReprData <$> reprDataItem, ReprDecl <$> reprDeclItem]

reprDataItem :: Parser ReprDataItem
reprDataItem = whiteWrap $ do
  symbol "data"
  src <- pat
  symbol "as"
  target <- term
  curlies $ do
    ctors <- commaSep (notFollowedBy (symbol "case") >> reprCtorItem)
    cse <- reprCaseItem
    optional comma
    return $ ReprDataItem src target ctors (Just cse)

reprDeclItem :: Parser ReprDeclItem
reprDeclItem = whiteWrap $ do
  symbol "def"
  name <- identifier
  reservedOp "as"
  ReprDeclItem name <$> term

reprCtorItem :: Parser ReprDataCtorItem
reprCtorItem = do
  src <- pat
  reservedOp "as"
  ReprDataCtorItem src <$> term

reprCaseItem :: Parser ReprDataCaseItem
reprCaseItem = do
  symbol "case"
  subject <- singlePat
  ctors <-
    curlies
      ( commaSep
          ( do
              name <- identifier
              reservedOp "=>"
              bind <- singlePat
              return (name, bind)
          )
      )
  symbol "as"
  ReprDataCaseItem (subject, ctors) <$> term

-- | Parse a constructor item.
ctorItem :: GlobalName -> Parser (Int -> CtorItem)
ctorItem d = do
  name <- identifier
  _ <- colon
  ty <- term
  return $ \idx -> CtorItem name ty idx d

-- | Parse a data item.
dataItem :: Parser DataItem
dataItem = whiteWrap $ do
  symbol "data"
  (name, ty) <- declSignature
  ctors <- curlies (commaSep (ctorItem name))
  return $
    DataItem
      name
      (fromMaybe (genTerm TyT) ty)
      (zipWith ($) ctors [0 ..])

-- | Parse a declaration.
declItem :: Parser DeclItem
declItem = whiteWrap $ do
  start <- getPos
  symbol "def"
  (name, ty) <- declSignature
  t <- lets
  DeclItem name (fromMaybe (genTerm Wild) ty) t . Loc start <$> getPos

-- | Parse the type signature of a declaration.
declSignature :: Parser (String, Maybe Type)
declSignature = do
  name <- identifier
  ty <- optionMaybe $ colon >> term
  return (name, ty)

-- | Parse a term.
-- Some are grouped to prevent lots of backtracking.
term :: Parser Term
term = do
  t <- choice [caseExpr, lets, piTOrSigmaT, lam, app]
  resolveTerm t

-- | Parse a single term.
--
-- This is a term which never requires parentheses to disambiguate.
singleTerm :: Parser Term
singleTerm = choice [varOrHole, pairOrParens]

-- | Parse a pattern given a parser for terms.
enterPat :: Parser Term -> Parser Term
enterPat p = do
  t <- p
  t' <- resolveTerm t
  if isValidPat t'
    then return t'
    else fail $ "Cannot use term " ++ printVal t ++ " as a pattern"

-- | Parse a pattern.
pat :: Parser Pat
pat = enterPat term

-- | Parse a pattern variable.
singlePat :: Parser Pat
singlePat = enterPat singleTerm

-- | Parse a variable.
var :: Parser Var
var = do
  name <- identifier
  registerVar name

-- | Parse a variable binding.
newVar :: Parser Var
newVar = do
  name <- identifier
  registerNewVar name

-- | Generate a fresh variable.
freshVar :: Parser Var
freshVar = do
  idx <- newVarIndex
  return $ Var ("n" ++ show idx) idx

-- | Parse a named parameter like `(n : Nat)`.
named :: Parser (PiMode, Var, Type)
named =
  (try . parens)
    ( do
        name <- newVar
        _ <- colon
        ty <- term
        return (Explicit, name, ty)
    )
    <|> (try . square)
      ( do
          name <- newVar
          _ <- colon
          ty <- term
          return (Implicit, name, ty)
      )
    <|> ( do
            name <- freshVar
            t <- app
            return (Explicit, name, t)
        )

-- | Parse a pi type or sigma type.
piTOrSigmaT :: Parser Type
piTOrSigmaT = try . locatedTerm $ do
  (m, name, ty1) <- named
  binderT <-
    (reservedOp "->" >> return (PiT m))
      <|> ( reservedOp "**" >> case m of
              Explicit -> return SigmaT
              Implicit -> fail "Cannot use implicit arguments in a sigma type"
          )
  binderT name ty1 <$> term

-- | Parse an application.
app :: Parser Term
app = do
  t <- singleTerm
  ts <- many (((Implicit,) <$> try (square singleTerm)) <|> ((Explicit,) <$> singleTerm))
  return $ listToApp (t, ts)

-- | Parse a series of let terms.
lets :: Parser Term
lets = curlies $ do
  bindings <- many . located $ do
    reserved "let"
    v <- newVar
    ty <- optionMaybe $ do
      colon
      term
    reservedOp "="
    t <- term
    reservedOp ";"
    return (v, ty, t)
  ret <- term
  return $
    foldr
      ( \((v, ty, t), loc) acc -> case ty of
          Just ty' -> Term (Let v ty' t acc) (termDataAt (loc <> termLoc acc))
          Nothing -> Term (Let v (genTerm Wild) t acc) (termDataAt (loc <> termLoc acc))
      )
      ret
      bindings

-- | Parse a lambda.
lam :: Parser Term
lam = do
  reservedOp "\\"
  v <- many1 (((Implicit,) <$> try (square (located newVar))) <|> ((Explicit,) <$> located newVar))
  reservedOp "=>"
  t <- term
  end <- getPos
  return $ foldr (\(m, (x, l)) acc -> Term (Lam m x acc) (termDataAt (l <> Loc end end))) t v

-- Lam v <$> term

-- | Parse a pair.
pairOrParens :: Parser Term
pairOrParens = locatedTerm . parens $ do
  t1 <- term
  t2 <- optionMaybe $ comma >> term
  case t2 of
    Just t2' -> return $ Pair t1 t2'
    Nothing -> return t1.value

-- | Parse a variable or hole. Holes are prefixed with a question mark.
varOrHole :: Parser Term
varOrHole = locatedTerm $ do
  hole <- optionMaybe $ reservedOp "?"
  v <- var
  case hole of
    Just _ -> return $ Hole v
    Nothing -> return $ V v

caseExpr :: Parser Term
caseExpr = locatedTerm $ do
  reserved "case"
  t <- term
  clauses <- curlies (commaSep caseClause)
  return $ Case t clauses

caseClause :: Parser (Pat, Term)
caseClause = do
  p <- pat
  reservedOp "=>"
  t' <- term
  return (p, t')

-- | Resolve the "primitive" data types and constructors in a term.
resolveTerm :: Term -> Parser Term
resolveTerm = mapTermM r
  where
    r :: Term -> Parser (MapResult Term)
    r (Term (V (Var "_" _)) d) = return . Replace $ Term Wild d
    r (Term (V (Var "Type" _)) d) = return $ Replace (Term TyT d)
    r _ = return Continue
