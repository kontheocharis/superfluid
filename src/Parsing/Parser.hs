module Parsing.Parser (parseProgram, parseTerm) where

import Checking.Context (Signature (Signature))
import Control.Monad (foldM)
import Control.Monad.Identity (Identity)
import Control.Monad.RWS (modify)
import Data.Char (isDigit, isSpace, readLitChar)
import Data.List.NonEmpty (NonEmpty ((:|)), fromList, singleton)
import Data.Maybe (fromMaybe, isJust)
import Data.String
import Data.Text (Text)
import Debug.Trace (trace, traceShow)
import Interface.Pretty (Print (printVal))
import Lang
  ( CtorItem (..),
    DataItem (..),
    DeclItem (..),
    GlobalName,
    HasLoc (getLoc),
    Item (..),
    Lit (..),
    Loc (..),
    MapResult (..),
    Pat,
    PiMode (..),
    PrimItem (PrimItem),
    Program (..),
    ReprDataCaseItem (ReprDataCaseItem),
    ReprDataCtorItem (ReprDataCtorItem),
    ReprDataItem (ReprDataItem),
    ReprDeclItem (..),
    Term (..),
    TermMappable (..),
    TermValue (..),
    Type,
    Var (..),
    genTerm,
    isValidPat,
    listToApp,
    locatedAt,
    mapTermM,
    termDataAt,
    termLoc,
  )
import Parsing.Resolution (resolveGlobalsRec)
import Text.Parsec (Parsec, between, char, choice, eof, getPosition, getState, many, many1, modifyState, noneOf, notFollowedBy, optionMaybe, optional, putState, runParser, satisfy, skipMany, skipMany1, sourceColumn, sourceLine, string, (<|>))
import Text.Parsec.Char (alphaNum, letter)
import Text.Parsec.Combinator (sepEndBy, sepEndBy1)
import Text.Parsec.Prim (try)
import Text.Parsec.Text ()
import Common (Pos (..), PiMode (..))

-- | Parser state, used for generating fresh variables.
data ParserState = ParserState
  { varCount :: Int,
    -- Keep track of the names of variables so we can resolve them when encountering them.
    names :: [(String, Var)],
    -- Whether we are inside a pattern.
    inPat :: Bool
  }

initialParserState :: ParserState
initialParserState =
  ParserState
    { varCount = 0,
      names = [],
      inPat = False
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
commaSep p = p `sepEndBy` comma

commaSep1 :: Parser a -> Parser (NonEmpty a)
commaSep1 p = fromList <$> p `sepEndBy1` comma

comment :: Parser ()
comment = do
  _ <- try (string "--")
  skipMany (satisfy (/= '\n'))

-- | Parse vertical whitespace (i.e. a new line) or horizontal whitespace or comments.
anyWhite :: Parser ()
anyWhite = skipMany (skipMany1 (satisfy isSpace) <|> comment)

-- | Reserved identifiers.
reservedIdents :: [String]
reservedIdents = ["data", "case", "repr", "as", "def", "let", "prim", "rec", "unrepr"]

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

located :: (a -> Loc -> b) -> Parser a -> Parser b
located f p = do
  start <- getPos
  x <- p
  end <- getPos
  return $ f x (Loc start end)

locatedTerm :: Parser TermValue -> Parser Term
locatedTerm p = do
  (t, l) <- located (,) p
  return $ Term t (termDataAt l)

-- | Parse a term from a string.
parseTerm :: String -> Either String Term
parseTerm contents = case runParser (term <* eof) initialParserState "" (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

-- | Parse a program from its filename and string contents.
parseProgram :: String -> String -> Maybe Program -> Either String Program
parseProgram filename contents prelude = case runParser
  (program prelude <* eof)
  initialParserState
  filename
  (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

-- | Parse a program.
program :: Maybe Program -> Parser Program
program prelude = whiteWrap $ do
  ds <-
    many
      ( Data <$> dataItem
          <|> Decl <$> declItem
          <|> ReprData <$> reprDataItem
          <|> ReprDecl <$> reprDeclItem
          <|> Prim <$> primItem
      )
  let ds' =
        case prelude of
          Just (Program ds'') -> ds''
          Nothing -> []
          ++ ds
  -- Resolve the globals after getting all the declarations.
  return $ mapTermMappable (resolveGlobalsRec (Signature ds')) (Program ds)

-- | Wrap a parser in whitespace.
whiteWrap :: Parser a -> Parser a
whiteWrap p = do
  anyWhite
  x <- p
  anyWhite
  return x

reprDataItem :: Parser ReprDataItem
reprDataItem = whiteWrap $ do
  try (symbol "repr" >> symbol "data")
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
  try (symbol "repr" >> symbol "def")
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
  elim <- freshVar
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
  ReprDataCaseItem (subject, elim, ctors) <$> term

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

-- | Parse a primitive item
primItem :: Parser PrimItem
primItem = whiteWrap $ do
  symbol "prim"
  (name, ty) <- declSignature
  case ty of
    Nothing -> fail "Primitive items must have a type signature"
    Just ty' -> return $ PrimItem name ty'

-- | Parse a declaration.
declItem :: Parser DeclItem
declItem = whiteWrap $ do
  start <- getPos
  unf <- optionMaybe $ symbol "#unfold"
  symbol "def"
  r <- optionMaybe $ symbol "rec"
  (name, ty) <- declSignature
  t <- lets
  end <- getPos
  return $ DeclItem name (fromMaybe (genTerm Wild) ty) t (Loc start end) (isJust r) (isJust unf)

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
singleTerm = choice [literal, varOrHole, repTerm, unrepTerm, pairOrParens]

literal :: Parser Term
literal = locatedTerm $ do
  ( try (symbol "\'") >> do
      c <- parseChar
      _ <- symbol "\'"
      anyWhite
      return $ Lit (CharLit c)
    )
    <|> ( try (symbol "\"") >> do
            s <- many parseStringChar
            _ <- symbol "\""
            anyWhite
            return $ Lit (StringLit s)
        )
    <|> try
      ( do
          n <- many1 (satisfy isDigit)
          endingN <- optionMaybe (try (char 'n') >> optionMaybe singleTerm)
          anyWhite
          case endingN of
            Just i -> return $ Lit (FinLit (read n) (fromMaybe (genTerm Wild) i))
            Nothing -> return $ Lit (NatLit (read n))
      )
  where
    parseStringChar =
      (try (string "\\\\") >> return '\\')
        <|> (try (string "\\\"") >> return '\"')
        <|> (noneOf "\"" >>= \x -> return x)

    parseChar =
      try (string "\\\\" >> return '\\')
        <|> try (string "\\'" >> return '\'')
        <|> (noneOf "'" >>= \x -> return x)

-- | Parse a pattern given a parser for terms.
enterPat :: Parser Term -> Parser Term
enterPat p = do
  modifyState (\s' -> s' {inPat = True})
  t <- p
  modifyState (\s' -> s' {inPat = False})
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
  inP <- getState >>= \s -> return s.inPat
  if inP
    then registerNewVar name
    else registerVar name

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
named :: Parser (PiMode, NonEmpty (Loc, Var, Type))
named =
  (try . parens)
    ( do
        contents <- typings
        return (Explicit, contents)
    )
    <|> (try . square)
      ( do
          contents <- typings
          return (Implicit, contents)
      )
    <|> ( do
            (Explicit,)
              <$> located
                (\(n, t) l -> singleton (l, n, t))
                ( do
                    name <- freshVar
                    t <- app
                    return (name, t)
                )
        )
  where
    typings :: Parser (NonEmpty (Loc, Var, Type))
    typings = commaSep1 . located (\(n, t) l -> (l, n, t)) . try $ do
      name <- newVar
      _ <- colon
      ty <- term
      return (name, ty)

-- | Parse a pi type or sigma type.
piTOrSigmaT :: Parser Type
piTOrSigmaT = try $ do
  (m, ts) <- named
  op <-
    (reservedOp "->" >> return (PiT m))
      <|> (reservedOp "*" >> return SigmaT)
  ret <- term
  return $ foldr (\(l', name, ty) acc -> locatedAt l' (op name ty acc)) ret ts

-- | Parse an application.
app :: Parser Term
app = do
  t <- singleTerm
  ts <- many (((Implicit,) <$> try (square term)) <|> ((Explicit,) <$> try singleTerm))
  return $ listToApp (t, ts)

-- | Parse a representation term
repTerm :: Parser Term
repTerm = locatedTerm $ do
  try $ reserved "repr"
  Rep <$> singleTerm

-- | Parse an unrepresentation term
unrepTerm :: Parser Term
unrepTerm = locatedTerm $ do
  try $ reserved "unrepr"
  name <- identifier
  Unrep name <$> singleTerm

-- | Parse a series of let terms.
lets :: Parser Term
lets = curlies $ do
  bindings <- many . located (,) $ do
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
  v <- many1 (((Implicit,) <$> try (square (located (,) newVar))) <|> ((Explicit,) <$> located (,) newVar))
  reservedOp "=>"
  t <- term
  end <- getPos
  return $ foldr (\(m, (x, l)) acc -> Term (Lam m x acc) (termDataAt (l <> Loc end end))) t v

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
  return $ Case Nothing t clauses

caseClause :: Parser (Pat, Maybe Term)
caseClause = do
  p <- pat
  reservedOp "=>"
  t' <- (try (symbol "!") >> return Nothing) <|> Just <$> term
  return (p, t')

-- | Resolve the "primitive" data types and constructors in a term.
resolveTerm :: Term -> Parser Term
resolveTerm = mapTermM r
  where
    r :: Term -> Parser (MapResult Term)
    r (Term (V (Var "_" _)) d) = return . Replace $ Term Wild d
    r (Term (V (Var "Type" _)) d) = return $ Replace (Term TyT d)
    r _ = return Continue
