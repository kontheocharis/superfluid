module Parsing (parseProgram, parseTerm, ParseError (..)) where

import Common
  ( Arg (Arg),
    Clause (Clause),
    Filename,
    HasProjectFiles,
    Lit (CharLit, FinLit, NatLit, StringLit),
    Loc (Loc),
    Name (..),
    Param (..),
    PiMode (Explicit, Implicit),
    Pos (Pos),
    Tag,
    Tel,
    Times (Finite),
  )
import Data.Char (isDigit, isSpace)
import Data.List.NonEmpty (NonEmpty, singleton)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as SE
import Data.Set (Set)
import qualified Data.Set as S
import Data.String
import Data.Text (Text)
import Presyntax
  ( PCaseRep (..),
    PCtor (MkPCtor),
    PCtorRep (MkPCtorRep),
    PData (MkPData),
    PDataRep (MkPDataRep),
    PDef (..),
    PDefRep (MkPDefRep),
    PItem (..),
    PPat,
    PPrim (MkPPrim),
    PProgram (..),
    PTm (..),
    PTy,
    pApp,
    tagged,
  )
import Printing (Pretty (..))
import Text.Parsec
  ( Parsec,
    between,
    char,
    choice,
    eof,
    errorPos,
    getPosition,
    many,
    many1,
    noneOf,
    notFollowedBy,
    optionMaybe,
    optional,
    runParser,
    satisfy,
    skipMany,
    skipMany1,
    sourceColumn,
    sourceLine,
    sourceName,
    string,
    (<|>),
  )
import qualified Text.Parsec as PS
import Text.Parsec.Char (alphaNum, letter)
import Text.Parsec.Combinator (sepEndBy, sepEndBy1)
import Text.Parsec.Prim (try)
import Text.Parsec.Text ()

-- | Parser state, used for generating fresh variables.
data ParserState = ParserState {}

initialParserState :: ParserState
initialParserState = ParserState {}

data ParseError = ParseError Loc String

instance (Monad m, HasProjectFiles m) => Pretty m ParseError where
  pretty (ParseError l s) = do
    l' <- pretty l
    return $ l' ++ "\nParse error: " ++ s

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
commaSep1 p = NE.fromList <$> p `sepEndBy1` comma

comment :: Parser ()
comment = do
  _ <- try (string "--")
  skipMany (satisfy (/= '\n'))

-- | Parse vertical whitespace (i.e. a new line) or horizontal whitespace or comments.
anyWhite :: Parser ()
anyWhite = skipMany (skipMany1 (satisfy isSpace) <|> comment)

-- | Reserved identifiers.
reservedIdents :: [String]
reservedIdents =
  [ "data",
    "case",
    "repr",
    "as",
    "def",
    "let",
    "prim",
    "rec",
    "-inf",
    "inf",
    "unrepr",
    "impossible",
    "to"
  ]

anyIdentifier :: Parser String
anyIdentifier = try $ do
  f <- letter <|> char '_'
  rest <- many (char '_' <|> char '\'' <|> char '-' <|> alphaNum)
  anyWhite
  return $ f : rest

identifier :: Parser Name
identifier = try $ do
  name <- anyIdentifier
  if name `elem` reservedIdents
    then fail $ "Identifier " ++ name ++ " is reserved"
    else return $ Name name

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
  n <- sourceName <$> getPosition
  start <- getPos
  x <- p
  end <- getPos
  return $ f x (Loc n start end)

locatedTerm :: Parser PTm -> Parser PTm
locatedTerm p = do
  (t, l) <- located (,) p
  return $ PLocated l t

-- | Parse a term from a string.
parseTerm :: String -> Either ParseError PTm
parseTerm contents = case runParser (term <* eof) initialParserState "" (fromString contents) of
  Left err -> Left $ makeParseError "<interactive>" err
  Right p -> Right p

makeParseError :: Filename -> PS.ParseError -> ParseError
makeParseError file err = do
  let e = errorPos err
  let pos = Pos (sourceLine e) (sourceColumn e)
  ParseError (Loc file pos pos) (show err)

-- | Parse a program from its filename and string contents.
parseProgram :: String -> String -> Either ParseError PProgram
parseProgram filename contents = case runParser
  (program <* eof)
  initialParserState
  filename
  (fromString contents) of
  Left err -> Left $ makeParseError filename err
  Right p -> Right p

item :: Parser PItem
item = whiteWrap . located (flip PLocatedItem) $ do
  ts <- tags
  tagged ts
    <$> ( PData <$> dataItem
            <|> PDef <$> defItem
            <|> PDataRep <$> reprDataItem
            <|> PDefRep <$> reprDeclItem
            <|> PPrim <$> primItem
        )

-- | Parse a program.
program :: Parser PProgram
program = whiteWrap $ do
  ds <- many item
  return $ PProgram ds

-- | Wrap a parser in whitespace.
whiteWrap :: Parser a -> Parser a
whiteWrap p = do
  anyWhite
  x <- p
  anyWhite
  return x

reprDataItem :: Parser PDataRep
reprDataItem = do
  try (symbol "repr" >> symbol "data")
  src <- pat
  symbol "as"
  target <- term
  curlies $ do
    ctors <- commaSep (notFollowedBy (symbol "case") >> reprCtorItem)
    cse <- reprCaseItem
    optional comma
    return $ MkPDataRep src target ctors cse mempty

reprDeclItem :: Parser PDefRep
reprDeclItem = do
  try (symbol "repr" >> symbol "def")
  src <- pat
  reservedOp "as"
  target <- term
  return $ MkPDefRep src target mempty

reprCtorItem :: Parser PCtorRep
reprCtorItem = do
  src <- pat
  reservedOp "as"
  target <- term
  return $ MkPCtorRep src target mempty

reprCaseItem :: Parser PCaseRep
reprCaseItem = do
  symbol "case"
  subject <- singlePat
  tr <- toRet
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
  t <- term
  return $ MkPCaseRep subject tr ctors t mempty

-- | Parse a constructor item.
ctorItem :: Parser PCtor
ctorItem = do
  name <- identifier
  _ <- colon
  ty <- term
  return $ MkPCtor name ty mempty

-- | Parse a data item.
dataItem :: Parser PData
dataItem = do
  symbol "data"
  (name, te, ty) <- dataSig
  ctors <- curlies (commaSep ctorItem)
  return $
    MkPData
      name
      te
      (fromMaybe PU ty)
      ctors
      mempty

-- | Parse a primitive item
primItem :: Parser PPrim
primItem = do
  symbol "prim"
  (name, ty) <- defSig
  case ty of
    Nothing -> fail "Primitive items must have a type signature"
    Just ty' -> return $ MkPPrim name ty' mempty

tags :: Parser (Set Tag)
tags = do
  let names = M.fromList $ map (\t -> (show t, t)) [minBound .. maxBound :: Tag]
  S.fromList
    <$> many
      ( try (char '#') >> do
          i <- identifier
          case M.lookup i.unName names of
            Just n -> return n
            Nothing -> fail $ "Unknown tag " ++ i.unName
      )

-- | Parse a declaration.
defItem :: Parser PDef
defItem = do
  symbol "def"
  (name, ty) <- defSig
  t <- lets
  return $ MkPDef name (fromMaybe PWild ty) t mempty

-- | Parse the type signature of a declaration.
defSig :: Parser (Name, Maybe PTy)
defSig = do
  name <- identifier
  ty <- optionMaybe $ colon >> term
  return (name, ty)

dataSig :: Parser (Name, Tel PTy, Maybe PTy)
dataSig = do
  name <- identifier
  ns <- optionMaybe . try $ SE.fromList . map fst <$> tel
  ty <- optionMaybe $ colon >> term
  return (name, fromMaybe Empty ns, ty)

-- | Parse a term.
-- Some are grouped to prevent lots of backtracking.
term :: Parser PTm
term = choice [caseExpr, lets, piTOrSigmaT, lam, app]

-- | Parse a list
list :: Parser PTm
list = locatedTerm $ do
  try $ symbol "["
  end <- optionMaybe (symbol "]")
  case end of
    Just _ -> return $ PList [] Nothing
    Nothing -> els []
  where
    els xs = do
      consIndicator <- optionMaybe (symbol "..")
      case consIndicator of
        Just _ -> do
          xs' <- term
          optional comma
          symbol "]"
          return $ PList xs (Just xs')
        Nothing -> do
          end <- optionMaybe $ symbol "]"
          case end of
            Just _ -> return $ PList xs Nothing
            Nothing -> do
              x <- term
              endComma <- optionMaybe comma
              case endComma of
                Just _ -> els (xs ++ [x])
                Nothing -> do
                  symbol "]"
                  return $ PList (xs ++ [x]) Nothing

-- | Parse a single term.
--
-- This is a term which never requires parentheses to disambiguate.
singleTerm :: Parser PTm
singleTerm = choice [list, literal, varOrHoleOrU, repTerm, unrepTerm, pairOrParens]

literal :: Parser PTm
literal = locatedTerm $ do
  ( try (symbol "\'") >> do
      c <- parseChar
      _ <- symbol "\'"
      anyWhite
      return $ PLit (CharLit c)
    )
    <|> ( try (symbol "\"") >> do
            s <- many parseStringChar
            _ <- symbol "\""
            anyWhite
            return $ PLit (StringLit s)
        )
    <|> try
      ( do
          n <- many1 (satisfy isDigit)
          endingN <- optionMaybe (try (char 'n') >> optionMaybe singleTerm)
          anyWhite
          case endingN of
            Just i -> return $ PLit (FinLit (read n) (fromMaybe PWild i))
            Nothing -> return $ PLit (NatLit (read n))
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

-- | Parse a pattern.
pat :: Parser PPat
pat = term

-- | Parse a pattern variable.
singlePat :: Parser PPat
singlePat = singleTerm

-- | Parse a variable.
var :: Parser Name
var = identifier

-- | Parse named parameters like `(n : Nat)`.
tel :: Parser [(Param PTy, Loc)]
tel =
  ( concatMap NE.toList
      <$> many1
        ((try . parens) (typings Explicit) <|> (try . square) (typings Implicit))
  )
    <|> NE.toList <$> namelessTyping
  where
    namelessTyping :: Parser (NonEmpty (Param PTy, Loc))
    namelessTyping =
      located
        (\(n, t) l -> singleton (Param Explicit n t, l))
        ( do
            t <- app
            return (Name "_", t)
        )

    typings :: PiMode -> Parser (NonEmpty (Param PTy, Loc))
    typings m = do
      ts <- commaSep1
        . located (\ts l -> map (\(n, t) -> (Param m n t, l)) ts)
        . try
        $ do
          n <- many1 var
          _ <- colon
          ty <- term
          return $ map (,ty) n
      return . NE.fromList $ concat ts

-- | Parse a pi type or sigma type.
piTOrSigmaT :: Parser PTy
piTOrSigmaT = try $ do
  ns <- tel
  op <- (reservedOp "->" >> return PPi) <|> (reservedOp "*" >> return (const PSigma))
  ret <- term
  return $ foldr (\(t, l) acc -> PLocated l (op t.mode t.name t.ty acc)) ret ns

-- | Parse an application.
app :: Parser PTy
app = do
  t <- singleTerm
  ts <- many ((Arg Implicit <$> try (square term)) <|> (Arg Explicit <$> try singleTerm))
  return $ pApp t ts

-- | Parse a representation term
repTerm :: Parser PTm
repTerm = locatedTerm $ do
  try $ reserved "repr"
  PRepr (Finite 1) <$> singleTerm

-- | Parse an unrepresentation term
unrepTerm :: Parser PTm
unrepTerm = locatedTerm $ do
  try $ reserved "unrepr"
  PRepr (Finite (-1)) <$> singleTerm

-- | Parse a series of let terms.
lets :: Parser PTm
lets = curlies $ do
  bindings <- many . located (,) $ do
    reserved "let"
    v <- singlePat
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
      ( \((v, ty, t), loc) acc ->
          PLocated loc (PLet v (fromMaybe PWild ty) t acc)
      )
      ret
      bindings

toRet :: Parser (Maybe PTy)
toRet = optionMaybe $ try (reserved "to") >> singleTerm

-- | Parse a lambda.
lam :: Parser PTm
lam = do
  reservedOp "\\"
  v <-
    Left <$> try (reserved "case")
      <|> Right <$> many1 (((Implicit,) <$> try (square (located (,) var))) <|> ((Explicit,) <$> located (,) var))
  case v of
    Left () -> do
      clauses <- curlies (commaSep caseClause)
      r <- toRet
      return $ PLambdaCase r clauses
    Right v' -> do
      reservedOp "=>"
      t <- term
      n <- sourceName <$> getPosition
      end <- getPos
      return $ foldr (\(m, (x, l)) acc -> PLocated (l <> Loc n end end) (PLam m x acc)) t v'

-- | Parse a pair.
pairOrParens :: Parser PTm
pairOrParens = locatedTerm . parens $ do
  t <- sepEndBy term comma
  case t of
    [] -> return PUnit
    [t'] -> return t'
    ts -> return $ foldr1 PPair ts

-- | Parse a variable or hole. Holes are prefixed with a question mark.
varOrHoleOrU :: Parser PTm
varOrHoleOrU = locatedTerm $ do
  hole <- optionMaybe $ reservedOp "?"
  v <- var
  case hole of
    Just _ -> return $ PHole v
    Nothing -> case v of
      Name "Type" -> return PU
      Name "_" -> return PWild
      _ -> return $ PName v

caseExpr :: Parser PTm
caseExpr = locatedTerm $ do
  reserved "case"
  t <- term
  r <- toRet
  clauses <- curlies (commaSep caseClause)
  return $ PCase t r clauses

caseClause :: Parser (Clause PPat PTm)
caseClause = do
  p <- pat
  reservedOp "=>"
  t' <- (try (symbol "impossible") >> return Nothing) <|> Just <$> term
  return $ Clause p t'
