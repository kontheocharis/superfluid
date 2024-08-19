module Parsing (parseProgram, parseTerm) where

import Common
  ( Arg (..),
    Clause (..),
    Lit (..),
    Loc (..),
    Name (Name),
    PiMode (..),
    Pos (..),
    Tag,
    Times (..),
    globalName,
    unName,
  )
import Data.Char (isDigit, isSpace)
import Data.List.NonEmpty (NonEmpty, singleton)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Data.String
import Data.Text (Text)
import Globals (KnownGlobal (..), knownCtor, knownData)
import Presyntax (PCaseRep (..), PCtor (MkPCtor), PCtorRep (MkPCtorRep), PData (MkPData), PDataRep (MkPDataRep), PDef (..), PDefRep (MkPDefRep), PItem (..), PPat, PPrim (MkPPrim), PProgram (..), PTm (..), PTy, pApp, tagged)
import Text.Parsec (Parsec, between, char, choice, eof, getPosition, many, many1, noneOf, notFollowedBy, optionMaybe, optional, runParser, satisfy, skipMany, skipMany1, sourceColumn, sourceLine, string, (<|>))
import Text.Parsec.Char (alphaNum, letter)
import Text.Parsec.Combinator (sepEndBy, sepEndBy1)
import Text.Parsec.Prim (try)
import Text.Parsec.Text ()

-- | Parser state, used for generating fresh variables.
data ParserState = ParserState {}

initialParserState :: ParserState
initialParserState = ParserState {}

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
reservedIdents = ["data", "case", "repr", "as", "def", "let", "prim", "rec", "unrepr", "impossible"]

anyIdentifier :: Parser String
anyIdentifier = try $ do
  f <- letter <|> char '_'
  rest <- many (alphaNum <|> char '_' <|> char '\'' <|> char '-')
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
  start <- getPos
  x <- p
  end <- getPos
  return $ f x (Loc start end)

locatedTerm :: Parser PTm -> Parser PTm
locatedTerm p = do
  (t, l) <- located (,) p
  return $ PLocated l t

-- | Parse a term from a string.
parseTerm :: String -> Either String PTm
parseTerm contents = case runParser (term <* eof) initialParserState "" (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

-- | Parse a program from its filename and string contents.
parseProgram :: String -> String -> Either String PProgram
parseProgram filename contents = case runParser
  (program <* eof)
  initialParserState
  filename
  (fromString contents) of
  Left err -> Left $ show err
  Right p -> Right p

item :: Parser PItem
item = do
  ts <- tags
  tagged ts
    <$> ( PData <$> dataItem
            <|> PDef <$> declItem
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
reprDataItem = whiteWrap $ do
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
reprDeclItem = whiteWrap $ do
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
  return $ MkPCaseRep subject ctors t mempty

-- | Parse a constructor item.
ctorItem :: Parser PCtor
ctorItem = do
  name <- identifier
  _ <- colon
  ty <- term
  return $ MkPCtor name ty mempty

-- | Parse a data item.
dataItem :: Parser PData
dataItem = whiteWrap $ do
  symbol "data"
  (name, ty) <- declSignature
  ctors <- curlies (commaSep ctorItem)
  return $
    MkPData
      name
      (fromMaybe PU ty)
      ctors
      mempty

-- | Parse a primitive item
primItem :: Parser PPrim
primItem = whiteWrap $ do
  symbol "prim"
  (name, ty) <- declSignature
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
declItem :: Parser PDef
declItem = whiteWrap $ do
  symbol "def"
  (name, ty) <- declSignature
  t <- lets
  return $ MkPDef name (fromMaybe PWild ty) t mempty

-- | Parse the type signature of a declaration.
declSignature :: Parser (Name, Maybe PTy)
declSignature = do
  name <- identifier
  ty <- optionMaybe $ colon >> term
  return (name, ty)

-- | Parse a term.
-- Some are grouped to prevent lots of backtracking.
term :: Parser PTm
term = choice [caseExpr, lets, piTOrSigmaT, lam, app]

-- | Parse a single term.
--
-- This is a term which never requires parentheses to disambiguate.
singleTerm :: Parser PTm
singleTerm = choice [literal, varOrHole, repTerm, unrepTerm, pairOrParens]

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

-- | Parse a named parameter like `(n : Nat)`.
named :: Parser (PiMode, NonEmpty (Loc, Name, PTy))
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
                    t <- app
                    return (Name "_", t)
                )
        )
  where
    typings :: Parser (NonEmpty (Loc, Name, PTy))
    typings = commaSep1 . located (\(n, t) l -> (l, n, t)) . try $ do
      _ <- colon
      ty <- term
      return (Name "_", ty)

-- | Parse a pi type or sigma type.
piTOrSigmaT :: Parser PTy
piTOrSigmaT = try $ do
  (m, ts) <- named
  op <-
    (reservedOp "->" >> return (PPi m))
      <|> ( reservedOp "*"
              >> return
                (\x a b -> pApp (PName (knownData KnownSigma).globalName) [Arg Explicit a, Arg Explicit (PLam Explicit x b)])
          )
  ret <- term
  return $ foldr (\(l, name, ty) acc -> PLocated l (op name ty acc)) ret ts

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
    v <- var
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

-- | Parse a lambda.
lam :: Parser PTm
lam = do
  reservedOp "\\"
  v <- many1 (((Implicit,) <$> try (square (located (,) var))) <|> ((Explicit,) <$> located (,) var))
  reservedOp "=>"
  t <- term
  end <- getPos
  return $
    foldr
      ( \(m, (x, l)) acc ->
          PLocated (l <> Loc end end) (PLam m x acc)
      )
      t
      v

-- | Parse a pair.
pairOrParens :: Parser PTm
pairOrParens = locatedTerm . parens $ do
  t1 <- term
  t2 <- optionMaybe $ comma >> term
  case t2 of
    Just t2' -> return $ pApp (PName (knownCtor KnownPair).globalName) [Arg Explicit t1, Arg Explicit t2']
    Nothing -> return t1

-- | Parse a variable or hole. Holes are prefixed with a question mark.
varOrHole :: Parser PTm
varOrHole = locatedTerm $ do
  hole <- optionMaybe $ reservedOp "?"
  v <- var
  case hole of
    Just _ -> return $ PHole v
    Nothing -> return $ PName v

caseExpr :: Parser PTm
caseExpr = locatedTerm $ do
  reserved "case"
  t <- term
  clauses <- curlies (commaSep caseClause)
  return $ PCase t clauses

caseClause :: Parser (Clause PPat PTm)
caseClause = do
  p <- pat
  reservedOp "=>"
  t' <- (try (symbol "impossible") >> return Nothing) <|> Just <$> term
  return $ Clause p t'