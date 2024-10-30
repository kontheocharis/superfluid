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
    PiMode (..),
    Pos (Pos),
    Qty (..),
    Tag,
    Tel,
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
  ( MaybeQty (..),
    PCaseRep (..),
    PCtor (MkPCtor),
    PCtorRep (MkPCtorRep),
    PData (MkPData),
    PDataRep (MkPDataRep),
    PDef (..),
    PDefRep (MkPDefRep),
    PItem (..),
    PPat,
    PPats (..),
    PPrim (MkPPrim),
    PProgram (..),
    PTm (..),
    PTy,
    pApp,
    tagged,
    un,
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
import Text.Parsec.Combinator (endBy1, sepEndBy, sepEndBy1)
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
parens = between (reservedOp "(") (reservedOp ")")

curlies :: Parser a -> Parser a
curlies = between (reservedOp "{") (reservedOp "}")

square :: Parser a -> Parser a
square = between (reservedOp "[") (reservedOp "]")

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
    "if",
    "else",
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

reserved :: String -> Parser ()
reserved s = try $ do
  name <- anyIdentifier
  if name == s
    then return ()
    else fail $ "Expected symbol " ++ s ++ " but got " ++ name

reservedOp :: String -> Parser ()
reservedOp s = do
  _ <- string s
  anyWhite
  return ()

comma :: Parser ()
comma = reservedOp ","

colon :: Parser ()
colon = try $ reservedOp ":" >> notFollowedBy (char '=')

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
  try (reserved "repr" >> reserved "data")
  src <- pat
  reserved "as"
  target <- term
  curlies $ do
    ctors <- commaSep (notFollowedBy (reserved "case") >> reprCtorItem)
    cse <- reprCaseItem
    optional comma
    return $ MkPDataRep src target ctors cse mempty

reprDeclItem :: Parser PDefRep
reprDeclItem = do
  try (reserved "repr" >> reserved "def")
  src <- pat
  reserved "as"
  target <- term
  return $ MkPDefRep src target mempty

reprCtorItem :: Parser PCtorRep
reprCtorItem = do
  src <- pat
  reserved "as"
  target <- term
  return $ MkPCtorRep src target mempty

reprCaseItem :: Parser PCaseRep
reprCaseItem = do
  reserved "case"
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
  reserved "as"
  t <- term
  return $ MkPCaseRep subject tr ctors t mempty

-- | Parse a constructor item.
ctorItem :: Parser PCtor
ctorItem = do
  q <- qty
  name <- identifier
  _ <- colon
  ty <- term
  return $ MkPCtor name q ty mempty

-- | Parse a data item.
dataItem :: Parser PData
dataItem = do
  reserved "data"
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
  reserved "prim"
  q <- qty
  (name, ty) <- defSig
  case ty of
    Nothing -> fail "Primitive items must have a type signature"
    Just ty' -> return $ MkPPrim name q ty' mempty

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
  reserved "def"
  q <- qty
  (name, ty) <- defSig
  t <-
    try (curlies $ commaSep clause)
      <|> ( do
              t <- lets
              return [Clause (PPats []) (Just t)]
          )
  return $ MkPDef name q (fromMaybe PWild ty) t mempty

clause :: Parser (Clause PPats PTm)
clause = do
  ps <- many1 singlePat <* reservedOp "=>"
  t' <- (try (reserved "impossible") >> return Nothing) <|> Just <$> term
  return $ Clause (PPats ps) t'

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
term = choice [caseExpr, ifExpr, lets, piTOrSigmaT, lam, app]

-- | Parse a list
list :: Parser PTm
list = locatedTerm $ do
  try $ reservedOp "["
  end <- optionMaybe (reservedOp "]")
  case end of
    Just _ -> return $ PList [] Nothing
    Nothing -> els []
  where
    els xs = do
      consIndicator <- optionMaybe (reservedOp "..")
      case consIndicator of
        Just _ -> do
          xs' <- term
          optional comma
          reservedOp "]"
          return $ PList xs (Just xs')
        Nothing -> do
          end <- optionMaybe $ reservedOp "]"
          case end of
            Just _ -> return $ PList xs Nothing
            Nothing -> do
              x <- term
              endComma <- optionMaybe comma
              case endComma of
                Just _ -> els (xs ++ [x])
                Nothing -> do
                  reservedOp "]"
                  return $ PList (xs ++ [x]) Nothing

-- | Parse a single term.
--
-- This is a term which never requires parentheses to disambiguate.
singleTerm :: Parser PTm
singleTerm = choice [list, literal, varOrHoleOrU, repTerm, unrepTerm, pairOrParens]

literal :: Parser PTm
literal = locatedTerm $ do
  ( try (reservedOp "\'") >> do
      c <- parseChar
      _ <- reservedOp "\'"
      anyWhite
      return $ PLit (CharLit c)
    )
    <|> ( try (reservedOp "\"") >> do
            s <- many parseStringChar
            _ <- reservedOp "\""
            anyWhite
            return $ PLit (StringLit s)
        )
    <|> try
      ( do
          n <- many1 (satisfy isDigit)
          endingN <- optionMaybe (try (char 'n') >> optionMaybe singleTerm)
          anyWhite
          case endingN of
            Just i -> return $ PLit (FinLit (read n) i)
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

-- | Parse named parameters like `(0 n : Nat)`.
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
        (\(q, n, t) l -> singleton (Param Explicit q n t, l))
        ( do
            q <- qty
            t <- app
            return (fromMaybe Many q.un, Name "_", t)
        )

    typings :: PiMode -> Parser (NonEmpty (Param PTy, Loc))
    typings m = do
      ts <- commaSep1
        . located (\ts l -> map (\(q, n, t) -> (Param m q n t, l)) ts)
        . try
        $ do
          q <-
            fromMaybe
              ( case m of
                  Explicit -> Many
                  Implicit -> Zero
                  Instance -> Many
              )
              . (\u -> u.un)
              <$> qty
          n <- many1 var
          _ <- colon
          ty <- term
          return $ map (q,,ty) n
      return . NE.fromList $ concat ts

qty :: Parser MaybeQty
qty =
  MaybeQty
    <$> ( try (reservedOp "0" >> return (Just Zero))
            <|> try (reservedOp "1" >> return (Just One))
            <|> try (reservedOp "!" >> return (Just Many))
            <|> try (reservedOp "&" >> return (Just View))
            <|> return Nothing
        )

-- | Parse a pi type or sigma type.
piTOrSigmaT :: Parser PTy
piTOrSigmaT = try $ do
  ns <- tel
  ( reservedOp "->" >> do
      ret <- term
      return $ foldr (\(t, l) acc -> PLocated l (PPi t.mode (MaybeQty (Just t.qty)) t.name t.ty acc)) ret ns
    )
    <|> ( reservedOp "*" >> do
            q <- qty
            ret <- term
            -- Remove this terrible hack!
            return $ foldr (\(t, l) acc -> PLocated l (PSigma (MaybeQty (Just t.qty)) t.name t.ty q acc)) ret ns
        )

-- | Parse an application.
app :: Parser PTy
app = do
  t <- singleTerm
  ts <- many ((Arg Implicit Many <$> try (square term)) <|> (Arg Explicit Many <$> try singleTerm))
  return $ pApp t ts

-- | Parse a representation term
repTerm :: Parser PTm
repTerm = locatedTerm $ do
  try $ reserved "repr"
  PRepr <$> singleTerm

-- | Parse an unrepresentation term
unrepTerm :: Parser PTm
unrepTerm = locatedTerm $ do
  try $ reserved "unrepr"
  PUnrepr <$> singleTerm

-- | Parse a series of let terms.
lets :: Parser PTm
lets = curlies $ do
  bindings <- many . located (,) $ do
    reserved "let"
    q <- qty
    v <- singlePat
    ty <- optionMaybe $ do
      colon
      term
    reservedOp "="
    t <- term
    reservedOp ";"
    return (q, v, ty, t)
  ret <- term
  return $
    foldr
      ( \((q, v, ty, t), loc) acc ->
          PLocated loc (PLet q v (fromMaybe PWild ty) t acc)
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
      <|> Right <$> many1 (((Implicit,) <$> try (square (located (,) pat))) <|> ((Explicit,) <$> located (,) singlePat))
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

ifExpr :: Parser PTm
ifExpr = locatedTerm $ do
  ifs <-
    endBy1
      ( do
          try $ reserved "if"
          cond <- term
          t <- curlies term
          return (cond, t)
      )
      (try $ reserved "else")
  elseBranch <- curlies term
  return $ foldr (\(cond, t) acc -> PIf cond t acc) elseBranch ifs

caseClause :: Parser (Clause PPat PTm)
caseClause = do
  p <- pat
  reservedOp "=>"
  t' <- (try (reserved "impossible") >> return Nothing) <|> Just <$> term
  return $ Clause p t'
