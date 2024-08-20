module Common
  ( Name (..),
    PiMode (..),
    Clause (..),
    pattern Possible,
    pattern Impossible,
    Lit (..),
    Times (..),
    inc,
    inv,
    dec,
    Loc (..),
    Pos (..),
    startPos,
    endPos,
    globName,
    Idx (..),
    Lvl (..),
    WithNames (..),
    nextLvl,
    nextLvls,
    lvlToIdx,
    Arg (..),
    Spine,
    mapSpine,
    mapSpineM,
    MetaVar (..),
    Glob (..),
    Tag (..),
    CtorGlobal (..),
    DataGlobal (..),
    PrimGlobal (..),
    DefGlobal (..),
    HasNameSupply (..),
    HasProjectFiles (..),
  )
where

import Criterion.Main.Options (MatchType (Glob))
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Generics (Data, Typeable)
import Data.Sequence (Seq)
import Numeric.Natural (Natural)
import Printing (Pretty (..))
import Data.Set (Set)
import Data.List (intercalate)
import Data.Foldable (toList)

-- | Whether a pi type is implicit or explicit.
data PiMode
  = Implicit
  | Explicit
  | Instance
  deriving (Eq)

instance Show PiMode where
  show Implicit = "implicit"
  show Explicit = "explicit"
  show Instance = "instance"

-- instance

-- | An identifier
newtype Name = Name {unName :: String} deriving (Eq, Show, Ord)

-- | A value with a list of names
data WithNames a = WithNames {names :: [Name], value :: a}

-- | A pattern clause, generic over the syntax types
data Clause p t
  = Clause {pat :: p, branch :: Maybe t}
  deriving (Eq, Show, Functor, Foldable, Traversable)

pattern Possible :: p -> t -> Clause p t
pattern Possible p t = Clause p (Just t)

pattern Impossible :: p -> Clause p t
pattern Impossible p = Clause p Nothing

{-# COMPLETE Possible, Impossible #-}

instance Bifunctor Clause where
  bimap f g (Possible p t) = Possible (f p) (g t)
  bimap f _ (Impossible p) = Impossible (f p)

instance Bifoldable Clause where
  bifoldMap f g (Possible p t) = f p <> g t
  bifoldMap f _ (Impossible p) = f p

instance Bitraversable Clause where
  bitraverse f g (Possible p t) = Possible <$> f p <*> g t
  bitraverse f _ (Impossible p) = Impossible <$> f p

-- | A literal
data Lit t
  = StringLit String
  | CharLit Char
  | NatLit Natural
  | FinLit Natural t
  deriving (Eq, Data, Typeable, Show, Functor, Traversable, Foldable)

-- | An amount of times to do something, which might be infinite.
data Times = Finite Int | NegInf | PosInf deriving (Eq, Show)

inc :: Times -> Times
inc (Finite n) = Finite (n + 1)
inc NegInf = NegInf
inc PosInf = PosInf

dec :: Times -> Times
dec (Finite n) = Finite (n - 1)
dec NegInf = NegInf
dec PosInf = PosInf

inv :: Times -> Times
inv (Finite n) = Finite (-n)
inv NegInf = PosInf
inv PosInf = NegInf

instance Semigroup Times where
  Finite n <> Finite m = Finite (n + m)
  NegInf <> PosInf = Finite 0
  PosInf <> NegInf = Finite 0
  PosInf <> _ = PosInf
  _ <> PosInf = PosInf
  NegInf <> _ = NegInf
  _ <> NegInf = NegInf

instance Monoid Times where
  mempty = Finite 0

instance Bounded Times where
  minBound = NegInf
  maxBound = PosInf

instance Ord Times where
  compare (Finite n) (Finite m) = compare n m
  compare NegInf NegInf = EQ
  compare PosInf PosInf = EQ
  compare NegInf _ = LT
  compare _ NegInf = GT
  compare PosInf _ = GT
  compare _ PosInf = LT

-- | An optional location in the source code, represented by a start (inclusive) and
-- end (exclusive) position.
data Loc = NoLoc | Loc String Pos Pos deriving (Eq, Show)

instance Semigroup Loc where
  NoLoc <> NoLoc = NoLoc
  NoLoc <> Loc f s e = Loc f s e
  Loc f s e <> NoLoc = Loc f s e
  Loc f s1 e1 <> Loc f' s2 e2 =
    if f == f'
      then Loc f (min s1 s2) (max e1 e2)
      else error "Cannot merge locations from different files"

instance Ord Loc where
  NoLoc <= _ = True
  _ <= NoLoc = False
  Loc f s1 e1 <= Loc f' s2 e2 = if f == f' then s1 <= s2 && e1 <= e2 else error "Cannot compare locations from different files"

-- | A position in the source code, represented by a line and column number.
data Pos = Pos {line :: Int, col :: Int} deriving (Eq, Show)

-- | An ordering for positions, that gets the minimum position.
instance Ord Pos where
  Pos l1 c1 <= Pos l2 c2 = l1 < l2 || (l1 == l2 && c1 <= c2)

-- | Get the starting position of a location.
startPos :: Loc -> Maybe Pos
startPos NoLoc = Nothing
startPos (Loc _ start _) = Just start

-- | Get the ending position of a location.
endPos :: Loc -> Maybe Pos
endPos NoLoc = Nothing
endPos (Loc _ _ end) = Just end

-- | Get the project file name of a location.
locProjectFileName :: Loc -> Maybe String
locProjectFileName NoLoc = Nothing
locProjectFileName (Loc f _ _) = Just f

-- De Brujin indices and levels

newtype Idx = Idx {unIdx :: Int} deriving (Eq, Show)

newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Show)

instance Enum Lvl where
  toEnum = Lvl
  fromEnum l = l.unLvl

instance Enum Idx where
  toEnum = Idx
  fromEnum i = i.unIdx

nextLvl :: Lvl -> Lvl
nextLvl (Lvl l) = Lvl (l + 1)

nextLvls :: Lvl -> Int -> Lvl
nextLvls (Lvl l) n = Lvl (l + n)

lvlToIdx :: Lvl -> Lvl -> Idx
lvlToIdx (Lvl l) (Lvl i) = Idx (l - i - 1)

-- Spines and arguments

data Arg t = Arg {mode :: PiMode, arg :: t} deriving (Eq, Show, Functor, Traversable, Foldable)

type Spine t = Seq (Arg t)

mapSpine :: (t -> t') -> Spine t -> Spine t'
mapSpine f = fmap (fmap f)

mapSpineM :: (Monad m) => (t -> m t') -> Spine t -> m (Spine t')
mapSpineM f = traverse (traverse f)

-- Metas

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show)

-- Globals

newtype CtorGlobal = CtorGlobal {globalName :: Name} deriving (Eq, Show)

newtype DataGlobal = DataGlobal {globalName :: Name} deriving (Eq, Show)

newtype DefGlobal = DefGlobal {globalName :: Name} deriving (Eq, Show)

newtype PrimGlobal = PrimGlobal {globalName :: Name} deriving (Eq, Show)

data Glob = CtorGlob CtorGlobal | DataGlob DataGlobal | DefGlob DefGlobal | PrimGlob PrimGlobal deriving (Eq, Show)

globName :: Glob -> Name
globName (CtorGlob g) = g.globalName
globName (DataGlob g) = g.globalName
globName (DefGlob g) = g.globalName
globName (PrimGlob g) = g.globalName

-- Tags

data Tag = UnfoldTag deriving (Eq, Ord, Enum, Bounded)

instance (Monad m) => Pretty m Tag where
  pretty t = return $ "#" ++ show t

instance (Monad m) => Pretty m (Set Tag) where
  pretty ts = return $ intercalate " " (map show $ toList ts) ++ (if null ts then "" else " ")

instance Show Tag where
  show UnfoldTag = "unfold"

class (Monad m) => HasNameSupply m where
  uniqueName :: m Name

-- Printing

instance (Monad m) => Pretty m Name where
  pretty (Name n) = return n

instance (Pretty m x) => Pretty m (Arg x) where
  pretty (Arg m x) = case m of
    Explicit -> singlePretty x
    Implicit -> do
      x' <- pretty x
      return $ "[" ++ x' ++ "]"
    Instance -> do
      x' <- pretty x
      return $ "[[" ++ x' ++ "]]"

instance (Monad m) => Pretty m PiMode where
  pretty Implicit = return "implicit"
  pretty Explicit = return "explicit"
  pretty Instance = return "instance"

instance (Monad m) => Pretty m Times where
  pretty (Finite n) = return $ show n
  pretty NegInf = return "-inf"
  pretty PosInf = return "inf"

instance (Pretty m a) => Pretty m (Lit a) where
  pretty (StringLit s) = return $ show s
  pretty (CharLit c) = return $ show c
  pretty (NatLit n) = return $ show n
  pretty (FinLit n t) = do
    t' <- pretty t
    return $ show n ++ " % " ++ t'

-- Files

class (Monad m) => HasProjectFiles m where
  getProjectFileContents :: String -> m (Maybe String)

instance (HasProjectFiles m) => Pretty m Loc where
  pretty NoLoc = return ""
  pretty (Loc f s e) = do
    -- Fetch the contents of the file
    contents' <- getProjectFileContents f
    case contents' of
      Nothing -> return "<unknown file>"
      Just contents -> do
        let contentLines = lines contents

        -- Extract the lines that span the start and end positions
        let startLine = s.line
            endLine = e.line
            relevantLines = zip [startLine .. endLine] $ take (endLine - startLine + 1) $ drop (startLine - 1) contentLines

        -- Generate the underline string with carets
        let startCol = s.col
            endCol = if startLine == endLine then e.col else length (snd (last relevantLines))
            underline = replicate (startCol + length (show startLine) + 2 - 1) ' ' ++ replicate (endCol - startCol) '^'

        -- Combine the relevant lines with the underline
        let numberedLines = unlines $ map (\(num, line) -> show num ++ " | " ++ line) relevantLines
        let highlightedCode = numberedLines ++ "\n" ++ underline

        return highlightedCode
