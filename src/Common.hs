{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}

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

-- | Whether a pi type is implicit or explicit.
data PiMode
  = Implicit
  | Explicit
  | Instance
  deriving (Eq, Show)

-- | An identifier
newtype Name = Name {unName :: String} deriving (Eq, Show, Ord)

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
data Loc = NoLoc | Loc Pos Pos deriving (Eq, Show)

-- | A monoid instance for locations, that gets the maximum span.
instance Monoid Loc where
  mempty = NoLoc

instance Semigroup Loc where
  NoLoc <> NoLoc = NoLoc
  NoLoc <> Loc s e = Loc s e
  Loc s e <> NoLoc = Loc s e
  Loc s1 e1 <> Loc s2 e2 = Loc (min s1 s2) (max e1 e2)

instance Ord Loc where
  NoLoc <= _ = True
  _ <= NoLoc = False
  Loc s1 e1 <= Loc s2 e2 = s1 <= s2 && e1 <= e2

-- | A position in the source code, represented by a line and column number.
data Pos = Pos Int Int deriving (Eq, Show)

-- | An ordering for positions, that gets the minimum position.
instance Ord Pos where
  Pos l1 c1 <= Pos l2 c2 = l1 < l2 || (l1 == l2 && c1 <= c2)

-- | Get the starting position of a location.
startPos :: Loc -> Maybe Pos
startPos NoLoc = Nothing
startPos (Loc start _) = Just start

-- | Get the ending position of a location.
endPos :: Loc -> Maybe Pos
endPos NoLoc = Nothing
endPos (Loc _ end) = Just end

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

instance Show Tag where
  show UnfoldTag = "unfold"

class (Monad m) => HasNameSupply m where
  uniqueName :: m Name

-- Printing

instance Pretty Name where
  pretty (Name n) = n

instance (Pretty x) => Pretty (Arg x) where
  pretty (Arg m x) = case m of
    Explicit -> singlePretty x
    Implicit -> "[" ++ pretty x ++ "]"
    Instance -> "[[" ++ pretty x ++ "]]"

instance Pretty Times where
  pretty (Finite n) = show n
  pretty NegInf = "-inf"
  pretty PosInf = "inf"

instance (Pretty a) => Pretty (Lit a) where
  pretty (StringLit s) = show s
  pretty (CharLit c) = show c
  pretty (NatLit n) = show n
  pretty (FinLit n t) = show n ++ " % " ++ pretty t
