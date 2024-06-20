{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module Lang
  ( Type,
    GlobalName,
    Var (..),
    Term (..),
    TermValue (..),
    HasTermValue (..),
    TermData (..),
    PatValue,
    TypeValue,
    Loc (..),
    Pos (..),
    Pat,
    Item (..),
    PrimItem (..),
    DataItem (..),
    ReprItem (..),
    ReprSomeItem (..),
    ReprDataItem (..),
    ReprDeclItem (..),
    ReprDataCtorItem (..),
    ReprDataCaseItem (..),
    CtorItem (..),
    DeclItem (..),
    Program (..),
    HasLoc (..),
    TermMappable (..),
    MapResult (..),
    PiMode (..),
    mapTerm,
    mapTermM,
    piTypeToList,
    listToPiType,
    listToApp,
    itemName,
    isValidPat,
    termLoc,
    genTerm,
    termDataAt,
    locatedAt,
    typedAs,
    appToList,
    lamsToList,
    letToList,
    lams,
    startPos,
    endPos,
    isCompound,
    emptyTermData,
  )
where

import Control.Monad.Identity (runIdentity)
import Data.Generics (Data)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

-- | Type alias for terms that are expected to be types (just for documentation purposes).
type Type = Term

-- | Type alias for terms that are expected to be patterns (just for documentation purposes).
type Pat = Term

-- | A global name is a string.
type GlobalName = String

-- | A variable
-- Represented by a string name and a unique integer identifier (no shadowing).
data Var = Var { name :: String, idx :: Int } deriving (Eq, Ord, Generic, Data, Typeable, Show)

-- | Whether a pi type is implicit or explicit.
data PiMode = Implicit | Explicit deriving (Eq, Generic, Data, Typeable, Show)

-- | A term
data TermValue
  = -- Dependently-typed lambda calculus with Pi and Sigma:
    PiT PiMode Var Type Term
  | Lam PiMode Var Term
  | Let Var Type Term Term
  | App PiMode Term Term
  | SigmaT Var Type Term
  | Pair Term Term
  | Case Term [(Pat, Term)]
  | -- | Type of types (no universe polymorphism)
    TyT
  | -- | Variable
    V Var
  | -- | Wildcard pattern
    Wild
  | -- | Global variable (declaration)
    Global String
  | -- | Hole identified by an integer
    Hole Var
  | -- | Metavar identified by an integer
    Meta Var
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A term with associated data.
data Term = Term {value :: TermValue, dat :: TermData} deriving (Eq, Generic, Data, Typeable, Show)

-- | Alias for type values (just for documentation purposes)
type TypeValue = TermValue

-- | Alias for pattern values (just for documentation purposes)
type PatValue = TermValue

-- | An optional location in the source code, represented by a start (inclusive) and
-- end (exclusive) position.
data Loc = NoLoc | Loc Pos Pos deriving (Eq, Generic, Data, Typeable, Show)

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
data Pos = Pos Int Int deriving (Eq, Generic, Data, Typeable, Show)

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

-- | Auxiliary data contained alongside a term.
--
-- For now stores only the location in the source code, but will
-- be extended to store type information too.
data TermData = TermData {loc :: Loc, annotTy :: Maybe Type} deriving (Eq, Generic, Data, Typeable, Show)

-- | Empty term data.
emptyTermData :: TermData
emptyTermData = TermData NoLoc Nothing

-- | Class of types that have a location.
class HasLoc a where
  getLoc :: a -> Loc

instance HasLoc Term where
  getLoc = termLoc

instance HasLoc TermData where
  getLoc x = x.loc

instance HasLoc Loc where
  getLoc = id

-- | Create a term with the given value and location.
locatedAt :: (HasLoc a) => a -> TermValue -> Term
locatedAt a t = Term t (termDataAt (getLoc a))

-- | Create term data with the given location.
termDataAt :: (HasLoc a) => a -> TermData
termDataAt x = TermData (getLoc x) Nothing

-- | Get the term data from a term.
termLoc :: Term -> Loc
termLoc x = x.dat.loc

-- | Set the type annotation of a term.
typedAs :: Type -> Term -> Term
typedAs ty (Term t d) = Term t (d {annotTy = Just ty})

-- | Generated term, no data
genTerm :: TermValue -> Term
genTerm t = Term t emptyTermData

-- | Convert a pi type to a list of types and the return type.
piTypeToList :: Type -> ([(PiMode, Var, Type)], Type)
piTypeToList (Term (PiT m v ty1 ty2) _) = let (tys, ty) = piTypeToList ty2 in ((m, v, ty1) : tys, ty)
piTypeToList t = ([], t)

-- | Convert a list of types and the return type to a pi type.
listToPiType :: ([(PiMode, Var, Type)], Type) -> Type
listToPiType ([], ty) = ty
listToPiType ((m, v, ty1) : tys, ty2) = Term (PiT m v ty1 (listToPiType (tys, ty2))) emptyTermData

-- | Convert a *non-empty* list of terms to an application term
listToApp :: (Term, [(PiMode, Term)]) -> Term
listToApp (t, ts) = foldl (\acc (m, x) -> Term (App m acc x) (termDataAt (termLoc acc <> termLoc x))) t ts

-- | Convert an application term to a *non-empty* list of terms
appToList :: Term -> (Term, [(PiMode, Term)])
appToList (Term (App m t1 t2) _) = let (t, ts) = appToList t1 in (t, ts ++ [(m, t2)])
appToList t = (t, [])

-- | Convert a let term to a list of bindings and the body term.
letToList :: Term -> ([(Var, Type, Term)], Term)
letToList (Term (Let v ty t1 t2) _) = let (bs, t) = letToList t2 in ((v, ty, t1) : bs, t)
letToList t = ([], t)

-- | Convert a lambda term to a list of variables and the body term.
lamsToList :: Term -> ([(PiMode, Var)], Term)
lamsToList (Term (Lam m v t) _) = let (vs, t') = lamsToList t in ((m, v) : vs, t')
lamsToList t = ([], t)

-- | Wrap a term in `n` lambdas.
lams :: [(PiMode, Var)] -> Term -> Term
lams [] t = t
lams ((m, v) : vs) t = Term (Lam m v (lams vs t)) (termDataAt t)

-- | An item is either a declaration or a data item.
data Item
  = Decl DeclItem
  | Data DataItem
  | Repr ReprItem
  | Prim PrimItem
  deriving (Eq, Generic, Data, Typeable, Show)

-- | Get the name of an item.
itemName :: Item -> String
itemName (Decl (DeclItem name _ _ _)) = name
itemName (Data (DataItem name _ _)) = name
itemName (Repr (ReprItem name _)) = name
itemName (Prim (PrimItem name _)) = name

-- | A representation item is a name, label, inputs, and target term.
data ReprItem = ReprItem
  { name :: String,
    contents :: [ReprSomeItem]
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprSomeItem = ReprData ReprDataItem | ReprDecl ReprDeclItem
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprDataCaseItem = ReprDataCaseItem
  { binds :: (Pat, Var, [(String, Pat)]), -- subjectBind, elimBind, [(ctorName, elimBind)]
    target :: Term
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprDataCtorItem = ReprDataCtorItem
  { src :: Pat,
    target :: Term
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprDataItem = ReprDataItem
  { src :: Pat,
    target :: Term,
    ctors :: [ReprDataCtorItem],
    cse :: Maybe ReprDataCaseItem
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprDeclItem = ReprDeclItem
  { src :: String,
    target :: Term
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A declaration is a sequence of clauses, defining the equations for a function.
data DeclItem = DeclItem
  { name :: String,
    ty :: Type,
    value :: Term,
    loc :: Loc
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A data item is an indexed inductive data type declaration, with a sequence
-- of constructors.
data DataItem = DataItem
  { name :: String,
    ty :: Type,
    ctors :: [CtorItem]
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A constructor item is a constructor name and type.
data CtorItem = CtorItem
  { name :: String,
    ty :: Type,
    idx :: Int,
    dataName :: String
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A primitive item is a primitive name and type.
data PrimItem = PrimItem
  { name :: String,
    ty :: Type
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A program is a sequence of items.
newtype Program = Program [Item]
  deriving (Eq, Generic, Data, Typeable, Show)

instance Semigroup Program where
  Program a <> Program b = Program (a <> b)

instance Monoid Program where
  mempty = Program []

-- | Result of a term map.
data MapResult a = Continue | Replace a | ReplaceAndContinue a

-- | Apply a function to a term, if it is a Just, otherwise return the term.
mapTerm :: (Term -> MapResult Term) -> Term -> Term
mapTerm f term = runIdentity $ mapTermM (return . f) term

-- | Apply a function to a term, if it is a Just, otherwise return the term (monadic).
mapTermM :: (Monad m) => (Term -> m (MapResult Term)) -> Term -> m Term
mapTermM f term = do
  term' <- f term
  case term' of
    Continue -> do
      mappedTerm <- mapTermRec term.value
      return (Term mappedTerm term.dat)
    ReplaceAndContinue t' -> do
      mappedTerm <- mapTermRec t'.value
      return (Term mappedTerm t'.dat)
    Replace t' -> return t'
  where
    mapTermRec t' = case t' of
      (PiT m v t1 t2) -> PiT m v <$> mapTermM f t1 <*> mapTermM f t2
      (Lam m v t) -> Lam m v <$> mapTermM f t
      (Let v t1 t2 t3) -> Let v <$> mapTermM f t1 <*> mapTermM f t2 <*> mapTermM f t3
      (App m t1 t2) -> App m <$> mapTermM f t1 <*> mapTermM f t2
      (SigmaT v t1 t2) -> SigmaT v <$> mapTermM f t1 <*> mapTermM f t2
      (Pair t1 t2) -> Pair <$> mapTermM f t1 <*> mapTermM f t2
      (Case t cs) -> Case <$> mapTermM f t <*> mapM (\(p, c) -> (,) <$> mapTermM f p <*> mapTermM f c) cs
      TyT -> return TyT
      Wild -> return Wild
      (V v) -> return $ V v
      (Global s) -> return $ Global s
      (Hole i) -> return $ Hole i
      (Meta i) -> return $ Meta i

class TermMappable t where
  -- | Apply a term function to an item.
  mapTermMappableM :: (Monad m) => (Term -> m (MapResult Term)) -> t -> m t

  -- | Apply a term function to an item (non-monadic)
  mapTermMappable :: (Term -> MapResult Term) -> t -> t
  mapTermMappable f = runIdentity . mapTermMappableM (return . f)

-- | Apply a term function to a constructor item.
mapCtorItemM :: (Monad m) => (Term -> m (MapResult Term)) -> CtorItem -> m CtorItem
mapCtorItemM f (CtorItem name ty idx d) = CtorItem name <$> mapTermM f ty <*> pure idx <*> pure d

-- | Apply a term function to a declaration item.
mapItemM :: (Monad m) => (Term -> m (MapResult Term)) -> Item -> m Item
mapItemM f (Decl (DeclItem name ty term pos)) = Decl <$> (DeclItem name <$> mapTermM f ty <*> mapTermM f term <*> pure pos)
mapItemM f (Data (DataItem name ty ctors)) = Data <$> (DataItem name <$> mapTermM f ty <*> mapM (mapCtorItemM f) ctors)
mapItemM f (Repr (ReprItem name c)) = Repr . ReprItem name <$> mapM (mapReprSomeItemM f) c
mapItemM f (Prim (PrimItem name ty)) = Prim . PrimItem name <$> mapTermM f ty

mapReprSomeItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprSomeItem -> m ReprSomeItem
mapReprSomeItemM f (ReprData d) = ReprData <$> mapReprDataItemM f d
mapReprSomeItemM f (ReprDecl d) = ReprDecl <$> mapReprDeclItemM f d

mapReprDataItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDataItem -> m ReprDataItem
mapReprDataItemM f (ReprDataItem src target ctors caseItem) =
  ReprDataItem <$> mapTermM f src <*> mapTermM f target <*> mapM (mapReprDataCtorItemM f) ctors <*> traverse (mapReprDataCaseItemM f) caseItem

mapReprDeclItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDeclItem -> m ReprDeclItem
mapReprDeclItemM f (ReprDeclItem name target) = ReprDeclItem name <$> mapTermM f target

mapReprDataCtorItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDataCtorItem -> m ReprDataCtorItem
mapReprDataCtorItemM f (ReprDataCtorItem src target) = ReprDataCtorItem <$> mapTermM f src <*> mapTermM f target

mapReprDataCaseItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDataCaseItem -> m ReprDataCaseItem
mapReprDataCaseItemM f (ReprDataCaseItem binds target) = ReprDataCaseItem binds <$> mapTermM f target

-- | Apply a term function to a program.
mapProgramM :: (Monad m) => (Term -> m (MapResult Term)) -> Program -> m Program
mapProgramM f (Program items) = Program <$> mapM (mapItemM f) items

instance TermMappable Term where
  mapTermMappableM = mapTermM

instance TermMappable CtorItem where
  mapTermMappableM = mapCtorItemM

instance TermMappable Item where
  mapTermMappableM = mapItemM

instance TermMappable Program where
  mapTermMappableM = mapProgramM

instance TermMappable () where
  mapTermMappableM _ = return

-- Show instances for pretty printing:

class HasTermValue a where
  getTermValue :: a -> TermValue

instance HasTermValue Term where
  getTermValue t = t.value

instance HasTermValue TermValue where
  getTermValue = id

-- | Check if a term is compound (i.e. contains spaces), for formatting purposes.
isCompound :: (HasTermValue a) => a -> Bool
isCompound x =
  let x' = getTermValue x
   in case x' of
        (PiT {}) -> True
        (Lam {}) -> True
        (Let {}) -> True
        (Case {}) -> True
        (App {}) -> True
        (SigmaT {}) -> True
        _ -> False

-- | Check if a given term is a valid pattern (no typechecking).
isValidPat :: Term -> Bool
isValidPat (Term (App _ a b) _) = isValidPat a && isValidPat b
isValidPat (Term (V _) _) = True
isValidPat (Term Wild _) = True
isValidPat (Term (Pair p1 p2) _) = isValidPat p1 && isValidPat p2
isValidPat _ = False
