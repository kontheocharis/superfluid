{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

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
    Lit (..),
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
    ItemId (..),
    itemId,
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

import Algebra.Lattice (Lattice (..))
import Control.Applicative ((<|>))
import Control.Exception (assert)
import Control.Monad (foldM, join)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Extra (firstJustM)
import Control.Monad.Identity (runIdentity)
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Generics (Data)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.Extra (firstJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), ViewL (..), ViewR (..), (><))
import qualified Data.Sequence as S
import Data.Traversable (for)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Natural (Natural)
import GHC.TypeNats (Nat)
import Common (Name, Loc)



newtype Sig = Sig {members :: [Glob]}

class (Eval m, Unify m, MonadError ElabError m) => Elab m where
  getCtx :: m Ctx
  setCtx :: Ctx -> m ()

  accessCtx :: (Ctx -> a) -> m a
  accessCtx f = f <$> getCtx

  modifyCtx :: (Ctx -> Ctx) -> m ()
  modifyCtx f = do
    ctx <- getCtx
    setCtx (f ctx)

  enterCtx :: (Ctx -> Ctx) -> m a -> m a
  enterCtx f a = do
    ctx <- getCtx
    setCtx (f ctx)
    a' <- a
    setCtx ctx
    return a'

data Ctx = Ctx {env :: Env VTm, lvl :: Lvl, types :: [VTy], names :: Map Name Lvl, currentLoc :: Maybe Loc}

bind :: Name -> VTy -> Ctx -> Ctx
bind x ty ctx = define x (VNeu (VVar ctx.lvl)) ty ctx

insertedBind :: Name -> VTy -> Ctx -> Ctx
insertedBind = bind

define :: Name -> VTm -> VTy -> Ctx -> Ctx
define x t ty ctx =
  ctx
    { env = t : ctx.env,
      lvl = nextLvl ctx.lvl,
      types = ty : ctx.types,
      names = M.insert x ctx.lvl ctx.names
    }

lookupName :: Name -> Ctx -> Maybe (Idx, VTy)
lookupName n ctx = case M.lookup n ctx.names of
  Just l -> let idx = lvlToIdx ctx.lvl l in Just (idx, ctx.types !! idx.unIdx)
  Nothing -> Nothing

definedValue :: Idx -> Ctx -> VTm
definedValue i ctx = ctx.env !! i.unIdx

located :: Loc -> Ctx -> Ctx
located l ctx = ctx {currentLoc = Just l}

freshUserMeta :: (Elab m) => Maybe Name -> m (STm, VTy)
freshUserMeta n = do
  m <- freshMeta >>= evalHere
  return undefined

freshMeta :: (Elab m) => m STy
freshMeta = undefined

insert :: (Elab m) => (STm, VTy) -> m (STm, VTy)
insert = undefined

evalHere :: (Elab m) => STm -> m VTm
evalHere t = do
  e <- accessCtx (\c -> c.env)
  eval e t

unifyHere :: (Elab m) => VTm -> VTm -> m ()
unifyHere t1 t2 = do
  l <- accessCtx (\c -> c.lvl)
  _ <- unify l t1 t2
  return ()

closeValHere :: (Elab m) => Int -> VTm -> m Closure
closeValHere n t = do
  (l, e) <- accessCtx (\c -> (c.lvl, c.env))
  t' <- quote (nextLvls l n) t
  close n e t'

closeHere :: (Elab m) => Int -> STm -> m Closure
closeHere n t = do
  e <- accessCtx (\c -> c.env)
  close n e t

forceHere :: (Elab m) => VTm -> m VTm
forceHere t = do
  l <- accessCtx (\c -> c.lvl)
  force l t

forcePiType :: (Elab m) => PiMode -> VTy -> m (VTy, Closure)
forcePiType m ty = do
  ty' <- forceHere ty
  case ty' of
    VPi m' _ a b -> do
      if m == m'
        then return (a, b)
        else throwError $ ImplicitMismatch m m'
    _ -> do
      a <- freshMeta >>= evalHere
      v <- uniqueName
      b <- closeHere 1 =<< enterCtx (bind v a) freshMeta
      unifyHere ty (VPi m v a b)
      return (a, b)

inferSpine :: (Elab m) => (STm, VTy) -> Spine PTm -> m (STm, VTy)
inferSpine (t, ty) Empty = return (t, ty)
inferSpine (t, ty) (Arg m u :<| sp) = do
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Explicit -> insert (t, ty)
    Instance -> error "unimplemented"
  (a, b) <- forcePiType m ty'
  u' <- check u a
  uv <- evalHere u'
  b' <- b $$ [uv]
  inferSpine (SApp m t' u', b') sp

lastIdx :: STm
lastIdx = SVar (Idx 0)

symbolicArgsForClosure :: Lvl -> Closure -> [VTm]
symbolicArgsForClosure l (Closure n _ t) = map (VNeu . VVar . Lvl . (+ l.unLvl)) [0 .. n - 1]

forbidPat :: (Elab m) => PTm -> m ()
forbidPat p = ifInPat (throwError $ InvalidPattern p) (return ())

newPatBind :: (Elab m) => Name -> m (STm, VTy)
newPatBind x = do
  ty <- evalHere =<< freshMeta
  modifyCtx (bind x ty)
  return (lastIdx, ty)

ifIsCtorName :: (Elab m) => Idx -> Name -> (CtorGlobal -> m a) -> m a -> m a
ifIsCtorName i n a b = do
  v <- accessCtx (definedValue i) >>= forceHere
  case v of
    VGlobal (CtorGlob g@(CtorGlobal s)) Empty | s == n -> a g
    _ -> b

ifIsData :: (Elab m) => VTy -> (DataGlobal -> m a) -> m a -> m a
ifIsData v a b = do
  v' <- forceHere v
  case v' of
    VGlobal (DataGlob g@(DataGlobal s)) _ -> a g
    _ -> b

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterCtx (located l) $ infer t
  PName x -> do
    n <- accessCtx (lookupName x)
    case n of
      Just (i, t) ->
        ifInPat
          (ifIsCtorName i x (\g -> return (SGlobal (CtorGlob g), t)) (newPatBind x))
          (return (SVar i, t))
      Nothing -> ifInPat (newPatBind x) (throwError $ UnresolvedVariable x)
  PLam m x t -> do
    forbidPat term
    a <- freshMeta >>= evalHere
    (t', b) <- enterCtx (bind x a) $ infer t >>= insert
    b' <- closeValHere 1 b
    return (SLam m x t', VPi m x a b')
  PApp {} -> do
    let (subject, sp) = toPSpine term
    (s, sTy) <- infer subject
    inferSpine (s, sTy) sp
  PU -> forbidPat term >> return (SU, VU)
  PPi m x a b -> do
    forbidPat term
    a' <- check a VU
    av <- evalHere a'
    b' <- enterCtx (bind x av) $ check b VU
    return (SPi m x a' b', VU)
  PLet x a t u -> do
    forbidPat term
    a' <- check a VU
    va <- evalHere a'
    t' <- check t va
    vt <- evalHere t'
    (u', b) <- enterCtx (define x vt va) $ infer u
    pure (SLet x a' t' u', b)
  PRepr m x -> do
    forbidPat term
    (x', ty) <- infer x
    reprTy <- vRepr m ty
    return (SRepr m x', reprTy)
  PHole n -> do
    forbidPat term
    freshUserMeta (Just n)
  PWild ->
    ifInPat
      (uniqueName >>= newPatBind)
      (freshUserMeta Nothing)
  PCase s cs -> do
    forbidPat term
    (s', sTy) <- infer s
    vs <- evalHere s'
    d <- ifIsData sTy return (throwError $ InvalidCaseSubject s)

    return undefined
  PLit l -> return undefined

check :: (Elab m) => PTm -> VTy -> m STm
check term typ = do
  typ' <- forceHere typ
  case (term, typ') of
    (PLocated l t, ty) -> enterCtx (located l) $ check t ty
    (PLam m x t, VPi m' _ a b) | m == m' -> do
      forbidPat term
      vb <- evalInOwnCtx b
      SLam m x <$> enterCtx (bind x a) (check t vb)
    (t, VPi Implicit x' a b) -> do
      vb <- evalInOwnCtx b
      SLam Implicit x' <$> enterCtx (insertedBind x' a) (check t vb)
    (PLet x a t u, ty) -> do
      forbidPat term
      a' <- check a VU
      va <- evalHere a'
      t' <- check t va
      vt <- evalHere t'
      u' <- enterCtx (define x vt va) $ check u ty
      return (SLet x a' t' u')
    (PRepr m t, VNeu (VRepr m' t')) | m == m' -> do
      forbidPat term
      tc <- check t (VNeu (VHead t'))
      return $ SRepr m tc
    (PRepr m t, ty) | m < mempty -> do
      forbidPat term
      (t', ty') <- infer t >>= insert
      reprTy <- vRepr (inv m) ty
      unifyHere reprTy ty'
      return $ SRepr m t'
    (te, ty) -> do
      (te', ty') <- infer te >>= insert
      unifyHere ty ty'
      return te'

-- | A term
data TermValue
  = -- Dependently-typed lambda calculus with Pi and Sigma:
    PiT PiMode Var Type Term
  | Lam PiMode Var Term
  | Let Var Type Term Term
  | App PiMode Term Term
  | SigmaT Var Type Term
  | Pair Term Term
  | Case (Maybe Term) Term [(Pat, Maybe Term)] -- if the branch is Nothing, it is "impossible"
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
  | -- | A literal
    Lit (Lit Term)
  | -- | Metavar identified by an integer
    Meta Var
  | -- | Represent a term
    Rep Term
  | -- | Unrepresent a term of the given named type
    Unrep String Term
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A term with associated data.
data Term = Term {value :: TermValue, dat :: TermData} deriving (Eq, Generic, Data, Typeable, Show)

-- | Alias for type values (just for documentation purposes)
type TypeValue = TermValue

-- | Alias for pattern values (just for documentation purposes)
type PatValue = TermValue

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
  | ReprData ReprDataItem
  | ReprDecl ReprDeclItem
  | Prim PrimItem
  deriving (Eq, Generic, Data, Typeable, Show)

-- | An identifier for an item in a signature.
data ItemId
  = DataId String
  | DeclId String
  | ReprDataId String
  | ReprDeclId String
  | PrimId String
  deriving (Eq, Generic, Data, Typeable, Show)

-- | Get the identifier of an item.
itemId :: Item -> ItemId
itemId (Decl (DeclItem name _ _ _ _ _)) = DeclId name
itemId (Data (DataItem name _ _)) = DataId name
itemId (ReprData (ReprDataItem src _ _ _)) = ReprDataId (show src)
itemId (ReprDecl (ReprDeclItem name _)) = ReprDeclId name
itemId (Prim (PrimItem name _)) = PrimId name

-- | Get the name of an item.
itemName :: Item -> Maybe String
itemName (Decl d) = Just d.name
itemName (Data d) = Just d.name
itemName (ReprData _) = Nothing
itemName (ReprDecl _) = Nothing
itemName (Prim p) = Just p.name

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
    loc :: Loc,
    isRecursive :: Bool,
    unfold :: Bool
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
      (Case elim t cs) -> Case <$> traverse (mapTermM f) elim <*> mapTermM f t <*> mapM (\(p, c) -> (,) <$> mapTermM f p <*> traverse (mapTermM f) c) cs
      TyT -> return TyT
      Wild -> return Wild
      (V v) -> return $ V v
      (Global s) -> return $ Global s
      (Hole i) -> return $ Hole i
      (Meta i) -> return $ Meta i
      (Lit (FinLit n i)) -> Lit . FinLit n <$> mapTermM f i
      (Lit l) -> return $ Lit l
      (Rep t) -> Rep <$> mapTermM f t
      (Unrep s t) -> Unrep s <$> mapTermM f t

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
mapItemM f (Decl (DeclItem name ty term pos recu unf)) = Decl <$> (DeclItem name <$> mapTermM f ty <*> mapTermM f term <*> pure pos <*> pure recu <*> pure unf)
mapItemM f (Data (DataItem name ty ctors)) = Data <$> (DataItem name <$> mapTermM f ty <*> mapM (mapCtorItemM f) ctors)
mapItemM f (ReprData d) = ReprData <$> mapReprDataItemM f d
mapItemM f (ReprDecl d) = ReprDecl <$> mapReprDeclItemM f d
mapItemM f (Prim (PrimItem name ty)) = Prim . PrimItem name <$> mapTermM f ty

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
        (Rep {}) -> True
        (Unrep {}) -> True
        _ -> False

-- | Check if a given term is a valid pattern (no typechecking).
isValidPat :: Term -> Bool
isValidPat (Term (App _ a b) _) = isValidPat a && isValidPat b
isValidPat (Term (V _) _) = True
isValidPat (Term Wild _) = True
isValidPat (Term (Pair p1 p2) _) = isValidPat p1 && isValidPat p2
isValidPat _ = False

-- | Type alias for terms that are expected to be types (just for documentation purposes).
type Type = Term

-- | Type alias for terms that are expected to be patterns (just for documentation purposes).
type Pat = Term

-- | A global name is a string.
type GlobalName = String

-- | A variable
-- Represented by a string name and a unique integer identifier (no shadowing).
data Var = Var {name :: String, idx :: Int} deriving (Eq, Ord, Generic, Data, Typeable, Show)
