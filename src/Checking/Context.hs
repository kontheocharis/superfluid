module Checking.Context
  ( Judgement (..),
    Ctx (..),
    Signature (..),
    TcState (..),
    Tc,
    TcError (..),
    FlexApp (..),
    addEmptyDataItemToRepr,
    addCtorItemToRepr,
    addItem,
    addItems,
    addCaseItemToRepr,
    addSubst,
    addTyping,
    addTypings,
    findReprForCase,
    findReprForGlobal,
    classifyApp,
    ctx,
    emptyTcState,
    enterCtx,
    enterCtxMod,
    enterPat,
    enterSignatureMod,
    freshMeta,
    freshMetaAt,
    freshVar,
    getType,
    inCtx,
    inSignature,
    inState,
    lookupItemOrCtor,
    lookupSubst,
    lookupType,
    lookupTypeOrError,
    getDataItem,
    modifyCtx,
    modifyItem,
    addItemToRepr,
    modifySignature,
    registerHole,
    registerWild,
    addEmptyRepr,
    runTc,
    setType,
    solveMeta,
    withinCtx,
  )
where

import Control.Applicative ((<|>))
import Control.Monad (join)
import Control.Monad.Except (throwError)
import Control.Monad.State (MonadState (..), StateT (runStateT), gets, modify)
import Data.List (find, intercalate)
import Data.Map (Map, empty, insert, (!?))
import Data.Maybe (isJust)
import Interface.Pretty
import Lang
  ( CtorItem (..),
    DataItem (DataItem),
    HasLoc (..),
    Item (..),
    Loc (..),
    Pat,
    ReprDataCaseItem (..),
    ReprDataCtorItem (..),
    ReprDataItem (..),
    ReprDeclItem (..),
    ReprItem (..),
    ReprSomeItem (..),
    Term (..),
    TermValue (..),
    Type,
    Var (..),
    genTerm,
    itemName,
    lams,
    listToApp,
    locatedAt,
  )

-- | A typing judgement.
data Judgement = Typing Var Type | Subst Var Term

instance Show Judgement where
  show (Typing v ty) = printVal v ++ " : " ++ printVal ty
  show (Subst v t) = printVal v ++ " = " ++ printVal t

-- | A context, represented as a list of typing judgements.
newtype Ctx = Ctx [Judgement]

instance Show Ctx where
  show (Ctx js) = intercalate "\n" $ map show js

-- | A signature, represented as a list of items.
newtype Signature = Signature [Item] deriving (Show)

-- | A typechecking error.
data TcError
  = VariableNotFound Var
  | Mismatch Term Term
  | ItemNotFound String
  | CannotUnifyTwoHoles Var Var
  | CannotInferHoleType Var
  | NotAFunction Term
  | PatternNotSupported Pat
  | WrongConstructors [String] [String]
  | CannotUseReprAsTerm String

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ printVal v
  show (Mismatch t1 t2) =
    "Term mismatch: " ++ printSingleVal t1 ++ " vs " ++ printSingleVal t2 ++ " (at " ++ printVal (getLoc t1) ++ " and " ++ printVal (getLoc t2) ++ ")"
  show (ItemNotFound s) = "Item not found: " ++ s
  show (CannotUnifyTwoHoles h1 h2) = "Cannot unify two holes: " ++ printSingleVal h1 ++ " and " ++ printSingleVal h2
  show (CannotInferHoleType h) = "Cannot infer hole type: " ++ printSingleVal h
  show (NotAFunction t) = "Not a function: " ++ printSingleVal t
  show (PatternNotSupported p) = "Pattern is not supported yet: " ++ printVal p
  show (WrongConstructors cs1 cs2) = "Wrong constructors: got " ++ intercalate ", " cs1 ++ " but expected " ++ intercalate ", " cs2
  show (CannotUseReprAsTerm r) = "Cannot use representation " ++ r ++ " as a term yet!"

-- | The typechecking state.
data TcState = TcState
  { -- | The current context.
    ctx :: Ctx,
    -- | The signature.
    signature :: Signature,
    -- | Unique variable counter.
    varCounter :: Int,
    -- | Whether we are in a pattern
    inPat :: Bool,
    -- | Term types, indexed by location.
    termTypes :: Map Loc Type,
    -- | Meta values, indexed by variable.
    metaValues :: Map Var Term,
    -- | Hole/wild locations, to substitute in the end.
    holeLocs :: Map Loc (Maybe Var),
    -- | Identify impossible cases in the given declarations
    identifyImpossiblesIn :: [String]
  }
  deriving (Show)

-- | The empty typechecking state.
emptyTcState :: TcState
emptyTcState = TcState (Ctx []) (Signature []) 0 False empty empty empty []

-- | The typechecking monad.
type Tc a = StateT TcState (Either TcError) a

-- | Run a typechecking computation.
runTc :: Tc a -> Either TcError (a, TcState)
runTc tc = do
  (res, endState) <- runStateT tc emptyTcState
  return (res, endState)

-- | Map over some context.
withSomeCtx :: (TcState -> c) -> (c -> Tc a) -> Tc a
withSomeCtx ct f = do
  s <- get
  f (ct s)

-- | Get the current context.
ctx :: TcState -> Ctx
ctx s = s.ctx

-- | Get the current signature.
sig :: TcState -> Signature
sig s = s.signature

-- | Monadic map over the current context.
withinCtx :: (Ctx -> Tc a) -> Tc a
withinCtx = withSomeCtx ctx

-- | Map over the current context.
inCtx :: (Ctx -> a) -> Tc a
inCtx f = withSomeCtx ctx (return . f)

-- | Map over the current typechecking state.
inState :: (TcState -> a) -> Tc a
inState f = withSomeCtx id (return . f)

-- | Map over the signature.
inSignature :: (Signature -> a) -> Tc a
inSignature f = withSomeCtx sig (return . f)

-- | Get the type of a term.
getType :: Term -> Tc (Maybe Type)
getType t = do
  tys <- gets (\s -> s.termTypes)
  case tys !? getLoc t of
    Just ty -> return $ Just ty
    Nothing -> return Nothing

-- | Set the type of a term.
setType :: Term -> Type -> Tc ()
setType t ty = modify $ \s -> s {termTypes = insert (getLoc t) ty s.termTypes}

-- | Enter a pattern by setting the inPat flag to True.
enterPat :: Tc a -> Tc a
enterPat p = do
  s <- get
  put $ s {inPat = True}
  res <- p
  s' <- get
  put $ s' {inPat = False}
  return res

-- | Update the current context.
enterCtxMod :: (Ctx -> Ctx) -> Tc a -> Tc a -- todo: substitute in a
enterCtxMod f op = do
  s <- get
  let prevCtx = ctx s
  put $ s {ctx = f prevCtx}
  res <- op
  s' <- get
  put $ s' {ctx = prevCtx}
  return res

-- | Update the current signature.
enterSignatureMod :: (Signature -> Signature) -> Tc a -> Tc a -- todo: substitute in a
enterSignatureMod f op = do
  s <- get
  let prevCtx = sig s
  put $ s {signature = f prevCtx}
  res <- op
  s' <- get
  put $ s' {signature = prevCtx}
  return res

-- | Enter a new context and exit it after the operation.
enterCtx :: Tc a -> Tc a
enterCtx = enterCtxMod id

-- | Update the current context.
modifyCtx :: (Ctx -> Ctx) -> Tc ()
modifyCtx f = do
  s <- get
  put $ s {ctx = f (ctx s)}

-- | Update the signature.
modifySignature :: (Signature -> Signature) -> Tc ()
modifySignature f = do
  s <- get
  put $ s {signature = f (sig s)}

-- | Lookup a substitution of a variable in the current context.
lookupSubst :: Var -> Ctx -> Maybe Term
lookupSubst _ (Ctx []) = Nothing
lookupSubst v (Ctx ((Subst v' term) : c)) = if v == v' then Just term else lookupSubst v (Ctx c)
lookupSubst v (Ctx (_ : c)) = lookupSubst v (Ctx c)

-- | Lookup the type of a variable in the current context.
lookupType :: Var -> Ctx -> Maybe Type
lookupType _ (Ctx []) = Nothing
lookupType v (Ctx ((Typing v' ty) : c)) = if v == v' then Just ty else lookupType v (Ctx c)
lookupType v (Ctx (_ : c)) = lookupType v (Ctx c)

-- | Lookup the type of a variable in the current context.
lookupTypeOrError :: Var -> Ctx -> Tc Type
lookupTypeOrError v c = case lookupType v c of
  Nothing -> throwError $ VariableNotFound v
  Just ty -> return ty

-- | Lookup the declaration of a global variable in the signature.
lookupItemOrCtor :: String -> Signature -> Maybe (Either Item CtorItem)
lookupItemOrCtor _ (Signature []) = Nothing
lookupItemOrCtor s (Signature (d : _)) | s == itemName d = Just (Left d)
lookupItemOrCtor s (Signature ((Data (DataItem _ _ ctors)) : c)) =
  (Right <$> find (\(CtorItem name _ _ _) -> name == s) ctors) <|> lookupItemOrCtor s (Signature c)
lookupItemOrCtor s (Signature (_ : c)) = lookupItemOrCtor s (Signature c)

-- | Add a variable to the current context.
addTyping :: Var -> Type -> Ctx -> Ctx
addTyping v t (Ctx c) = Ctx (Typing v t : c)

-- | Add a list of typings to the current context.
addTypings :: [(Var, Type)] -> Ctx -> Ctx
addTypings [] c = c
addTypings ((v, t) : vs) c = addTyping v t (addTypings vs c)

-- | Add a substitution to the current context.
addSubst :: Var -> Term -> Ctx -> Ctx
addSubst v t (Ctx c) = Ctx (Subst v t : c)

-- | Add a declaration to the signature.
addItem :: Item -> Signature -> Signature
addItem d (Signature c) = Signature (d : c)

-- | Add a list of items to the signature.
addItems :: [Item] -> Signature -> Signature
addItems is s = foldl (flip addItem) s is

-- | Modify an item in the signature.
modifyItem :: String -> (Item -> Item) -> Signature -> Signature
modifyItem _ _ (Signature []) = Signature []
modifyItem s f (Signature (d : c)) | s == itemName d = Signature (f d : c)
modifyItem _ _ (Signature (d : c)) = Signature (d : c)

-- | Get a fresh variable.
freshVarPrefixed :: String -> Tc Var
freshVarPrefixed n = do
  s <- get
  let h = s.varCounter
  put $ s {varCounter = h + 1}
  return $ Var (n ++ show h) h

-- | Get a fresh variable.
freshVar :: Tc Var
freshVar = freshVarPrefixed "v"

-- | Get all variables in a context.
ctxVars :: Ctx -> [Var]
ctxVars (Ctx []) = []
ctxVars (Ctx ((Typing v _) : c)) = v : ctxVars (Ctx c)
ctxVars (Ctx (_ : c)) = ctxVars (Ctx c)

-- | Get a fresh applied metavariable in the current context.
freshMetaAt :: (HasLoc a) => a -> Tc Term
freshMetaAt h = do
  v <- freshVarPrefixed "m"
  vrs <- inCtx ctxVars
  let (m, ms) = (genTerm (Meta v), map (genTerm . V) vrs)
  let t = listToApp (m, ms)
  return $ locatedAt h t.value

-- | Get a fresh applied metavariable in the current context.
freshMeta :: Tc Term
freshMeta = freshMetaAt NoLoc

-- | Register a hole.
registerHole :: Loc -> Var -> Tc ()
registerHole l v = do
  s <- get
  put $ s {holeLocs = insert l (Just v) s.holeLocs}

-- | Register an underscore/wild.
registerWild :: Loc -> Tc ()
registerWild l = modify $ \s -> s {holeLocs = insert l Nothing s.holeLocs}

-- | Solve a meta.
solveMeta :: Var -> Term -> Tc ()
solveMeta h t = modify $ \s -> s {metaValues = insert h t s.metaValues}

-- | A flexible (meta) application.
data FlexApp = Flex Var [Term] deriving (Show)

-- | Add a term to a `FlexApp`
addTerm :: Term -> FlexApp -> FlexApp
addTerm t (Flex h ts) = Flex h (ts ++ [t])

-- | Interpret a `FlexApp`
classifyApp :: Term -> Maybe FlexApp
classifyApp (Term (Meta h) _) = return $ Flex h []
classifyApp (Term (App t1 t2) _) = do
  c <- classifyApp t1
  return $ addTerm t2 c
classifyApp _ = Nothing

-- | Add a representation to the signature, without any contents.
addEmptyRepr :: String -> Signature -> Signature
addEmptyRepr rName = addItem (Repr (ReprItem rName []))

-- | Add a representation item to a representation in the signature.
addItemToRepr :: String -> ReprSomeItem -> Signature -> Signature
addItemToRepr rName item = modifyItem rName $ \case
  Repr (ReprItem n cs) -> Repr (ReprItem n (item : cs))
  _ -> error $ "Representation" ++ rName ++ " is not a representation item"

-- | Add an empty data item to a representation in a signature.
--
-- Assumes that the representation is already present and empty.
addEmptyDataItemToRepr :: String -> String -> [Var] -> Term -> Signature -> Signature
addEmptyDataItemToRepr rName name binds target = addItemToRepr rName $ ReprData (ReprDataItem name binds target [] Nothing)

-- | Modify representation items in a signature.
modifyReprItems :: String -> (ReprSomeItem -> ReprSomeItem) -> Signature -> Signature
modifyReprItems rName f =
  modifyItem rName $ \case
    Repr (ReprItem n cs) ->
      Repr $ ReprItem n $ map f cs
    _ -> error $ "Representation" ++ rName ++ " is not a representation item"

-- | Add a constructor item to a representation in a signature.
addCtorItemToRepr :: String -> String -> ReprDataCtorItem -> Signature -> Signature
addCtorItemToRepr rName dName item = modifyReprItems rName go
  where
    go t@(ReprData d)
      | d.name == dName = ReprData $ d {ctors = d.ctors ++ [item]}
      | otherwise = t
    go t = t

-- | Add a case item to a representation in a signature.
addCaseItemToRepr :: String -> String -> ReprDataCaseItem -> Signature -> Signature
addCaseItemToRepr rName dName item = modifyReprItems rName go
  where
    go t@(ReprData d)
      | d.name == dName = ReprData $ d {cse = Just item}
      | otherwise = t
    go t = t

-- | Find a representation for the given global name.
-- Returns the name of the representation and the term.
findReprForGlobal :: String -> Tc (Maybe (String, Term))
findReprForGlobal name = do
  (Signature items) <- gets sig
  return $ join $ find isJust $ map findRepr items
  where
    findRepr (Repr (ReprItem rName contents)) = join $ find isJust $ map (findReprData rName) contents
    findRepr _ = Nothing

    findReprData rName (ReprDecl d)
      | d.name == name = Just (rName, d.target)
      | otherwise = Nothing
    findReprData rName (ReprData d)
      | d.name == name = Just (rName, lams d.binds d.target)
      | otherwise = join $ find isJust $ map (findReprDataCtor rName) d.ctors

    findReprDataCtor :: String -> ReprDataCtorItem -> Maybe (String, Term)
    findReprDataCtor rName c
      | c.name == name = Just (rName, lams c.binds c.target)
      | otherwise = Nothing

-- | Find a representation for the case expression of the given global type name.
findReprForCase :: String -> Tc (Maybe (String, Term))
findReprForCase tyName = do
  (Signature items) <- gets sig
  return $ join $ find isJust $ map findRepr items
  where
    findRepr (Repr (ReprItem rName contents)) = join $ find isJust $ map (findReprData rName) contents
    findRepr _ = Nothing

    findReprData rName (ReprData d)
      | d.name == tyName =
          case d.cse of
            Just reprCase ->
              let (subjectBind, ctors) = reprCase.binds
               in Just (rName, lams (subjectBind : map snd ctors) reprCase.target)
            Nothing -> Nothing
    findReprData _ _ = Nothing

-- | Get the data item for a given name in a signature.
--
-- Assumes that the data item is already present.
getDataItem :: String -> Signature -> DataItem
getDataItem name s =
  case lookupItemOrCtor name s of
    Just (Left (Data d)) -> d
    _ -> error $ "Data item " ++ name ++ " not found in signature"
