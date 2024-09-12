{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Typechecking
  ( Tc (..),
    TcError (..),
    Ctx (..),
    emptyCtx,
    Mode (..),
    InPat (..),
    Problem,
    Goal,
    SolveAttempts (..),
    prettyGoal,
    lam,
    letIn,
    app,
    univ,
    piTy,
    name,
    insertLam,
    repr,
    meta,
    wildPat,
    caseOf,
    checkByInfer,
    lit,
    defItem,
    dataItem,
    ctorItem,
    primItem,
    closeValHere,
    endDataItem,
    reprDataItem,
    reprCtorItem,
    reprCaseItem,
    reprDefItem,
    ensureAllProblemsSolved,
  )
where

import Algebra.Lattice (Lattice (..), (/\))
import Common
  ( Arg (Arg, mode),
    Clause,
    CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (DefGlobal),
    Glob (CtorGlob, DataGlob, DefGlob, PrimGlob),
    Has (..),
    HasNameSupply (uniqueName),
    HasProjectFiles,
    Idx (..),
    Lit (..),
    Loc,
    Lvl (..),
    MetaVar,
    Name (Name),
    Param (..),
    PiMode (..),
    PrimGlobal (..),
    Spine,
    Tag,
    Tel,
    Times (Finite),
    inv,
    lvlToIdx,
    nextLvl,
    nextLvls,
    pattern Impossible,
    pattern Possible,
  )
import Control.Applicative (Alternative (empty))
import Control.Monad (replicateM, unless)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Extra (when)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Foldable (Foldable (..), toList)
import qualified Data.IntMap as IM
import Data.List (intercalate, zipWith4)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..), (><))
import qualified Data.Sequence as S
import Data.Set (Set)
import Debug.Trace (traceM)
import Evaluation
  ( Eval (..),
    close,
    ensureIsCtor,
    eval,
    evalInOwnCtx,
    evalPat,
    force,
    ifIsData,
    isCtorTy,
    isTypeFamily,
    quote,
    quotePat,
    resolve,
    unfoldDefs,
    vApp,
    vAppNeu,
    vRepr,
    ($$),
  )
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    KnownGlobal (..),
    PrimGlobalInfo (..),
    Sig,
    addCaseRepr,
    addCtorRepr,
    addDataRepr,
    addDefRepr,
    addItem,
    getCtorGlobal,
    getDataGlobal,
    getDefGlobal,
    hasName,
    knownData,
    lookupGlobal,
    modifyDataItem,
    modifyDefItem,
    unfoldDef,
  )
import Literals (unfoldLit)
import Meta (freshMetaVar, solveMetaVar)
import Printing (Pretty (..), indentedFst)
import Syntax (BoundState (Bound, Defined), Bounds, SPat (..), STm (..), STy, sAppSpine, sGatherApps, sGatherPis, sPis, uniqueSLams)
import Value
  ( Closure (body, numVars),
    Env,
    PRen (..),
    Sub,
    VHead (VFlex, VGlobal, VRigid),
    VNeu (VApp, VCaseApp, VReprApp),
    VPatB (..),
    VTm (..),
    VTy,
    isEmptySub,
    liftPRenN,
    vGetSpine,
    pattern VGlob,
    pattern VRepr,
    pattern VVar,
  )

data TcError
  = Mismatch [UnifyError]
  | PotentialMismatch VTm VTm
  | UnresolvedVariable Name
  | ImplicitMismatch PiMode PiMode
  | InvalidPattern
  | RemainingProblems [Problem]
  | ImpossibleCaseIsPossible VTm VTm
  | ImpossibleCaseMightBePossible VTm VTm Sub
  | ImpossibleCase VTm [UnifyError]
  | InvalidCaseSubject STm VTy
  | InvalidDataFamily VTy
  | InvalidCtorType STy
  | ExpectedCtor VPatB CtorGlobal
  | UnexpectedPattern VPatB
  | MissingCtor CtorGlobal
  | DuplicateItem Name
  | ImpossibleCasesNotSupported
  | Chain [TcError]

data InPat = NotInPat | InPossiblePat [Name] | InImpossiblePat deriving (Eq)

instance (HasProjectFiles m, Tc m) => Pretty m TcError where
  pretty e = do
    loc <- (view :: m Loc) >>= pretty
    err' <- err
    return $ loc <> "\n" <> err'
    where
      err = case e of
        Mismatch us -> do
          us' <- mapM pretty us
          return $ intercalate "\n" us'
        PotentialMismatch t1 t2 -> do
          t1' <- pretty t1
          t2' <- pretty t2
          return $ "Potential mismatch: " <> t1' <> " and " <> t2'
        UnresolvedVariable n -> do
          n' <- pretty n
          return $ "Unresolved variable: " <> n'
        ImplicitMismatch m1 m2 -> do
          return $ "Implicit mismatch: " <> show m1 <> " and " <> show m2
        InvalidPattern -> do
          return "Invalid in pattern position"
        ImpossibleCaseIsPossible t1 t2 -> do
          t1' <- pretty t1
          t2' <- pretty t2
          return $ "Impossible case is possible: " <> t1' <> " = " <> t2'
        ImpossibleCaseMightBePossible t1 t2 s -> do
          t1' <- pretty t1
          t2' <- pretty t2
          s' <-
            if isEmptySub s
              then return ""
              else do
                s' <- pretty s
                return $ "\nThis could happen if " ++ s'
          return $ "Impossible case might be possible: " <> t1' <> " =? " <> t2' <> s'
        ImpossibleCase p t -> do
          p' <- pretty p
          t' <- intercalate "\n" <$> mapM pretty t
          return $ "Impossible case: " <> p' <> "\n" <> indentedFst t'
        InvalidCaseSubject t ty -> do
          t' <- pretty t
          ty' <- pretty ty
          return $ "Invalid case subject: " <> t' <> " : " <> ty'
        InvalidDataFamily t -> do
          t' <- pretty t
          return $ "Invalid data family type: " <> t'
        InvalidCtorType t -> do
          t' <- pretty t
          return $ "Invalid constructor type: " <> t'
        DuplicateItem n -> do
          n' <- pretty n
          return $ "Duplicate item: " <> n'
        ExpectedCtor t c -> do
          t' <- pretty t
          return $ "Expected constructor " <> show c.globalName <> " but got " <> t'
        UnexpectedPattern c -> do
          c' <- pretty c
          return $ "Unexpected pattern: " <> c'
        MissingCtor c -> do
          return $ "Missing constructor: " <> show c.globalName
        ImpossibleCasesNotSupported -> do
          return "Impossible cases are currently not supported"
        RemainingProblems ps -> do
          ps' <-
            mapM
              ( \p -> enterProblem p $ do
                  l' <- pretty p.loc
                  c' <- intercalate "\n" <$> mapM pretty (toList p.errs)
                  return $ l' ++ "\n" ++ c'
              )
              ps
          return $ "Cannot solve some metavariables:\n" ++ indentedFst (intercalate "\n" ps')
        Chain es -> do
          es' <- mapM pretty es
          return $ unlines es'

instance Show InPat where
  show NotInPat = "not in pat"
  show (InPossiblePat ns) = "in possible pat with " ++ show ns
  show InImpossiblePat = "in impossible pat"

class (Eval m, Has m Loc, Has m (Seq Problem), Has m InPat, Has m Ctx, Has m SolveAttempts) => Tc m where
  addGoal :: Goal -> m ()

  getCtx :: m Ctx
  getCtx = view

  setCtx :: Ctx -> m ()
  setCtx = modify . const

  modifyCtx :: (Ctx -> Ctx) -> m ()
  modifyCtx = modify

  accessCtx :: (Ctx -> a) -> m a
  accessCtx f = f <$> getCtx

  enterCtx :: (Ctx -> Ctx) -> m a -> m a
  enterCtx = enter

  tcError :: TcError -> m a
  showMessage :: String -> m ()

  inPat :: m InPat
  inPat = view

  enterLoc :: Loc -> m a -> m a
  enterLoc = enter . const

  enterPat :: InPat -> m a -> m a
  enterPat = enter . const

  setInPat :: InPat -> m ()
  setInPat = modify . const

  whenInPat :: (InPat -> m a) -> m a
  whenInPat f = do
    p <- inPat
    f p

  ifInPat :: m a -> m a -> m a
  ifInPat a b = whenInPat $ \case
    NotInPat -> b
    _ -> a

data CtxTy = CtxTy VTy | TyUnneeded deriving (Show)

data Ctx = Ctx
  { env :: Env VTm,
    lvl :: Lvl,
    types :: [CtxTy],
    bounds :: Bounds,
    nameList :: [Name],
    names :: Map Name Lvl
  }
  deriving (Show)

data Mode = Check VTy | Infer

type Child m = (Mode -> m (STm, VTy))

instance (Tc m) => Has m (Env VTm) where
  view = accessCtx (\c -> c.env)
  modify f = modifyCtx (\c -> c {env = f c.env})

instance (Tc m) => Has m [Name] where
  view = accessCtx (\c -> c.nameList)
  modify f = modifyCtx (\c -> c {nameList = f c.nameList})

instance (Tc m) => Has m Lvl where
  view = accessCtx (\c -> c.lvl)
  modify f = modifyCtx (\c -> c {lvl = f c.lvl})

instance (Monad m, Pretty m VTm) => Pretty m CtxTy where
  pretty (CtxTy t) = pretty t
  pretty TyUnneeded = return "_"

instance (Eval m, Has m [Name]) => Pretty m Ctx where
  pretty c =
    intercalate "\n"
      <$> mapM
        ( \(n, ty, tm) -> do
            n' <- pretty n
            ty' <- pretty ty
            tm' <- case tm of
              Just t -> (" = " ++) <$> pretty t
              Nothing -> return ""
            return $ n' ++ " : " ++ ty' ++ tm'
        )
        (reverse con)
    where
      con :: [(Name, CtxTy, Maybe VTm)]
      con =
        zipWith4
          ( \i n t e ->
              ( n,
                t,
                case e of
                  VNeu (VVar x) | x == Lvl i -> Nothing
                  _ -> Just e
              )
          )
          [c.lvl.unLvl - 1, c.lvl.unLvl - 2 .. 0]
          c.nameList
          c.types
          c.env

emptyCtx :: Ctx
emptyCtx =
  Ctx
    { env = [],
      lvl = Lvl 0,
      types = [],
      bounds = [],
      nameList = [],
      names = M.empty
    }

ensureAllProblemsSolved :: (Tc m) => m ()
ensureAllProblemsSolved = do
  solveRemainingProblems
  ps <- view
  if S.null ps
    then return ()
    else tcError $ RemainingProblems (toList ps)

uniqueNames :: (Tc m) => Int -> m [Name]
uniqueNames n = replicateM n uniqueName

data CtxEntry = CtxEntry
  { name :: Name,
    ty :: CtxTy,
    tm :: VTm,
    lvl :: Lvl,
    bound :: BoundState
  }

bind :: Name -> VTy -> Ctx -> Ctx
bind x ty ctx =
  addCtxEntry
    ( CtxEntry
        { name = x,
          ty = CtxTy ty,
          tm = VNeu (VVar ctx.lvl),
          lvl = ctx.lvl,
          bound = Bound
        }
    )
    ctx

enterTel :: (Tc m) => Tel STy -> m a -> m a
enterTel Empty f = f
enterTel (t :<| ts) f = do
  t' <- evalHere t.ty
  enterCtx (bind t.name t') (enterTel ts f)

insertedBind :: Name -> VTy -> Ctx -> Ctx
insertedBind = bind

define :: Name -> VTm -> VTy -> Ctx -> Ctx
define x t ty ctx =
  addCtxEntry
    ( CtxEntry
        { tm = t,
          ty = CtxTy ty,
          bound = Defined,
          lvl = ctx.lvl,
          name = x
        }
    )
    ctx

typelessBind :: Name -> Ctx -> Ctx
typelessBind x ctx =
  addCtxEntry
    ( CtxEntry
        { tm = VNeu (VVar ctx.lvl),
          ty = TyUnneeded,
          lvl = ctx.lvl,
          bound = Bound,
          name = x
        }
    )
    ctx

addCtxEntry :: CtxEntry -> Ctx -> Ctx
addCtxEntry e ctx =
  ctx
    { env = e.tm : ctx.env,
      lvl = nextLvl e.lvl,
      types = e.ty : ctx.types,
      bounds = e.bound : ctx.bounds,
      names = M.insert e.name e.lvl ctx.names,
      nameList = e.name : ctx.nameList
    }

typelessBinds :: [Name] -> Ctx -> Ctx
typelessBinds ns ctx = foldr typelessBind ctx (reverse ns)

ensureNeeded :: CtxTy -> VTm
ensureNeeded (CtxTy t) = t
ensureNeeded TyUnneeded = error "Type is unneeded"

lookupName :: Name -> Ctx -> Maybe (Idx, VTy)
lookupName n ctx = case M.lookup n ctx.names of
  Just l -> let idx = lvlToIdx ctx.lvl l in Just (idx, ensureNeeded (ctx.types !! idx.unIdx))
  Nothing -> Nothing

inferMeta :: (Tc m) => Maybe Name -> m (STm, VTy)
inferMeta n = do
  ty <- newMeta Nothing
  vty <- evalHere ty
  checkMeta n vty

data Goal = Goal
  { ctx :: Ctx,
    tm :: STm,
    ty :: VTy
  }

prettyGoal :: (Tc m) => Goal -> m String
prettyGoal (Goal c n ty) = enterCtx (const c) $ do
  c' <- getCtx >>= pretty
  n' <- pretty n
  ty' <- pretty ty
  let g = n' ++ " : " ++ ty'
  return $ indentedFst c' ++ "\n" ++ replicate (length g + 4) '―' ++ "\n" ++ indentedFst g ++ "\n"

checkMeta :: (Tc m) => Maybe Name -> VTy -> m (STm, VTy)
checkMeta n ty = do
  m <- newMeta n
  c <- getCtx
  case n of
    Just _ -> addGoal (Goal c m ty)
    Nothing -> return ()
  return (m, ty)

newMeta :: (Tc m) => Maybe Name -> m STm
newMeta n = do
  bs <- accessCtx (\c -> c.bounds)
  m <- freshMetaVar n
  return (SMeta m bs)

freshMeta :: (Tc m) => m STm
freshMeta = newMeta Nothing

freshMetaOrPatBind :: (Tc m) => m (STm, VTm)
freshMetaOrPatBind =
  ifInPat
    ( do
        n <- uniqueName
        (n', _) <- inferPatBind n
        vn <- evalPatHere (SPat n' [n])
        return (n', vn.vPat)
    )
    ( do
        n' <- freshMeta
        vn <- evalHere n'
        return (n', vn)
    )

insertFull :: (Tc m) => (STm, VTy) -> m (STm, VTy)
insertFull (tm, ty) = do
  f <- force ty
  case f of
    VPi Implicit _ _ b -> do
      (a, va) <- freshMetaOrPatBind
      ty' <- b $$ [va]
      insertFull (SApp Implicit tm a, ty')
    _ -> return (tm, ty)

insert :: (Tc m) => (STm, VTy) -> m (STm, VTy)
insert (tm, ty) = case tm of
  SLam Implicit _ _ -> return (tm, ty)
  _ -> insertFull (tm, ty)

evalHere :: (Tc m) => STm -> m VTm
evalHere t = do
  e <- accessCtx (\c -> c.env)
  eval e t

evalPatHere :: (Tc m) => SPat -> m VPatB
evalPatHere t = do
  e <- accessCtx (\c -> c.env)
  evalPat e t

handleUnification :: (Tc m) => VTm -> VTm -> CanUnify -> m ()
handleUnification t1 t2 r = do
  p <- inPat
  case p of
    InImpossiblePat -> case r of
      Yes -> tcError $ ImpossibleCaseIsPossible t1 t2
      Maybe -> addNewProblem t1 t2 Blocking --  tcError $ ImpossibleCaseMightBePossible t1 t2 s
      No _ -> return ()
    InPossiblePat _ -> case r of
      Yes -> return ()
      Maybe -> addNewProblem t1 t2 Blocking -- applySubToCtx s
      No errs -> tcError $ ImpossibleCase t1 errs
    NotInPat -> case r of
      Yes -> return ()
      Maybe -> addNewProblem t1 t2 Blocking
      No errs -> tcError $ Mismatch errs

canUnifyHere :: (Tc m) => VTm -> VTm -> m CanUnify
canUnifyHere t1 t2 = do
  -- l <- accessCtx (\c -> c.lvl)
  t1' <- resolveHere t1
  t2' <- resolveHere t2
  unify t1' t2'

resolveHere :: (Tc m) => VTm -> m VTm
resolveHere t = do
  e <- accessCtx (\c -> c.env)
  resolve e t

unifyHere :: (Tc m) => VTm -> VTm -> m ()
unifyHere t1 t2 = do
  canUnifyHere t1 t2 >>= handleUnification t1 t2

closeValHere :: (Tc m) => Int -> VTm -> m Closure
closeValHere n t = do
  (l, e) <- accessCtx (\c -> (c.lvl, c.env))
  t' <- quote (nextLvls l n) t
  close n e t'

closeHere :: (Tc m) => Int -> STm -> m Closure
closeHere n t = do
  e <- accessCtx (\c -> c.env)
  close n e t

ifForcePiType ::
  (Tc m) =>
  PiMode ->
  VTy ->
  (PiMode -> Name -> VTy -> Closure -> m a) ->
  (PiMode -> Name -> VTy -> Closure -> m a) ->
  m a
ifForcePiType m ty the els = do
  ty' <- force ty >>= unfoldDefs
  case ty' of
    VPi m' x a b -> do
      if m == m'
        then the m' x a b
        else els m' x a b
    _ -> do
      a <- freshMeta >>= evalHere
      x <- uniqueName
      b <- enterCtx (bind x a) freshMeta >>= closeHere 1
      unifyHere ty (VPi m x a b)
      the m x a b

forbidPat :: (Tc m) => m ()
forbidPat = ifInPat (tcError InvalidPattern) (return ())

inferPatBind :: (Tc m) => Name -> m (STm, VTy)
inferPatBind x = do
  ty <- freshMeta >>= evalHere
  checkPatBind x ty

checkPatBind :: (Tc m) => Name -> VTy -> m (STm, VTy)
checkPatBind x ty = do
  modifyCtx (bind x ty)
  whenInPat
    ( \case
        InPossiblePat ns -> setInPat (InPossiblePat (ns ++ [x]))
        _ -> return ()
    )
  return (SVar (Idx 0), ty)

reprHere :: (Tc m) => Times -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

name :: (Tc m) => Name -> m (STm, VTy)
name n =
  ifInPat
    ( do
        l <- access (lookupGlobal n)
        case l of
          Just c@(CtorInfo _) -> globalInfoToTm n c
          _ -> inferPatBind n
    )
    ( do
        r <- accessCtx (lookupName n)
        case r of
          Just (i, t) -> return (SVar i, t)
          Nothing -> do
            l <- access (lookupGlobal n)
            case l of
              Just x -> globalInfoToTm n x
              Nothing -> tcError $ UnresolvedVariable n
    )

ensureNewName :: (Tc m) => Name -> m ()
ensureNewName n = do
  r <- access (hasName n)
  when r $ tcError $ DuplicateItem n

getLvl :: (Tc m) => m Lvl
getLvl = accessCtx (\c -> c.lvl)

inPatNames :: InPat -> [Name]
inPatNames (InPossiblePat ns) = ns
inPatNames _ = []

evalInOwnCtxHere :: (Tc m) => Closure -> m VTm
evalInOwnCtxHere t = do
  l <- accessCtx (\c -> c.lvl)
  evalInOwnCtx l t

lam :: (Tc m) => Mode -> PiMode -> Name -> Child m -> m (STm, VTy)
lam mode m x t = do
  forbidPat
  case mode of
    Check ty ->
      ifForcePiType
        m
        ty
        ( \_ x' a b -> do
            vb <- evalInOwnCtxHere b
            (t', _) <- enterCtx (bind x a) (t (Check vb))
            return (SLam m x t', VPi m x' a b)
        )
        ( \m' x' a b -> case m' of
            Implicit -> insertLam x' a b (\s -> lam s m x t)
            _ -> tcError $ ImplicitMismatch m m'
        )
    Infer -> do
      a <- freshMeta >>= evalHere
      (t', b) <- enterCtx (bind x a) $ t Infer >>= insert
      b' <- closeValHere 1 b
      return (SLam m x t', VPi m x a b')

insertLam :: (Tc m) => Name -> VTy -> Closure -> Child m -> m (STm, VTy)
insertLam x' a b t = do
  vb <- evalInOwnCtxHere b
  (t', _) <- enterCtx (insertedBind x' a) (t (Check vb))
  return (SLam Implicit x' t', VPi Implicit x' a b)

letIn :: (Tc m) => Mode -> Name -> Child m -> Child m -> Child m -> m (STm, VTy)
letIn mode x a t u = do
  forbidPat
  (a', _) <- a (Check VU)
  va <- evalHere a'
  (t', _) <- t (Check va)
  vt <- evalHere t'
  (u', ty) <- enterCtx (define x vt va) $ u mode
  return (SLet x a' t' u', ty)

spine :: (Tc m) => (STm, VTy) -> Spine (Child m) -> m (STm, VTy)
spine (t, ty) Empty = return (t, ty)
spine (t, ty) (Arg m u :<| sp) = do
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Explicit -> insertFull (t, ty)
    Instance -> error "unimplemented"
  ifForcePiType
    m
    ty'
    ( \_ _ a b -> do
        (u', _) <- u (Check a)
        uv <- evalHere u'
        b' <- b $$ [uv]
        spine (SApp m t' u', b') sp
    )
    (\m' _ _ _ -> tcError $ ImplicitMismatch m m')

app :: (Tc m) => Child m -> Spine (Child m) -> m (STm, VTy)
app s sp = do
  (s', sTy) <- s Infer
  spine (s', sTy) sp

univ :: (Tc m) => m (STm, VTy)
univ = do
  forbidPat
  return (SU, VU)

piTy :: (Tc m) => PiMode -> Name -> Child m -> Child m -> m (STm, VTy)
piTy m x a b = do
  forbidPat
  (a', _) <- a (Check VU)
  av <- evalHere a'
  (b', _) <- enterCtx (bind x av) $ b (Check VU)
  return (SPi m x a' b', VU)

repr :: (Tc m) => Mode -> Times -> Child m -> m (STm, VTy)
repr mode m t = do
  forbidPat
  case mode of
    Check ty@(VNeu (VRepr m' t')) | m == m' -> do
      (tc, _) <- t (Check (VNeu t'))
      return (SRepr m tc, ty)
    Check ty | m < mempty -> do
      (t', ty') <- t Infer >>= insert
      reprTy <- reprHere (inv m) ty
      unifyHere reprTy ty'
      return (SRepr m t', ty)
    Check ty -> checkByInfer (repr Infer m t) ty
    Infer -> do
      (t', ty) <- t Infer
      reprTy <- reprHere m ty
      return (SRepr m t', reprTy)

checkByInfer :: (Tc m) => m (STm, VTy) -> VTy -> m (STm, VTy)
checkByInfer t ty = do
  (t', ty') <- t >>= insert
  unifyHere ty ty'
  return (t', ty)

pat :: (Tc m) => InPat -> Child m -> (SPat -> VTy -> m ()) -> (SPat -> VTy -> m a) -> m a
pat inPt pt runInsidePatScope runOutsidePatScope = enterCtx id $ do
  (p', t, ns) <- enterPat inPt $ do
    (p', t') <- pt Infer >>= insert
    ns <- inPatNames <$> inPat
    runInsidePatScope (SPat p' ns) t'
    return (p', t', ns)
  runOutsidePatScope (SPat p' ns) t

constLamsForPis :: (Tc m) => VTy -> VTm -> m STm
constLamsForPis pis val = do
  spis <- quoteHere pis
  let (args, _) = sGatherPis spis
  sval <- closeValHere (length args) val
  uniqueSLams (toList $ fmap (\p -> p.mode) args) sval.body

mzip :: (Alternative m) => [m a] -> [m b] -> [(m a, m b)]
mzip (a : as) (b : bs) = (a, b) : mzip as bs
mzip [] (b : bs) = (empty, b) : mzip [] bs
mzip (a : as) [] = (a, empty) : mzip as []
mzip _ _ = []

caseClauses :: (Tc m) => DataGlobalInfo -> [Clause (Child m) (Child m)] -> (VPatB -> SPat -> VTy -> Child m -> m a) -> m [a]
caseClauses di cs f = do
  mapM
    ( \case
        (_, Just (Impossible _)) -> tcError ImpossibleCasesNotSupported
        (c, Just (Possible p t)) -> do
          pat (InPossiblePat []) p (const . const $ return ()) $ \sp pTy -> do
            vp <- evalPatHere sp
            case c of
              Just c' -> do
                ensureIsCtor vp.vPat c' (tcError $ ExpectedCtor vp c')
                f vp sp pTy t
              Nothing -> do
                tcError $ UnexpectedPattern vp
        (Just c, Nothing) -> tcError $ MissingCtor c
        (Nothing, Nothing) -> error "impossible"
    )
    (mzip (map Just di.ctors) (map Just cs))

caseOf :: (Tc m) => Mode -> Child m -> Maybe (Child m) -> [Clause (Child m) (Child m)] -> m (STm, VTy)
caseOf mode s r cs = do
  forbidPat
  case mode of
    Infer -> do
      retTy <- freshMeta >>= evalHere
      caseOf (Check retTy) s r cs
    Check ty -> do
      (ss, ssTy) <- s Infer
      d <- ifIsData ssTy return (tcError $ InvalidCaseSubject ss ssTy)
      di <- access (getDataGlobal d)
      let motive = fromJust di.motiveTy
      freshArgsForParams <- replicateM (length di.params) (freshMeta >>= evalHere)
      motiveApplied <- motive $$ freshArgsForParams
      rr <- case r of
        Just r' -> fst <$> r' (Check motiveApplied)
        Nothing -> constLamsForPis motiveApplied ty
      vrr <- evalHere rr
      scs <- caseClauses di cs $ \vp sp pTy t -> do
        let pTySp = vGetSpine pTy
        branchTy <- vApp vrr (pTySp S.:|> Arg Explicit vp.vPat)
        (st, _) <- t (Check branchTy)
        return $ Possible sp st
      return (SCase d ss rr scs, ty)

wildPat :: (Tc m) => Mode -> m (STm, VTy)
wildPat mode = do
  n <- uniqueName
  case mode of
    Infer -> inferPatBind n
    (Check ty) -> checkPatBind n ty

meta :: (Tc m) => Mode -> Maybe Name -> m (STm, VTy)
meta mode n = do
  forbidPat
  case mode of
    Infer -> inferMeta n
    Check ty -> checkMeta n ty

lit :: (Tc m) => Mode -> Lit (Child m) -> m (STm, VTy)
lit mode l = case mode of
  Check ty -> checkByInfer (lit Infer l) ty
  Infer -> do
    (l', ty, args) <- case l of
      StringLit s -> return (StringLit s, KnownString, Empty)
      CharLit c -> return (CharLit c, KnownChar, Empty)
      NatLit n -> return (NatLit n, KnownNat, Empty)
      FinLit f bound -> do
        (bound', _) <- bound (Check (VGlob (DataGlob (knownData KnownNat)) Empty))
        vbound' <- evalHere bound'
        return (FinLit f bound', KnownFin, S.singleton (Arg Explicit vbound'))
    return (SLit l', VGlob (DataGlob (knownData ty)) args)

defItem :: (Tc m) => Name -> Set Tag -> Child m -> Child m -> m ()
defItem n ts ty tm = do
  ensureNewName n
  (ty', _) <- ty (Check VU)
  vty <- evalHere ty'
  modify (addItem n (DefInfo (DefGlobalInfo vty Nothing Nothing)) ts)
  (tm', _) <- tm (Check vty)
  vtm <- evalHere tm'
  b <- normaliseProgram
  stm <- if b then quote (Lvl 0) vtm else return tm'
  modify (modifyDefItem (DefGlobal n) (\d -> d {tm = Just stm, vtm = Just vtm}))
  return ()

tel :: (Tc m) => Tel (Child m) -> m (Tel STy)
tel Empty = return Empty
tel (t :<| ts) = do
  (t', _) <- t.ty (Check VU)
  vt <- evalHere t'
  ts' <- enterCtx (bind t.name vt) $ tel ts
  return (Param t.mode t.name t' :<| ts')

dataItem :: (Tc m) => Name -> Set Tag -> Tel (Child m) -> Child m -> m ()
dataItem n ts te ty = do
  ensureNewName n
  te' <- tel te
  pretty te' >>= traceM
  ty' <- enterTel te' $ do
    (ty', _) <- ty (Check VU)
    vty <- evalHere ty'
    i <- getLvl >>= (`isTypeFamily` vty)
    unless i (tcError $ InvalidDataFamily vty)
    return ty'
  cty <- closeHere (length te') ty'
  modify (addItem n (DataInfo (DataGlobalInfo te' cty [] Nothing Nothing [])) ts)

endDataItem :: (Tc m) => DataGlobal -> m ()
endDataItem dat = do
  (motiveTy, elimTy, arity) <- buildElimTy dat
  modify
    ( modifyDataItem
        dat
        ( \d ->
            d
              { elimTy = Just elimTy,
                motiveTy = Just motiveTy,
                elimTyArity = arity
              }
        )
    )
  elimTy' <- pretty elimTy
  traceM $ "Eliminator type is " ++ elimTy'

ctorItem :: (Tc m) => DataGlobal -> Name -> Set Tag -> Child m -> m ()
ctorItem dat n ts ty = do
  di <- access (getDataGlobal dat)
  idx <- access (\s -> length (getDataGlobal dat s).ctors)
  ty' <- enterTel di.params $ do
    ensureNewName n
    (ty', _) <- ty (Check VU)
    pretty ty' >>= traceM
    vty <- evalHere ty'
    i <- getLvl >>= (\l -> isCtorTy l dat vty)
    unless i (tcError $ InvalidCtorType ty')
    return ty'
  cty <- closeHere (length di.params) ty'
  modify (addItem n (CtorInfo (CtorGlobalInfo cty idx dat)) ts)
  modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal n]}))

primItem :: (Tc m) => Name -> Set Tag -> Child m -> m ()
primItem n ts ty = do
  ensureNewName n
  (ty', _) <- ty (Check VU)
  vty <- evalHere ty'
  modify (addItem n (PrimInfo (PrimGlobalInfo vty)) ts)

vReprHere :: (Tc m) => Times -> VTm -> m VTm
vReprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

reprItem :: (Tc m) => m VTy -> (VTy -> Set Tag -> Sig -> Sig) -> Set Tag -> Child m -> m ()
reprItem getGlob addGlob ts r = do
  ty <- getGlob
  ty' <- vReprHere (Finite 1) ty
  (r', _) <- r (Check ty')
  vr <- evalHere r'
  modify (addGlob vr ts)

reprDataItem :: (Tc m) => DataGlobal -> Set Tag -> Child m -> m ()
reprDataItem dat = reprItem (access (getDataGlobal dat) >>= \d -> snd <$> globalInfoToTm dat.globalName (DataInfo d)) (addDataRepr dat)

reprCtorItem :: (Tc m) => CtorGlobal -> Set Tag -> Child m -> m ()
reprCtorItem ctor = reprItem (access (getCtorGlobal ctor) >>= \d -> snd <$> globalInfoToTm ctor.globalName (CtorInfo d)) (addCtorRepr ctor)

reprDefItem :: (Tc m) => DefGlobal -> Set Tag -> Child m -> m ()
reprDefItem def = reprItem (access (getDefGlobal def) >>= \d -> return d.ty) (addDefRepr def)

reprCaseItem :: (Tc m) => DataGlobal -> Set Tag -> Child m -> m ()
reprCaseItem dat ts c = do
  elimTy <- access (getDataGlobal dat) >>= \d -> return $ fromJust d.elimTy
  reprItem (return elimTy) (addCaseRepr dat) ts c

quoteHere :: (Tc m) => VTm -> m STm
quoteHere t = do
  l <- accessCtx (\c -> c.lvl)
  quote l t

spineForTel :: Int -> Tel STm -> Spine STm
spineForTel dist te =
  S.fromList $ zipWith (curry (\(Param m _ _, i) -> Arg m (SVar (Idx (dist + length te - i - 1))))) (toList te) [0 ..]

telWithNames :: (Tc m) => Tel a -> m (Tel a)
telWithNames = do
  mapM
    ( \(Param m n a) -> do
        case n of
          Name "_" -> do
            n' <- uniqueName
            return (Param m n' a)
          Name _ -> return (Param m n a)
    )

buildElimTy :: (Tc m) => DataGlobal -> m (Closure, VTy, [Arg ()])
buildElimTy dat = do
  datInfo <- access (getDataGlobal dat)

  let sTyParams = datInfo.params

  let sTy = datInfo.ty.body
  let (sTyIndices, _) = sGatherPis sTy
  sTyIndicesBinds <- telWithNames sTyIndices
  let spToData i = sAppSpine (SGlobal (DataGlob dat)) (spineForTel i sTyParams >< spineForTel i sTyIndicesBinds)

  let distFromMotiveToMethod i = i + length sTyIndicesBinds + 1
  let subjSpToData = spToData 0
  let distFromTyBindsToRet = length datInfo.ctors + 1
  let retSp = spineForTel distFromTyBindsToRet sTyIndicesBinds

  motiveSubjName <- uniqueName
  elimTyName <- uniqueName
  subjectTyName <- uniqueName

  let motiveTy = sPis (sTyIndicesBinds :|> Param Explicit motiveSubjName subjSpToData) SU
  methodTys <- mapM ctorMethodTy datInfo.ctors

  let elimTy =
        sPis
          ( ( ( (sTyParams :|> Param Explicit elimTyName motiveTy)
                  >< sTyIndicesBinds
              )
                :|> Param Explicit subjectTyName subjSpToData
            )
              >< S.fromList
                ( zipWith
                    ( \i (methodTy, methodName) ->
                        Param Explicit methodName (methodTy (distFromMotiveToMethod i))
                    )
                    [0 ..]
                    methodTys
                )
          )
          (sAppSpine (SVar (Idx (distFromMotiveToMethod (length methodTys)))) (retSp S.|> Arg Explicit (SVar (Idx (length methodTys)))))

  elimTy' <- evalHere elimTy
  motiveTy' <- closeHere (length datInfo.params) motiveTy
  return (motiveTy', elimTy', map (\p -> Arg p.mode ()) (toList sTyIndicesBinds))
  where
    ctorMethodTy :: (Tc m) => CtorGlobal -> m (Int -> STy, Name)
    ctorMethodTy ctor = do
      ctorInfo <- access (getCtorGlobal ctor)
      let sTy = ctorInfo.ty.body
      let (sTyBinds', sTyRet) = sGatherPis sTy
      sTyBinds <- telWithNames sTyBinds'
      let (_, sTyRetSp) = sGatherApps sTyRet
      let spToCtor = sAppSpine (SGlobal (CtorGlob ctor)) (spineForTel 0 sTyBinds)
      n <- uniqueName
      return . (,n) $ \sMotiveIdx ->
        let methodRetTy =
              sAppSpine
                (SVar (Idx (sMotiveIdx + length sTyBinds)))
                (sTyRetSp S.|> Arg Explicit spToCtor)
         in sPis sTyBinds methodRetTy

globalInfoToTm :: (Tc m) => Name -> GlobalInfo -> m (STm, VTy)
globalInfoToTm n i = case i of
  DefInfo d -> return (SGlobal (DefGlob (DefGlobal n)), d.ty)
  DataInfo d -> do
    ty' <- evalHere $ sPis d.params d.ty.body
    return (SGlobal (DataGlob (DataGlobal n)), ty')
  CtorInfo c -> do
    di <- access (getDataGlobal c.dataGlobal)
    metas <- replicateM (length di.params) (freshMeta >>= evalHere)
    ty' <- c.ty $$ metas
    return (SGlobal (CtorGlob (CtorGlobal n)), ty')
  PrimInfo p -> return (SGlobal (PrimGlob (PrimGlobal n)), p.ty)

data UnifyError
  = DifferentSpineLengths (Spine VTm) (Spine VTm)
  | DifferentClauses [Clause VPatB Closure] [Clause VPatB Closure]
  | Mismatching VTm VTm
  | SolveError SolveError
  | ErrorInCtx [Name] UnifyError
  deriving (Show)

data SolveError
  = InvertError (Spine VTm)
  | OccursError MetaVar
  | EscapingVariable
  | Blocking
  | WithProblem Problem SolveError
  deriving (Show)

data CanUnify = Yes | No [UnifyError] | Maybe deriving (Show)

instance (Tc m) => Pretty m CanUnify where
  pretty Yes = return "can unify"
  pretty (No xs) = do
    xs' <- intercalate ", " <$> mapM pretty xs
    return $ "cannot unify: " ++ xs'
  pretty Maybe = do
    return "unclear"

instance (Tc m) => Pretty m SolveError where
  pretty (InvertError s) = do
    s' <- pretty s
    return $ "the arguments " ++ s' ++ " contain non-variables"
  pretty (OccursError m) = do
    m' <- pretty (SMeta m [])
    return $ "the meta-variable " ++ m' ++ " occurs in a term it is being unified against"
  pretty EscapingVariable = do
    return "a variable in a term escapes the context of the meta it is being unified against"
  pretty Blocking = return "reduction is blocked"
  pretty (WithProblem p e) = do
    p' <- enterProblem p $ do
      lhs <- pretty p.lhs
      rhs <- pretty p.rhs
      return $ lhs ++ " =? " ++ rhs
    e' <- pretty e
    return $ p' ++ "\n" ++ e'

instance (Tc m) => Pretty m UnifyError where
  pretty (SolveError e) = pretty e
  pretty (DifferentSpineLengths s s') = do
    s'' <- pretty s
    s''' <- pretty s'
    return $ "the arguments " ++ s'' ++ " and " ++ s''' ++ " have different lengths"
  pretty (DifferentClauses cs cs') = do
    cs'' <- pretty cs
    cs''' <- pretty cs'
    return $ "the clauses " ++ cs'' ++ " and " ++ cs''' ++ " are different"
  pretty (Mismatching t t') = do
    t'' <- pretty t
    t''' <- pretty t'
    return $ "the terms " ++ t'' ++ " and " ++ t''' ++ " do not match"
  pretty (ErrorInCtx ns e) = enterCtx (const $ typelessBinds ns emptyCtx) $ pretty e

instance (Eval m) => Lattice (m CanUnify) where
  a \/ b = do
    a' <- a
    case a' of
      Yes -> a
      No _ -> b
      Maybe -> do
        b' <- b
        case b' of
          Yes -> return Yes
          No _ -> a
          Maybe -> return Maybe

  a /\ b = do
    a' <- a
    case a' of
      Yes -> b
      No xs -> do
        b' <- b
        case b' of
          Yes -> a
          No ys -> return $ No (xs ++ ys)
          Maybe -> return $ No xs
      Maybe -> do
        b' <- b
        case b' of
          Yes -> return Maybe
          No ys -> return $ No ys
          Maybe -> return Maybe

type SolveT = ExceptT SolveError

enterTypelessClosure :: (Tc m) => Closure -> m a -> m a
enterTypelessClosure c m = do
  ns <- uniqueNames c.numVars
  enterCtx (typelessBinds ns) m

enterTypelessPatBinds :: (Tc m) => VPatB -> m a -> m a
enterTypelessPatBinds p = enterCtx (typelessBinds p.binds)

invertSpine :: (Tc m) => Spine VTm -> SolveT m PRen
invertSpine Empty = do
  l <- lift getLvl
  return $ PRen (Lvl 0) l mempty
invertSpine s@(sp' :|> Arg _ t) = do
  (PRen dom cod ren) <- invertSpine sp'
  f <- lift $ force t
  case f of
    VNeu (VVar (Lvl l')) | IM.notMember l' ren -> return $ PRen (nextLvl dom) cod (IM.insert l' dom ren)
    _ -> throwError $ InvertError s

renameSp :: (Tc m) => MetaVar -> PRen -> STm -> Spine VTm -> SolveT m STm
renameSp _ _ t Empty = return t
renameSp m pren t (sp :|> Arg i u) = do
  xs <- renameSp m pren t sp
  ys <- rename m pren u
  return $ SApp i xs ys

renameClosure :: (Tc m) => MetaVar -> PRen -> Closure -> SolveT m STm
renameClosure m pren cl = do
  vt <- lift $ evalInOwnCtx pren.codSize cl
  rename m (liftPRenN cl.numVars pren) vt

renamePat :: (Tc m) => MetaVar -> PRen -> VPatB -> SolveT m SPat
renamePat _ pren p = do
  lift $ quotePat pren.codSize p

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: (Tc m) => MetaVar -> PRen -> VTm -> SolveT m STm
rename m pren tm = do
  f <- lift $ force tm
  case f of
    VNeu (VApp (VFlex m') sp)
      | m == m' -> throwError $ OccursError m
      | otherwise -> renameSp m pren (SMeta m' []) sp
    VNeu (VApp (VRigid (Lvl x)) sp) -> case IM.lookup x pren.vars of
      Nothing -> throwError EscapingVariable
      Just x' -> renameSp m pren (SVar (lvlToIdx pren.domSize x')) sp
    VNeu (VReprApp n h sp) -> do
      t' <- rename m pren (vAppNeu h sp)
      renameSp m pren (SRepr n t') sp
    VNeu (VCaseApp dat v r cs sp) -> do
      v' <- rename m pren (VNeu v)
      cs' <- mapM (bitraverse (renamePat m pren) (renameClosure m pren)) cs
      r' <- rename m pren r
      renameSp m pren (SCase dat v' r' cs') sp
    VLam i x t -> do
      t' <- renameClosure m pren t
      return $ SLam i x t'
    VPi i x a b -> do
      a' <- rename m pren a
      b' <- renameClosure m pren b
      return $ SPi i x a' b'
    VU -> return SU
    VNeu (VApp (VGlobal g) sp) -> renameSp m pren (SGlobal g) sp
    VLit l -> SLit <$> traverse (rename m pren) l

unifySpines :: (Tc m) => Spine VTm -> Spine VTm -> m CanUnify
unifySpines Empty Empty = return Yes
unifySpines (sp :|> Arg _ u) (sp' :|> Arg _ u') = unifySpines sp sp' /\ unify u u'
unifySpines sp sp' = return $ No [DifferentSpineLengths sp sp']

unifyClauses :: (Tc m) => [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses [] [] = return Yes
unifyClauses (c : cs) (c' : cs') = unifyClause c c' /\ unifyClauses cs cs'
unifyClauses a b = return $ No [DifferentClauses a b]

unifyPat :: (Tc m) => VPatB -> VPatB -> m CanUnify
unifyPat pt@(VPatB p binds) (VPatB p' binds') = do
  let n = length binds
  let n' = length binds'
  if n == n'
    then enterTypelessPatBinds pt $ unify p p'
    else return $ No []

unifyClause :: (Tc m) => Clause VPatB Closure -> Clause VPatB Closure -> m CanUnify
unifyClause (Possible p t) (Possible p' t') = unifyPat p p' /\ unifyClosure t t'
unifyClause (Impossible p) (Impossible p') = unifyPat p p'
unifyClause a b = return $ No [DifferentClauses [a] [b]]

data Problem = Problem
  { ctx :: Ctx,
    loc :: Loc,
    lhs :: VTm,
    rhs :: VTm,
    errs :: [UnifyError]
  }
  deriving (Show)

instance (Tc m) => Pretty m Problem where
  pretty (Problem ctx _ lhs rhs errs) = enterCtx (const ctx) $ do
    lhs' <- pretty lhs
    rhs' <- pretty rhs
    errs' <- intercalate ", " <$> mapM pretty errs
    return $ "lhs: " ++ lhs' ++ "\nrhs: " ++ rhs' ++ "\nerrors: " ++ errs'

addProblem :: (Tc m) => Problem -> m ()
addProblem p = modify (S.|> p)

addNewProblem :: (Tc m) => VTm -> VTm -> SolveError -> m ()
addNewProblem t t' e = do
  c <- getCtx
  l <- view
  let p = Problem {ctx = c, loc = l, lhs = t, rhs = t', errs = []}
  addProblem $ p {errs = [SolveError (WithProblem p e)]}

removeProblem :: (Tc m) => Int -> m ()
removeProblem i = modify (\(p :: Seq Problem) -> S.deleteAt i p)

getProblems :: (Tc m) => m (Seq Problem)
getProblems = view

enterProblem :: (Tc m) => Problem -> m a -> m a
enterProblem p = enterPat NotInPat . enterCtx (const p.ctx) . enterLoc p.loc

newtype SolveAttempts = SolveAttempts {n :: Int}

solveRemainingProblems :: (Tc m) => m ()
solveRemainingProblems = do
  att <- view
  solveRemainingProblems' att
  where
    solveRemainingProblems' :: (Tc m) => SolveAttempts -> m ()
    solveRemainingProblems' (SolveAttempts 0) = return ()
    solveRemainingProblems' (SolveAttempts n) = do
      ps <- getProblems
      if null ps
        then return ()
        else do
          _ <-
            S.traverseWithIndex
              ( \i p -> enterProblem p $ do
                  lhs' <- resolveHere p.lhs
                  rhs' <- resolveHere p.rhs
                  c <- unify lhs' rhs'
                  handleUnification lhs' rhs' c
                  removeProblem i
              )
              ps
          solveRemainingProblems' (SolveAttempts (n - 1))

runSolveT :: (Tc m) => MetaVar -> Spine VTm -> VTm -> SolveT m () -> m CanUnify
runSolveT m sp t f = do
  f' <- runExceptT f
  case f' of
    Left err -> do
      addNewProblem (VNeu (VApp (VFlex m) sp)) t err
      return Yes
    Right () -> solveRemainingProblems >> return Yes

unifyFlex :: (Tc m) => MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyFlex m sp t = runSolveT m sp t $ do
  pren <- invertSpine sp
  rhs <- rename m pren t
  solution <- lift $ uniqueSLams (reverse $ map (\a -> a.mode) (toList sp)) rhs >>= eval []
  lift $ solveMetaVar m solution

iDontKnow :: (Tc m) => m CanUnify
iDontKnow = return Maybe

unfoldDefAndUnify :: (Tc m) => DefGlobal -> Spine VTm -> VTm -> m CanUnify
unfoldDefAndUnify g sp t' = do
  gu <- access (unfoldDef g)
  case gu of
    Nothing -> iDontKnow
    Just gu' -> do
      t <- vApp gu' sp
      unify t t'

unifyLit :: (Tc m) => Lit VTm -> VTm -> m CanUnify
unifyLit a t = case t of
  VLit a' -> case (a, a') of
    (StringLit x, StringLit y) | x == y -> return Yes
    (CharLit x, CharLit y) | x == y -> return Yes
    (NatLit x, NatLit y) | x == y -> return Yes
    (FinLit d n, FinLit d' n') | d == d' -> unify n n'
    _ -> return $ No [Mismatching (VLit a) (VLit a')]
  _ -> unify (unfoldLit a) t

unifyClosure :: (Tc m) => Closure -> Closure -> m CanUnify
unifyClosure cl1 cl2 = do
  l <- getLvl
  t1 <- evalInOwnCtx l cl1
  t2 <- evalInOwnCtx l cl2
  if cl1.numVars == cl2.numVars
    then enterTypelessClosure cl1 $ unify t1 t2
    else error "unifyClosure: different number of variables"

etaConvert :: (Tc m) => VTm -> PiMode -> Closure -> m CanUnify
etaConvert t m c = do
  l <- getLvl
  x <- evalInOwnCtx l c
  x' <- vApp t (S.singleton (Arg m (VNeu (VVar l))))
  enterTypelessClosure c $ unify x x'

unify :: (Tc m) => VTm -> VTm -> m CanUnify
unify t1 t2 = do
  t1' <- force t1
  t2' <- force t2
  case (t1', t2') of
    (VPi m _ t c, VPi m' _ t' c') | m == m' -> unify t t' /\ unifyClosure c c'
    (VLam m _ c, VLam m' _ c') | m == m' -> unifyClosure c c'
    (t, VLam m' _ c') -> etaConvert t m' c'
    (VLam m _ c, t) -> etaConvert t m c
    (VU, VU) -> return Yes
    (t, VLit a') -> unifyLit a' t
    (VLit a, t') -> unifyLit a t'
    (VGlob (CtorGlob c) sp, VGlob (CtorGlob c') sp') | c == c' -> unifySpines sp sp'
    (VGlob (DataGlob d) sp, VGlob (DataGlob d') sp') | d == d' -> unifySpines sp sp'
    (VGlob (PrimGlob f) sp, VGlob (PrimGlob f') sp') ->
      if f == f'
        then unifySpines sp sp'
        else iDontKnow
    (VGlob (DefGlob f) sp, VGlob (DefGlob f') sp') ->
      if f == f'
        then unifySpines sp sp' \/ unfoldDefAndUnify f sp t2'
        else unfoldDefAndUnify f sp t2'
    (VGlob (DefGlob f) sp, t') -> unfoldDefAndUnify f sp t'
    (t, VGlob (DefGlob f') sp') -> unfoldDefAndUnify f' sp' t
    (VNeu (VCaseApp a s r bs sp), VNeu (VCaseApp b s' r' bs' sp')) | a == b -> do
      ( unify (VNeu s) (VNeu s')
          /\ unifyClauses bs bs'
          /\ unify r r'
          /\ unifySpines sp sp'
        )
        \/ iDontKnow
    (VNeu (VReprApp m v sp), VNeu (VReprApp m' v' sp')) | m == m' -> do
      (unify (VNeu v) (VNeu v') /\ unifySpines sp sp') \/ iDontKnow
    (VNeu (VApp (VRigid x) sp), VNeu (VApp (VRigid x') sp')) | x == x' -> do
      unifySpines sp sp' \/ iDontKnow
    (VNeu (VApp (VFlex x) sp), VNeu (VApp (VFlex x') sp')) | x == x' -> do
      unifySpines sp sp' \/ iDontKnow
    (VNeu (VApp (VFlex x) sp), t') -> unifyFlex x sp t'
    (t, VNeu (VApp (VFlex x') sp')) -> unifyFlex x' sp' t
    (VNeu (VApp (VRigid _) _), _) -> iDontKnow
    (_, VNeu (VApp (VRigid _) _)) -> iDontKnow
    (VNeu (VReprApp {}), _) -> iDontKnow
    (_, VNeu (VReprApp {})) -> iDontKnow
    (VNeu (VCaseApp {}), _) -> iDontKnow
    (_, VNeu (VCaseApp {})) -> iDontKnow
    _ -> return $ No [Mismatching t1' t2']
