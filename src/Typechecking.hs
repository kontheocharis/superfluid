{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

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
    unrepr,
    meta,
    wildPat,
    caseOf,
    checkByInfer,
    enterTel,
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

import Algebra.Lattice (Lattice (..), meets1, (/\))
import Common
  ( Arg (..),
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
    Logger (msg),
    Lvl (..),
    MetaVar,
    Name (Name),
    Param (..),
    PiMode (..),
    Positive,
    PrimGlobal (..),
    Spine,
    Tag,
    Tel,
    Times (..),
    composeN,
    composeZ,
    inv,
    lvlToIdx,
    mapSpine,
    mapSpineM,
    nextLvl,
    nextLvls,
    telWithNames,
    pattern Impossible,
    pattern Possible,
  )
import Context
  ( Ctx (..),
    Goal (Goal),
    bind,
    define,
    emptyCtx,
    insertedBind,
    lookupName,
    typelessBinds,
  )
import Control.Applicative (Alternative (empty))
import Control.Monad (replicateM, unless, zipWithM)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Extra (when)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Foldable (Foldable (..), toList)
import qualified Data.IntMap as IM
import Data.List (intercalate)
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..), (><))
import qualified Data.Sequence as S
import Data.Set (Set)
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
    vApp,
    vCase,
    vRepr,
    vUnfold,
    vUnfoldLazy,
    vWhnf,
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
import Syntax
  ( Case (..),
    Closure (body, numVars),
    Env,
    PRen (..),
    SPat (..),
    STm (..),
    STy,
    Sub,
    VLazy,
    VLazyHead (..),
    VNeu,
    VNeuHead (..),
    VNorm (..),
    VPatB (..),
    VTm (..),
    VTy,
    WTm (..),
    headAsValue,
    isEmptySub,
    liftPRenN,
    sAppSpine,
    sGatherApps,
    sGatherLams,
    sGatherPis,
    sPis,
    uniqueSLams,
    vGetSpine,
    weakAsValue,
    pattern VVar,
  )
import Unelaboration (Unelab)

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

class (Eval m, Unelab m, Has m Loc, Has m (Seq Problem), Has m InPat, Has m Ctx, Has m SolveAttempts) => Tc m where
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

data Mode = Check VTy | Infer

type Child m = (Mode -> m (STm, VTy))

ensureAllProblemsSolved :: (Tc m) => m ()
ensureAllProblemsSolved = do
  solveRemainingProblems
  ps <- view
  if S.null ps
    then return ()
    else tcError $ RemainingProblems (toList ps)

uniqueNames :: (Tc m) => Int -> m [Name]
uniqueNames n = replicateM n uniqueName

enterTel :: (Tc m) => Tel STy -> m a -> m a
enterTel Empty f = f
enterTel (t :<| ts) f = do
  t' <- evalHere t.ty
  enterCtx (bind t.name t') (enterTel ts f)

inferMeta :: (Tc m) => Maybe Name -> m (STm, VTy)
inferMeta n = do
  ty <- newMeta Nothing
  vty <- evalHere ty
  checkMeta n vty

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
  m <- pretty ty
  msg $ " Getting whnf for " ++ m
  f <- unfoldHere ty
  f' <- pretty f
  msg $ " Got whnf " ++ f'
  case f of
    VNorm (VPi Implicit _ _ b) -> do
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

unfoldLazyHere :: (Tc m) => VLazy -> m (Maybe VTm)
unfoldLazyHere (n, sp) = do
  lvl <- getLvl
  vUnfoldLazy lvl (n, sp)

unfoldHere :: (Tc m) => VTm -> m VTm
unfoldHere t = do
  l <- accessCtx (\c -> c.lvl)
  t' <- pretty t
  msg $ "Trying to unfold " ++  t'
  res <- vUnfold l t
  res' <- pretty res
  msg $ "Unfolded to " ++  res'
  return res

ifForcePiType ::
  (Tc m) =>
  PiMode ->
  VTy ->
  (PiMode -> Name -> VTy -> Closure -> m a) ->
  (PiMode -> Name -> VTy -> Closure -> m a) ->
  m a
ifForcePiType m ty the els = do
  ty' <- unfoldHere ty
  case ty' of
    VNorm (VPi m' x a b) -> do
      if m == m'
        then the m' x a b
        else els m' x a b
    _ -> do
      a <- freshMeta >>= evalHere
      x <- uniqueName
      b <- enterCtx (bind x a) freshMeta >>= closeHere 1
      unifyHere ty (VNorm (VPi m x a b))
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

reprHere :: (Tc m) => Int -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  res <- vRepr l m t
  t' <- pretty t
  t'' <- pretty res
  msg $ "Result of REPR " ++ show m ++ " " ++ t' ++ " is " ++ t''
  return res

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
            return (SLam m x t', VNorm (VPi m x' a b))
        )
        ( \m' x' a b -> case m' of
            Implicit -> insertLam x' a b (\s -> lam s m x t)
            _ -> tcError $ ImplicitMismatch m m'
        )
    Infer -> do
      a <- freshMeta >>= evalHere
      (t', b) <- enterCtx (bind x a) $ t Infer >>= insert
      b' <- closeValHere 1 b
      return (SLam m x t', VNorm (VPi m x a b'))

insertLam :: (Tc m) => Name -> VTy -> Closure -> Child m -> m (STm, VTy)
insertLam x' a b t = do
  vb <- evalInOwnCtxHere b
  (t', _) <- enterCtx (insertedBind x' a) (t (Check vb))
  return (SLam Implicit x' t', VNorm (VPi Implicit x' a b))

letIn :: (Tc m) => Mode -> Name -> Child m -> Child m -> Child m -> m (STm, VTy)
letIn mode x a t u = do
  forbidPat
  (a', _) <- a (Check (VNorm VU))
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
  return (SU, (VNorm VU))

piTy :: (Tc m) => PiMode -> Name -> Child m -> Child m -> m (STm, VTy)
piTy m x a b = do
  forbidPat
  (a', _) <- a (Check (VNorm VU))
  av <- evalHere a'
  (b', _) <- enterCtx (bind x av) $ b (Check (VNorm VU))
  return (SPi m x a' b', (VNorm VU))

repr :: (Tc m) => Mode -> Child m -> m (STm, VTy)
repr mode t = do
  forbidPat
  case mode of
    Check ty -> do
      msg "Checking"
      checkByInfer (repr Infer t) ty
    Infer -> do
      (t', ty) <- t Infer
      msg $ "Inferred"
      reprTy <- reprHere 1 ty
      msg $ "Represented"
      return (SRepr t', reprTy)

unrepr :: (Tc m) => Mode -> Child m -> m (STm, VTy)
unrepr mode t = do
  forbidPat
  case mode of
    Check ty -> do
      (t', ty') <- t Infer >>= insert
      reprTy <- reprHere 1 ty
      unifyHere reprTy ty'
      return (SUnrepr t', ty)
    Infer -> do
      (t', ty) <- t Infer
      unreprTy <- reprHere (-1) ty
      return (SUnrepr t', unreprTy)

checkByInfer :: (Tc m) => m (STm, VTy) -> VTy -> m (STm, VTy)
checkByInfer t ty = do
  msg "Inserting"
  (t', ty') <- t >>= insert
  msg "Unifying"
  unifyHere ty ty'
  return (t', ty)

pat :: (Tc m) => InPat -> m VTy -> Child m -> (SPat -> VTy -> m ()) -> (SPat -> VTy -> m a) -> m a
pat inPt wideTyM pt runInsidePatScope runOutsidePatScope = enterCtx id $ do
  (p', t, ns) <- enterPat inPt $ do
    (p', t') <- pt Infer >>= insert
    wideTy <- wideTyM
    unifyHere t' wideTy

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

caseClauses :: (Tc m) => DataGlobalInfo -> m VTy -> [Clause (Child m) (Child m)] -> (VPatB -> SPat -> VTy -> Child m -> m a) -> m [a]
caseClauses di wideTyM cs f = do
  mapM
    ( \case
        (_, Just (Impossible _)) -> tcError ImpossibleCasesNotSupported
        (c, Just (Possible p t)) -> do
          pat (InPossiblePat []) wideTyM p (const . const $ return ()) $ \sp pTy -> do
            vp <- evalPatHere sp
            case c of
              Just c' -> do
                l <- getLvl
                ensureIsCtor l vp.vPat c' (tcError $ ExpectedCtor vp c')
                f vp sp pTy t
              Nothing -> do
                tcError $ UnexpectedPattern vp
        (Just c, Nothing) -> tcError $ MissingCtor c
        (Nothing, Nothing) -> error "impossible"
    )
    (mzip (map Just di.ctors) (map Just cs))

ensureDataAndGetWide :: (Tc m) => VTy -> (forall a. m a) -> m (DataGlobal, Spine VTm, Spine VTm, m VTy)
ensureDataAndGetWide ssTy f = do
  l <- getLvl
  ifIsData
    l
    ssTy
    ( \d sp -> do
        di <- access (getDataGlobal d)
        let paramSp = S.take (length di.params) sp
        let indexSp = S.drop (length di.params) sp
        let rest =
              VNorm . VData . (d,) . (paramSp ><)
                <$> traverse
                  (traverse (\_ -> freshMeta >>= evalHere))
                  (S.drop (length di.params) sp)
        return (d, paramSp, indexSp, rest)
    )
    f

caseOf :: (Tc m) => Mode -> Child m -> Maybe (Child m) -> [Clause (Child m) (Child m)] -> m (STm, VTy)
caseOf mode s r cs = do
  forbidPat
  case mode of
    Infer -> do
      retTy <- freshMeta >>= evalHere
      caseOf (Check retTy) s r cs
    Check ty -> do
      (ss, ssTy) <- s Infer
      (d, paramSp, indexSp, wideTyM) <- ensureDataAndGetWide ssTy (tcError $ InvalidCaseSubject ss ssTy)
      di <- access (getDataGlobal d)
      let motive = fromJust di.motiveTy
      motiveApplied <- motive $$ map (\a -> a.arg) (toList paramSp)
      rr <- case r of
        Just r' -> fst <$> r' (Check motiveApplied)
        Nothing -> constLamsForPis motiveApplied ty
      vrr <- evalHere rr
      scs <- caseClauses di wideTyM cs $ \vp sp pTy t -> do
        let pTySp = S.drop (length di.params) $ vGetSpine pTy
        branchTy <- vApp vrr (pTySp S.:|> Arg Explicit vp.vPat)
        (st, _) <- t (Check branchTy)
        return $ Possible sp st
      vs <- evalHere ss
      retTy <- vApp vrr (indexSp S.:|> Arg Explicit vs)
      unifyHere ty retTy
      sParamSp <- mapSpineM quoteHere paramSp
      sIndexSp <- mapSpineM quoteHere indexSp
      return (SCase (Case d sParamSp ss sIndexSp rr scs), ty)

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
        (bound', _) <- bound (Check (VNorm (VData (knownData KnownNat, Empty))))
        vbound' <- evalHere bound'
        return (FinLit f bound', KnownFin, S.singleton (Arg Explicit vbound'))
    return (SLit l', (VNorm (VData (knownData ty, args))))

defItem :: (Tc m) => Name -> Set Tag -> Child m -> Child m -> m ()
defItem n ts ty tm = do
  ensureNewName n
  (ty', _) <- ty (Check (VNorm VU))
  vty <- evalHere ty'
  modify (addItem n (DefInfo (DefGlobalInfo n vty Nothing Nothing)) ts)
  (tm', _) <- tm (Check vty)
  vtm <- evalHere tm'
  b <- normaliseProgram
  stm <- if b then quote (Lvl 0) vtm else return tm'
  modify (modifyDefItem (DefGlobal n) (\d -> d {tm = Just stm, vtm = Just vtm}))
  return ()

tel :: (Tc m) => Tel (Child m) -> m (Tel STy)
tel Empty = return Empty
tel (t :<| ts) = do
  (t', _) <- t.ty (Check (VNorm VU))
  vt <- evalHere t'
  ts' <- enterCtx (bind t.name vt) $ tel ts
  return (Param t.mode t.name t' :<| ts')

dataItem :: (Tc m) => Name -> Set Tag -> Tel (Child m) -> Child m -> m ()
dataItem n ts te ty = do
  ensureNewName n
  te' <- tel te
  ty' <- enterTel te' $ do
    (ty', _) <- ty (Check (VNorm VU))
    vty <- evalHere ty'
    i <- getLvl >>= (`isTypeFamily` vty)
    unless i (tcError $ InvalidDataFamily vty)
    return ty'
  cty <- closeHere (length te') ty'
  fty <- evalHere $ sPis te' ty'
  modify (addItem n (DataInfo (DataGlobalInfo n te' fty cty [] Nothing Nothing Empty)) ts)

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
                indexArity = arity
              }
        )
    )

ctorItem :: (Tc m) => DataGlobal -> Name -> Set Tag -> Child m -> m ()
ctorItem dat n ts ty = do
  di <- access (getDataGlobal dat)
  idx <- access (\s -> length (getDataGlobal dat s).ctors)
  (sp, ty') <- enterTel di.params $ do
    ensureNewName n
    (ty', _) <- ty (Check (VNorm VU))
    let sp = fmap (\p -> Arg p.mode ()) $ fst (sGatherPis ty')
    vty <- evalHere ty'
    i <- getLvl >>= (\l -> isCtorTy l dat vty)
    case i of
      Nothing -> tcError $ InvalidCtorType ty'
      Just _ -> return (sp, ty')
  cty <- closeHere (length di.params) ty'
  modify (addItem n (CtorInfo (CtorGlobalInfo n cty idx dat sp)) ts)
  modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal n]}))

primItem :: (Tc m) => Name -> Set Tag -> Child m -> m ()
primItem n ts ty = do
  ensureNewName n
  (ty', _) <- ty (Check (VNorm VU))
  vty <- evalHere ty'
  modify (addItem n (PrimInfo (PrimGlobalInfo n vty)) ts)

reprItem :: (Tc m) => Tel STm -> m VTy -> (Closure -> Set Tag -> Sig -> Sig) -> Set Tag -> Child m -> m STm
reprItem te getGlob addGlob ts r = do
  ty <- getGlob
  (r', _) <- enterTel te $ do
    ty' <- pretty ty
    msg $ "Checking repr item: " ++ ty'
    x <- r (Check ty)
    msg $ "Checked repr item"
    return x
  vr <- closeHere (length te) r'
  modify (addGlob vr ts)
  return r'

reprDataItem :: (Tc m) => DataGlobal -> Set Tag -> Child m -> m (Tel STm)
reprDataItem dat ts c = do
  di <- access (getDataGlobal dat)
  tm <-
    reprItem
      Empty
      (return di.fullTy)
      (addDataRepr dat)
      ts
      c
  let (ls, _) = sGatherLams tm
  return (telWithNames di.params ls)

reprCtorItem :: (Tc m) => Tel STm -> CtorGlobal -> Set Tag -> Child m -> m ()
reprCtorItem te ctor ts c = do
  ci <- access (getCtorGlobal ctor)
  msg $ "repr ctor " ++ show (ctor.globalName)
  _ <-
    reprItem
      te
      (evalInOwnCtxHere ci.ty)
      (addCtorRepr ctor)
      ts
      c
  msg $ "repr ctor done" ++ show (ctor.globalName)
  return ()

reprDefItem :: (Tc m) => DefGlobal -> Set Tag -> Child m -> m ()
reprDefItem def ts c = do
  _ <- reprItem Empty (access (getDefGlobal def) >>= \d -> return d.ty) (addDefRepr def) ts c
  return ()

reprCaseItem :: (Tc m) => Tel STm -> DataGlobal -> Set Tag -> Child m -> m ()
reprCaseItem te dat ts c = do
  di <- access (getDataGlobal dat)
  _ <-
    reprItem
      te
      (evalInOwnCtxHere (fromJust di.elimTy))
      (addCaseRepr dat)
      ts
      c
  return ()

quoteHere :: (Tc m) => VTm -> m STm
quoteHere t = do
  l <- accessCtx (\c -> c.lvl)
  quote l t

spineForTel :: Int -> Tel STm -> Spine STm
spineForTel dist te =
  S.fromList $ zipWith (curry (\(Param m _ _, i) -> Arg m (SVar (Idx (dist + length te - i - 1))))) (toList te) [0 ..]

telWithUniqueNames :: (Tc m) => Tel a -> m (Tel a)
telWithUniqueNames = do
  mapM
    ( \(Param m n a) -> do
        case n of
          Name "_" -> do
            n' <- uniqueName
            return (Param m n' a)
          Name _ -> return (Param m n a)
    )

buildElimTy :: (Tc m) => DataGlobal -> m (Closure, Closure, Spine ())
buildElimTy dat = do
  -- @@Cleanup: this is a mess, ideally should hide all the index acrobatics..
  datInfo <- access (getDataGlobal dat)

  let sTyParams = datInfo.params
  let sTyParamsV = map (VNeu . VVar . Lvl) $ take (length datInfo.params) [0 ..]

  let motiveLvl = length datInfo.params
  let methodTyLvl i = motiveLvl + 1 + i
  let sTyIndicesLvl = methodTyLvl (length datInfo.ctors)

  sTy <- datInfo.ty $$ sTyParamsV >>= quote (Lvl sTyIndicesLvl)
  let (mTyIndices, _) = sGatherPis datInfo.ty.body
  mTyIndicesBinds <- telWithUniqueNames mTyIndices

  let (sTyIndices, _) = sGatherPis sTy
  sTyIndicesBinds <- telWithUniqueNames sTyIndices

  let spToData i j = sAppSpine (SData dat) (spineForTel i sTyParams >< spineForTel j mTyIndicesBinds)

  motiveSubjName <- uniqueName
  elimTyName <- uniqueName
  subjectTyName <- uniqueName
  methodTys <- mapM (ctorMethodTy (length sTyParams)) datInfo.ctors

  let motiveTy = sPis (mTyIndicesBinds :|> Param Explicit motiveSubjName (spToData (length mTyIndicesBinds) 0)) SU
  let subjSpToData = spToData (length mTyIndicesBinds + length methodTys + 1) 0

  let elimTy =
        sPis
          ( foldr
              (><)
              Empty
              [ S.singleton (Param Explicit elimTyName motiveTy),
                S.fromList
                  ( zipWith
                      (\i (methodTy, methodName) -> Param Explicit methodName (methodTy i))
                      [0 ..]
                      methodTys
                  ),
                sTyIndicesBinds,
                S.singleton (Param Explicit subjectTyName subjSpToData)
              ]
          )
          (sAppSpine (SVar (Idx (1 + length sTyIndicesBinds + length methodTys))) (spineForTel 1 sTyIndicesBinds S.|> Arg Explicit (SVar (Idx 0))))

  elimTy' <- closeHere (length datInfo.params) elimTy
  motiveTy' <- closeHere (length datInfo.params) motiveTy
  return (motiveTy', elimTy', fmap (\p -> Arg p.mode ()) sTyIndicesBinds)
  where
    ctorMethodTy :: (Tc m) => Int -> CtorGlobal -> m (Int -> STy, Name)
    ctorMethodTy sTyParamLen ctor = do
      ctorInfo <- access (getCtorGlobal ctor)
      sTy <- (ctorInfo.ty $$ map (VNeu . VVar . Lvl) [0 .. sTyParamLen - 1]) >>= quote (Lvl (sTyParamLen + 1 + ctorInfo.idx))
      let (sTyBinds', sTyRet) = sGatherPis sTy
      sTyBinds <- telWithUniqueNames sTyBinds'
      let (_, sTyRetSp) = sGatherApps sTyRet

      let spToCtor =
            sAppSpine
              ( SCtor
                  ( ctor,
                    ( toList . fmap (\a -> a.arg) $
                        S.take sTyParamLen sTyRetSp
                    )
                  )
              )
              (spineForTel 0 sTyBinds)
      n <- uniqueName
      return . (,n) $ \sMotiveIdx ->
        let methodRetTy =
              sAppSpine
                (SVar (Idx (sMotiveIdx + length sTyBinds)))
                (S.drop sTyParamLen sTyRetSp S.|> Arg Explicit spToCtor)
         in sPis sTyBinds methodRetTy

globalInfoToTm :: (Tc m) => Name -> GlobalInfo -> m (STm, VTy)
globalInfoToTm n i = case i of
  DefInfo d -> return (SDef (DefGlobal n), d.ty)
  DataInfo d -> do
    ty' <- evalHere $ sPis d.params d.ty.body
    return (SData (DataGlobal n), ty')
  CtorInfo c -> do
    di <- access (getDataGlobal c.dataGlobal)
    metas <- replicateM (length di.params) freshMeta
    vmetas <- mapM evalHere metas
    ty' <- c.ty $$ vmetas
    return (SCtor (CtorGlobal n, metas), ty')
  PrimInfo p -> return (SPrim (PrimGlobal n), p.ty)

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

instance (Tc m) => Has m (Env VTm) where
  view = accessCtx (\c -> c.env)
  modify f = modifyCtx (\c -> c {env = f c.env})

instance (Tc m) => Has m [Name] where
  view = accessCtx (\c -> c.nameList)
  modify f = modifyCtx (\c -> c {nameList = f c.nameList})

instance (Tc m) => Has m Lvl where
  view = accessCtx (\c -> c.lvl)
  modify f = modifyCtx (\c -> c {lvl = f c.lvl})

instance (Eval m) => Lattice (m CanUnify) where
  a \/ b = do
    a' <- a
    case a' of
      Yes -> return a'
      No _ -> b
      Maybe -> do
        b' <- b
        case b' of
          Yes -> return Yes
          No _ -> return a'
          Maybe -> return Maybe

  a /\ b = do
    a' <- a
    case a' of
      Yes -> b
      No xs -> do
        b' <- b
        case b' of
          Yes -> return a'
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

renameCaseSpine ::
  (Tc m) =>
  (MetaVar -> PRen -> s -> SolveT m STm) ->
  MetaVar ->
  PRen ->
  Case s VTm VPatB Closure ->
  Spine VTm ->
  SolveT m STm
renameCaseSpine renameSubject m pren (Case dat pp v i r cs) sp = do
  v' <- renameSubject m pren v
  cs' <- mapM (bitraverse (renamePat m pren) (renameClosure m pren)) cs
  r' <- rename m pren r
  pp' <- mapSpineM (rename m pren) pp
  i' <- mapSpineM (rename m pren) i
  renameSp m pren (SCase (Case dat pp' v' i' r' cs')) sp

renameReprSpine :: (Tc m) => MetaVar -> PRen -> Int -> VTm -> Spine VTm -> SolveT m STm
renameReprSpine m pren t n sp = do
  m' <- rename m pren n
  let hd = composeZ t SRepr SUnrepr m'
  renameSp m pren hd sp

renameLazy :: (Tc m) => MetaVar -> PRen -> VLazy -> SolveT m STm
renameLazy m pren (n, sp) = case n of
  VDef d -> renameSp m pren (SDef d) sp
  VLit t -> do
    t' <- traverse (rename m pren) t
    renameSp m pren (SLit t') sp
  VLazyCase c -> renameCaseSpine renameLazy m pren c sp
  VRepr n' -> renameReprSpine m pren 1 (headAsValue n') sp

renameNeu :: (Tc m) => MetaVar -> PRen -> VNeu -> SolveT m STm
renameNeu m pren (n, sp) = case n of
  VFlex m'
    | m == m' -> throwError $ OccursError m
    | otherwise -> renameSp m pren (SMeta m' []) sp
  VRigid (Lvl l) -> case IM.lookup l pren.vars of
    Nothing -> throwError EscapingVariable
    Just x' -> renameSp m pren (SVar (lvlToIdx pren.domSize x')) sp
  VBlockedCase c -> renameCaseSpine renameNeu m pren c sp
  VPrim p -> renameSp m pren (SPrim p) sp
  VUnrepr n' -> renameReprSpine m pren (-1) (headAsValue n') sp

renameNorm :: (Tc m) => MetaVar -> PRen -> VNorm -> SolveT m STm
renameNorm m pren n = case n of
  VLam i x t -> do
    t' <- renameClosure m pren t
    return $ SLam i x t'
  VPi i x ty t -> do
    ty' <- rename m pren ty
    t' <- renameClosure m pren t
    return $ SPi i x ty' t'
  VU -> return SU
  VData (d, sp) -> renameSp m pren (SData d) sp
  VCtor ((c, pp), sp) -> do
    pp' <- mapM (rename m pren) pp
    renameSp m pren (SCtor (c, pp')) sp

rename :: (Tc m) => MetaVar -> PRen -> VTm -> SolveT m STm
rename m pren tm = case tm of
  VNorm n -> renameNorm m pren n
  VLazy n -> renameLazy m pren n
  VNeu n -> renameNeu m pren n

unifySpines :: (Tc m) => Spine VTm -> Spine VTm -> m CanUnify
unifySpines Empty Empty = return Yes
unifySpines (sp :|> Arg _ u) (sp' :|> Arg _ u') = unifySpines sp sp' /\ unify u u'
unifySpines sp sp' = return $ No [DifferentSpineLengths sp sp']

unifyClauses :: (Tc m) => [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses [] [] = return Yes
unifyClauses (c : cs) (c' : cs') = unifyClause c c' /\ unifyClauses cs cs'
unifyClauses a b = return $ No [DifferentClauses a b]

unifyClause :: (Tc m) => Clause VPatB Closure -> Clause VPatB Closure -> m CanUnify
unifyClause (Possible _ t) (Possible _ t') = unifyClosure t t'
unifyClause (Impossible _) (Impossible _) = return Yes
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
      addNewProblem (VNeu (VFlex m, sp)) t err
      return Yes
    Right () -> solveRemainingProblems >> return Yes

unifyFlex :: (Tc m) => MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyFlex m sp t = runSolveT m sp t $ do
  pren <- invertSpine sp
  rhs <- rename m pren t
  solution <- lift $ uniqueSLams (reverse $ map (\a -> a.mode) (toList sp)) rhs >>= eval []
  lift $ solveMetaVar m solution

unifyClosure :: (Tc m) => Closure -> Closure -> m CanUnify
unifyClosure cl1 cl2 = do
  l <- getLvl
  t1 <- evalInOwnCtx l cl1
  t2 <- evalInOwnCtx l cl2
  if cl1.numVars == cl2.numVars
    then enterTypelessClosure cl1 $ unify t1 t2
    else error "unifyClosure: different number of variables"

iDontKnow :: (Tc m) => m CanUnify
iDontKnow = return Maybe

unify :: (Tc m) => VTm -> VTm -> m CanUnify
unify t1 t2 = do
  t1' <- force t1
  t2' <- force t2
  pt1 <- pretty t1'
  pt2 <- pretty t2'
  msg $ "unify: " ++ pt1 ++ " =? " ++ pt2
  unifyForced t1' t2'

etaConvert :: (Tc m) => VTm -> PiMode -> Closure -> m CanUnify
etaConvert t m c = do
  l <- getLvl
  x <- evalInOwnCtx l c
  x' <- vApp t (S.singleton (Arg m (VNeu (VVar l))))
  enterTypelessClosure c $ unify x x'

unifyForced :: (Tc m) => VTm -> VTm -> m CanUnify
unifyForced t1 t2 = case (t1, t2) of
  (VNorm (VLam m _ c), VNorm (VLam m' _ c')) | m == m' -> unifyClosure c c'
  (t, VNorm (VLam m' _ c')) -> etaConvert t m' c'
  (VNorm (VLam m _ c), t) -> etaConvert t m c
  (VNorm n1, VNorm n2) -> unifyNormRest n1 n2
  (VNeu (VFlex x, sp), VNeu (VFlex x', sp')) | x == x' -> unifySpines sp sp' \/ iDontKnow
  (VNeu (VFlex x, sp), _) -> unifyFlex x sp t2
  (_, VNeu (VFlex x', sp')) -> unifyFlex x' sp' t1
  (VNeu n1, VNeu n2) -> unifyNeuRest n1 n2
  (VLazy l1, VLazy l2) -> unifyLazy l1 l2
  (VLazy l, t) -> unifyLazyWithTermOr l t iDontKnow
  (t, VLazy l) -> unifyLazyWithTermOr l t iDontKnow
  _ -> return $ No [Mismatching t1 t2]

unifyNormRest :: (Tc m) => VNorm -> VNorm -> m CanUnify
unifyNormRest n1 n2 = case (n1, n2) of
  (VPi m _ t c, VPi m' _ t' c') | m == m' -> unify t t' /\ unifyClosure c c'
  (VU, VU) -> return Yes
  (VData (d, sp), VData (d', sp')) | d == d' -> unifySpines sp sp'
  (VCtor ((c, _), sp), VCtor ((c', _), sp'))
    | c == c' -> unifySpines sp sp'
  _ -> return $ No [Mismatching (VNorm n1) (VNorm n2)]

unifyLazy :: (Tc m) => VLazy -> VLazy -> m CanUnify
unifyLazy (n1, sp1) (n2, sp2) = case (n1, n2) of
  (VDef d1, VDef d2) | d1 == d2 -> unifySpines sp1 sp2
  (VLit l1, VLit l2) -> unifyLit l1 l2 /\ unifySpines sp1 sp2
  (VLazyCase c1, VLazyCase c2) -> unifyCases VLazy c1 c2 /\ unifySpines sp1 sp2
  (VRepr n1', VRepr n2') -> unify (headAsValue n1') (headAsValue n2') /\ unifySpines sp1 sp2
  _ -> unifyLazyWithTermOr (n1, sp1) (VLazy (n2, sp2)) (unifyLazyWithTermOr (n2, sp2) (VLazy (n1, sp1)) iDontKnow)

unifyNeuRest :: (Tc m) => VNeu -> VNeu -> m CanUnify
unifyNeuRest (n1, sp1) (n2, sp2) = case (n1, n2) of
  (VRigid x, VRigid x') | x == x' -> unifySpines sp1 sp2 \/ iDontKnow
  (VBlockedCase c1, VBlockedCase c2) -> unifyCases VNeu c1 c2 /\ unifySpines sp1 sp2
  (VPrim p1, VPrim p2) | p1 == p2 -> unifySpines sp1 sp2
  (VUnrepr c1, VUnrepr c2) -> unify (headAsValue c1) (headAsValue c2) /\ unifySpines sp1 sp2
  _ -> return $ No [Mismatching (VNeu (n1, sp1)) (VNeu (n2, sp2))]

unifyLazyWithTermOr :: (Tc m) => VLazy -> VTm -> m CanUnify -> m CanUnify
unifyLazyWithTermOr l t els = do
  l' <- unfoldLazyHere l
  case l' of
    Just l'' -> unify l'' t
    Nothing -> els

unifyCases :: (Tc m) => (s -> VTm) -> Case s VTm VPatB Closure -> Case s VTm VPatB Closure -> m CanUnify
unifyCases f c1 c2 = unify (f c1.subject) (f c2.subject) /\ unifyClauses c1.clauses c2.clauses

unifyLit :: (Tc m) => Lit VTm -> Lit VTm -> m CanUnify
unifyLit l1 l2 = case (l1, l2) of
  (StringLit x, StringLit y) | x == y -> return Yes
  (CharLit x, CharLit y) | x == y -> return Yes
  (NatLit x, NatLit y) | x == y -> return Yes
  (FinLit d n, FinLit d' n') | d == d' -> unify n n'
  _ -> return $ No [Mismatching (VLazy (VLit l1, Empty)) (VLazy (VLit l2, Empty))]
