{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
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
    tel,
    piTy,
    name,
    insertLam,
    repr,
    unrepr,
    meta,
    wild,
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

import Algebra.Lattice (Lattice (..), (/\))
import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (DefGlobal),
    Has (..),
    HasNameSupply (uniqueName),
    HasProjectFiles,
    Idx (..),
    Lit (..),
    Loc,
    Lvl (..),
    MetaVar,
    Name (..),
    Param (..),
    PiMode (..),
    PrimGlobal (..),
    Qty (..),
    Spine,
    Tag,
    Tel,
    Try (..),
    composeZ,
    lvlToIdx,
    mapSpineM,
    nextLvl,
    nextLvls,
    telWithNames,
    pattern Impossible,
    pattern Possible, enterLoc,
  )
import Context
import Control.Applicative (Alternative (empty))
import Control.Monad (replicateM, unless)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Extra (when)
import Control.Monad.Trans (MonadTrans (lift))
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
    force,
    ifIsData,
    isCtorTy,
    isTypeFamily,
    quote,
    quotePat,
    resolve,
    vApp,
    vRepr,
    vUnfold,
    vUnfoldLazy,
    ($$),
    ($$>),
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
    dataIsIrrelevant,
    getCtorGlobal,
    getDataGlobal,
    getDefGlobal,
    hasName,
    knownData,
    lookupGlobal,
    modifyDataItem,
    modifyDefItem,
  )
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

data InPat = NotInPat | InPossiblePat [(Qty, Name)] | InImpossiblePat deriving (Eq)

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

class
  ( Eval m,
    Unelab m,
    Has m Loc,
    Try m,
    Has m Qty,
    Has m (Seq Problem),
    Has m InPat,
    Has m Ctx,
    Has m SolveAttempts
  ) =>
  Tc m
  where
  addGoal :: Goal -> m ()

  tcError :: TcError -> m a

  inPat :: m InPat
  inPat = view

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

instance (Monad m, Pretty m VTy) => Pretty m Mode where
  pretty (Check ty) = do
    ty' <- pretty ty
    return $ "Check " ++ ty'
  pretty Infer = return "Infer"

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

inferMeta :: (Tc m) => Maybe Name -> Qty -> m (STm, VTy)
inferMeta n q = do
  ty <- newMeta Nothing Zero
  vty <- evalHere ty
  checkMeta n vty q

prettyGoal :: (Tc m) => Goal -> m String
prettyGoal (Goal c n _ ty) = enterCtx (const c) $ do
  c' <- getCtx >>= pretty
  ty' <- pretty ty
  let g = maybe "_" (\n' -> "?" ++ n'.unName) n ++ " : " ++ ty'
  return $ indentedFst c' ++ "\n" ++ replicate (length g + 4) '―' ++ "\n" ++ indentedFst g ++ "\n"

checkMeta :: (Tc m) => Maybe Name -> VTy -> Qty -> m (STm, VTy)
checkMeta n ty q = do
  m <- newMeta n q
  c <- getCtx
  case n of
    Just _ -> addGoal (Goal c n m ty)
    Nothing -> return ()
  return (m, ty)

newMeta :: (Tc m) => Maybe Name -> Qty -> m STm
newMeta n q = do
  bs <- accessCtx (\c -> c.bounds)
  m <- freshMetaVar n q
  return (SMeta m bs)

freshMeta :: (Tc m) => Qty -> m STm
freshMeta = newMeta Nothing

freshMetaOrPatBind :: (Tc m) => m (STm, VTm)
freshMetaOrPatBind = do
  q <- qty
  ifInPat
    ( do
        n <- uniqueName
        (n', _) <- inferPatBind n
        vn <- evalPatHere (SPat n' [(q, n)])
        return (n', vn.vPat)
    )
    ( do
        n' <- freshMeta q
        vn <- evalHere n'
        return (n', vn)
    )

insertFull :: (Tc m) => (STm, VTy) -> m (STm, VTy)
insertFull (tm, ty) = do
  f <- unfoldHere ty
  case f of
    VNorm (VPi Implicit q _ _ b) -> do
      (a, va) <- enterQty q freshMetaOrPatBind
      ty' <- b $$ [va]
      insertFull (SApp Implicit q tm a, ty')
    _ -> return (tm, ty)

insert :: (Tc m) => (STm, VTy) -> m (STm, VTy)
insert (tm, ty) = case tm of
  SLam Implicit _ _ _ -> return (tm, ty)
  _ -> insertFull (tm, ty)

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
  vUnfold l t

ifForcePiType ::
  (Tc m) =>
  PiMode ->
  VTy ->
  (PiMode -> Qty -> Name -> VTy -> Closure -> m a) ->
  (PiMode -> Qty -> Name -> VTy -> Closure -> m a) ->
  m a
ifForcePiType m ty the els = do
  ty' <- unfoldHere ty
  case ty' of
    VNorm (VPi m' q x a b) -> do
      if m == m'
        then the m' q x a b
        else els m' q x a b
    _ -> do
      a <- freshMeta Zero >>= evalHere
      x <- uniqueName
      q <- qty
      b <- enterCtx (bind x q a) (freshMeta Zero) >>= closeHere 1
      unifyHere ty (VNorm (VPi m q x a b))
      the m q x a b

forbidPat :: (Tc m) => m ()
forbidPat = ifInPat (tcError InvalidPattern) (return ())

patBind :: (Tc m) => Mode -> Name -> m (STm, VTy)
patBind md n = case md of
  Infer -> inferPatBind n
  Check ty -> checkPatBind n ty

inferPatBind :: (Tc m) => Name -> m (STm, VTy)
inferPatBind x = do
  q <- qty
  ty <- freshMeta q >>= evalHere
  checkPatBind x ty

checkPatBind :: (Tc m) => Name -> VTy -> m (STm, VTy)
checkPatBind x ty = do
  q <- qty
  modifyCtx (bind x q ty)
  whenInPat
    ( \case
        InPossiblePat ns -> setInPat (InPossiblePat (ns ++ [(q, x)]))
        _ -> return ()
    )
  return (SVar (Idx 0), ty)

reprHere :: (Tc m) => Int -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

name :: (Tc m) => Mode -> Name -> m (STm, VTy)
name md n = do
  ifInPat
    ( do
        l <- access (lookupGlobal n)
        case l of
          Just c@(CtorInfo _) -> inferOnly (global n c) md
          _ -> patBind md n
    )
    ( do
        r <- accessCtx (lookupName n)
        l <- getLvl
        case r of
          Just e -> do
            inferOnly (return (SVar $ lvlToIdx l e.lvl, assertIsNeeded e.ty)) md
          Nothing -> do
            n' <- access (lookupGlobal n)
            case n' of
              Just x -> inferOnly (global n x) md
              Nothing -> tcError $ UnresolvedVariable n
    )

ensureNewName :: (Tc m) => Name -> m ()
ensureNewName n = do
  r <- access (hasName n)
  when r $ tcError $ DuplicateItem n

getLvl :: (Tc m) => m Lvl
getLvl = accessCtx (\c -> c.lvl)

inPatNames :: InPat -> [(Qty, Name)]
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
        ( \_ q x' a b -> do
            vb <- evalInOwnCtxHere b
            (t', _) <- enterCtx (bind x q a) (t (Check vb))
            return (SLam m q x t', VNorm (VPi m q x' a b))
        )
        ( \m' q x' a b -> case m' of
            Implicit -> insertLam q x' a b (\s -> lam s m x t)
            _ -> tcError $ ImplicitMismatch m m'
        )
    Infer -> do
      a <- freshMeta Zero >>= evalHere
      let q = Many
      (t', b) <- enterCtx (bind x q a) $ t Infer >>= insert
      b' <- closeValHere 1 b
      return (SLam m q x t', VNorm (VPi m q x a b'))

insertLam :: (Tc m) => Qty -> Name -> VTy -> Closure -> Child m -> m (STm, VTy)
insertLam q x' a b t = do
  vb <- evalInOwnCtxHere b
  (t', _) <- enterCtx (insertedBind x' q a) (t (Check vb))
  return (SLam Implicit q x' t', VNorm (VPi Implicit q x' a b))

letIn :: (Tc m) => Mode -> Qty -> Name -> Child m -> Child m -> Child m -> m (STm, VTy)
letIn mode q x a t u = do
  forbidPat
  (a', _) <- enterQty Zero $ a (Check (VNorm VU))
  va <- evalHere a'
  (t', _) <- enterQty q $ t (Check va)
  vt <- evalHere t'
  (u', ty) <- enterCtx (define x q vt va) $ u mode
  return (SLet q x a' t' u', ty)

spine :: (Tc m) => (STm, VTy) -> Spine (Child m) -> m (STm, VTy)
spine (t, ty) Empty = return (t, ty)
spine (t, ty) (Arg m _ u :<| sp) = do
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Explicit -> insertFull (t, ty)
    Instance -> error "unimplemented"
  ifForcePiType
    m
    ty'
    ( \_ q _ a b -> do
        (u', _) <- enterQty q $ u (Check a)
        uv <- evalHere u'
        b' <- b $$ [uv]
        spine (SApp m q t' u', b') sp
    )
    (\m' _ _ _ _ -> tcError $ ImplicitMismatch m m')

app :: (Tc m) => Child m -> Spine (Child m) -> m (STm, VTy)
app s sp = do
  (s', sTy) <- s Infer
  spine (s', sTy) sp

univ :: (Tc m) => m (STm, VTy)
univ = do
  forbidPat
  return (SU, VNorm VU)

piTy :: (Tc m) => PiMode -> Qty -> Name -> Child m -> Child m -> m (STm, VTy)
piTy m q x a b = do
  forbidPat
  (a', _) <- a (Check (VNorm VU))
  av <- evalHere a'
  (b', _) <- enterCtx (bind x q av) $ b (Check (VNorm VU))
  return (SPi m q x a' b', VNorm VU)

repr :: (Tc m) => Mode -> Child m -> m (STm, VTy)
repr mode t = do
  forbidPat
  case mode of
    Check ty -> do
      checkByInfer (repr Infer t) ty
    Infer -> do
      (t', ty) <- t Infer
      reprTy <- reprHere 1 ty
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
checkByInfer t ty = inferOnly t (Check ty)

inferOnly :: (Tc m) => m (STm, VTy) -> Mode -> m (STm, VTy)
inferOnly t mode = case mode of
  Check ty' -> do
    (t', ty) <- t >>= insert
    unifyHere ty ty'
    return (t', ty)
  Infer -> t

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
  uniqueSLams (toList $ fmap (\p -> (p.mode, p.qty)) args) sval.body

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
                  ( \p -> do
                      v' <- freshMeta p.qty >>= evalHere
                      return (Arg p.mode p.qty v')
                  )
                  (S.drop (length di.params) sp)
        return (d, paramSp, indexSp, rest)
    )
    f

caseSubject :: (Tc m) => Child m -> m (STm, VTy)
caseSubject s = do
  sRes <- try $ s Infer
  case sRes of
    Right r -> return r
    Left e -> do
      (ss, ssTy) <- enterQty Zero $ s Infer
      l <- getLvl
      ifIsData
        l
        ssTy
        ( \d _ -> do
            i <- access (dataIsIrrelevant d)
            if i
              then
                return ()
              else giveUp e
        )
        (return ()) -- Handled later
      return (ss, ssTy)

caseOf :: (Tc m) => Mode -> Child m -> Maybe (Child m) -> [Clause (Child m) (Child m)] -> m (STm, VTy)
caseOf mode s r cs = do
  forbidPat
  case mode of
    Infer -> do
      q <- qty
      retTy <- freshMeta q >>= evalHere
      caseOf (Check retTy) s r cs
    Check ty -> do
      (ss, ssTy) <- caseSubject s
      (d, paramSp, indexSp, wideTyM) <- ensureDataAndGetWide ssTy (tcError $ InvalidCaseSubject ss ssTy)

      di <- access (getDataGlobal d)
      let motive = fromJust di.motiveTy
      motiveApplied <- motive $$ map (\a -> a.arg) (toList paramSp)
      rr <- case r of
        Just r' -> enterQty Zero $ fst <$> r' (Check motiveApplied)
        Nothing -> constLamsForPis motiveApplied ty
      vrr <- evalHere rr

      scs <- caseClauses di wideTyM cs $ \vp sp pTy t -> do
        let pTySp = S.drop (length di.params) $ vGetSpine pTy
        branchTy <- vApp vrr (pTySp S.:|> Arg Explicit Many vp.vPat)
        (st, _) <- t (Check branchTy)
        return $ Possible sp st

      vs <- evalHere ss
      retTy <- vApp vrr (indexSp S.:|> Arg Explicit Many vs)
      unifyHere ty retTy

      sParamSp <- mapSpineM quoteHere paramSp
      sIndexSp <- mapSpineM quoteHere indexSp

      return (SCase (Case d sParamSp ss sIndexSp rr scs), ty)

wild :: (Tc m) => Mode -> m (STm, VTy)
wild md = do
  n <- uniqueName
  case md of
    Infer -> do
      forbidPat
      meta md Nothing
    (Check ty) -> ifInPat (checkPatBind n ty) (meta md Nothing)

meta :: (Tc m) => Mode -> Maybe Name -> m (STm, VTy)
meta mode n = do
  forbidPat
  q <- qty
  case mode of
    Infer -> inferMeta n q
    Check ty -> checkMeta n ty q

lit :: (Tc m) => Mode -> Lit (Child m) -> m (STm, VTy)
lit mode l = case mode of
  Check ty -> checkByInfer (lit Infer l) ty
  Infer -> do
    (l', ty, args) <- case l of
      StringLit s -> return (StringLit s, KnownString, Empty)
      CharLit c -> return (CharLit c, KnownChar, Empty)
      NatLit n -> return (NatLit n, KnownNat, Empty)
      FinLit f bound -> do
        (bound', _) <- bound (Check (VNorm (VData (knownData KnownNat, Empty)))) -- @@TODO: Check that bound is valid!
        vbound' <- evalHere bound'
        return (FinLit f bound', KnownFin, S.singleton (Arg Explicit Zero vbound'))
    return (SLit l', VNorm (VData (knownData ty, args)))

defItem :: (Tc m) => Qty -> Name -> Set Tag -> Child m -> Child m -> m ()
defItem q n ts ty tm = do
  ensureNewName n
  (ty', _) <- enterQty Zero $ ty (Check (VNorm VU))
  vty <- evalHere ty'
  modify (addItem n (DefInfo (DefGlobalInfo n q vty Nothing Nothing)) ts)
  (tm', _) <- enterQty q $ tm (Check vty)

  vtm <- evalHere tm'
  b <- normaliseProgram
  stm <- if b then quote (Lvl 0) vtm else return tm'

  modify (modifyDefItem (DefGlobal n) (\d -> d {tm = Just stm, vtm = Just vtm}))
  return ()

tel :: (Tc m) => Tel (Child m) -> m (Tel STy)
tel Empty = return Empty
tel (t :<| ts) = do
  (t', _) <- enterQty Zero $ t.ty (Check (VNorm VU))
  vt <- evalHere t'
  ts' <- enterCtx (bind t.name t.qty vt) $ tel ts
  return (Param t.mode t.qty t.name t' :<| ts')

dataItem :: (Tc m) => Name -> Set Tag -> Tel (Child m) -> Child m -> m ()
dataItem n ts te ty = do
  ensureNewName n
  te' <- tel te
  ty' <- enterTel te' $ do
    (ty', _) <- enterQty Zero $ ty (Check (VNorm VU))
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
  (sp, ty', q) <- enterTel di.params $ do
    ensureNewName n
    (ty', _) <- enterQty Zero $ ty (Check (VNorm VU))
    let sp = fmap (\p -> Arg p.mode p.qty ()) $ fst (sGatherPis ty')
    vty <- evalHere ty'
    i <- getLvl >>= (\l -> isCtorTy l dat vty)
    case i of
      Nothing -> tcError $ InvalidCtorType ty'
      Just (_, q) -> return (sp, ty', q)
  cty <- closeHere (length di.params) ty'
  modify (addItem n (CtorInfo (CtorGlobalInfo n cty idx q dat sp)) ts)
  modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal n]}))

primItem :: (Tc m) => Name -> Qty -> Set Tag -> Child m -> m ()
primItem n q ts ty = do
  ensureNewName n
  (ty', _) <- enterQty Zero $ ty (Check (VNorm VU))
  vty <- evalHere ty'
  modify (addItem n (PrimInfo (PrimGlobalInfo n q vty)) ts)

reprItem :: (Tc m) => Tel STm -> m VTy -> (Closure -> Set Tag -> Sig -> Sig) -> Set Tag -> Child m -> m STm
reprItem te getGlob addGlob ts r = do
  ty <- getGlob
  (r', _) <- enterTel te $ r (Check ty)
  vr <- closeHere (length te) r'
  modify (addGlob vr ts)
  return r'

reprDataItem :: (Tc m) => DataGlobal -> Set Tag -> Child m -> m (Tel STm)
reprDataItem dat ts c = do
  di <- access (getDataGlobal dat)
  tm <-
    enterQty Zero $
      reprItem
        Empty
        (reprHere 1 di.fullTy)
        (addDataRepr dat)
        ts
        c
  let (ls, _) = sGatherLams tm
  return (telWithNames di.params (toList $ fmap (\p -> p.name) ls))

reprCtorItem :: (Tc m) => Tel STm -> CtorGlobal -> Set Tag -> Child m -> m ()
reprCtorItem te ctor ts c = do
  ci <- access (getCtorGlobal ctor)
  _ <-
    reprItem
      te
      (evalInOwnCtxHere ci.ty >>= reprHere 1)
      (addCtorRepr ctor)
      ts
      c
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

spineForTel :: Int -> Tel STm -> Spine STm
spineForTel dist te =
  S.fromList $ zipWith (curry (\(Param m q _ _, i) -> Arg m q (SVar (Idx (dist + length te - i - 1))))) (toList te) [0 ..]

telWithUniqueNames :: (Tc m) => Tel a -> m (Tel a)
telWithUniqueNames = do
  mapM
    ( \(Param m q n a) -> do
        case n of
          Name "_" -> do
            n' <- uniqueName
            return (Param m q n' a)
          Name _ -> return (Param m q n a)
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

  let motiveTy = sPis (mTyIndicesBinds :|> Param Explicit Zero motiveSubjName (spToData (length mTyIndicesBinds) 0)) SU
  let subjSpToData = spToData (length mTyIndicesBinds + length methodTys + 1) 0

  let elimTy =
        sPis
          ( foldr
              (><)
              Empty
              [ S.singleton (Param Explicit Zero elimTyName motiveTy),
                S.fromList
                  ( zipWith
                      (\i (methodTy, methodName) -> Param Explicit Many methodName (methodTy i))
                      [0 ..]
                      methodTys
                  ),
                sTyIndicesBinds,
                S.singleton (Param Explicit Many subjectTyName subjSpToData)
              ]
          )
          (sAppSpine (SVar (Idx (1 + length sTyIndicesBinds + length methodTys))) (spineForTel 1 sTyIndicesBinds S.|> Arg Explicit Zero (SVar (Idx 0))))

  elimTy' <- closeHere (length datInfo.params) elimTy
  motiveTy' <- closeHere (length datInfo.params) motiveTy
  return (motiveTy', elimTy', fmap (\p -> Arg p.mode p.qty ()) sTyIndicesBinds)
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
                    S.take sTyParamLen sTyRetSp
                  )
              )
              (spineForTel 0 sTyBinds)
      n <- uniqueName
      return . (,n) $ \sMotiveIdx ->
        let methodRetTy =
              sAppSpine
                (SVar (Idx (sMotiveIdx + length sTyBinds)))
                (S.drop sTyParamLen sTyRetSp S.|> Arg Explicit Zero spToCtor)
         in sPis sTyBinds methodRetTy

global :: (Tc m) => Name -> GlobalInfo -> m (STm, VTy)
global n i = case i of
  DefInfo d -> do
    return (SDef (DefGlobal n), d.ty)
  DataInfo d -> do
    ty' <- evalHere $ sPis d.params d.ty.body
    return (SData (DataGlobal n), ty')
  CtorInfo c -> do
    di <- access (getDataGlobal c.dataGlobal)
    metas <- traverse (\p -> Arg p.mode p.qty <$> freshMeta p.qty) di.params
    vmetas <- mapSpineM evalHere metas
    ty' <- c.ty $$> vmetas
    return (SCtor (CtorGlobal n, metas), ty')
  PrimInfo p -> return (SPrim (PrimGlobal n), p.ty)

data UnifyError
  = DifferentSpineLengths (Spine VTm) (Spine VTm)
  | DifferentClauses [Clause VPatB Closure] [Clause VPatB Closure]
  | Mismatching VTm VTm
  | SolveError SolveError
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

-- Typeless and quantityless
enterTypelessClosure :: (Tc m) => [Qty] -> Closure -> m a -> m a
enterTypelessClosure qs c m = do
  ns <- uniqueNames c.numVars
  enterCtx (typelessBinds (zip qs ns)) m

invertSpine :: (Tc m) => Spine VTm -> SolveT m PRen
invertSpine Empty = do
  l <- lift getLvl
  return $ PRen (Lvl 0) l mempty
invertSpine s@(sp' :|> Arg _ q t) = do
  (PRen dom cod ren) <- invertSpine sp'
  f <- lift $ force t
  case f of
    VNeu (VVar (Lvl l')) | IM.notMember l' ren -> return $ PRen (nextLvl dom) cod (IM.insert l' (dom, q) ren)
    _ -> throwError $ InvertError s

renameSp :: (Tc m) => MetaVar -> PRen -> STm -> Spine VTm -> SolveT m STm
renameSp _ _ t Empty = return t
renameSp m pren t (sp :|> Arg i q u) = do
  xs <- renameSp m pren t sp
  ys <- rename m pren u
  return $ SApp i q xs ys

renameClosure :: (Tc m) => MetaVar -> PRen -> [Qty] -> Closure -> SolveT m STm
renameClosure m pren qs cl = do
  vt <- lift $ evalInOwnCtx pren.codSize cl
  rename m (liftPRenN qs pren) vt

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
  cs' <-
    mapM
      ( \(Clause p t) -> do
          p' <- renamePat m pren p
          t' <- traverse (renameClosure m pren (map fst p.binds)) t
          return $ Clause p' t'
      )
      cs
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
  VLet q x a t u -> do
    a' <- rename m pren a
    t' <- rename m pren t
    u' <- renameClosure m pren [q] u
    return $ SLet q x a' t' u'

renameNeu :: (Tc m) => MetaVar -> PRen -> VNeu -> SolveT m STm
renameNeu m pren (n, sp) = case n of
  VFlex m'
    | m == m' -> throwError $ OccursError m
    | otherwise -> renameSp m pren (SMeta m' []) sp
  VRigid (Lvl l) -> case IM.lookup l pren.vars of
    Nothing -> throwError EscapingVariable
    Just (x', _) -> renameSp m pren (SVar (lvlToIdx pren.domSize x')) sp
  VBlockedCase c -> renameCaseSpine renameNeu m pren c sp
  VPrim p -> renameSp m pren (SPrim p) sp
  VUnrepr n' -> renameReprSpine m pren (-1) (headAsValue n') sp

renameNorm :: (Tc m) => MetaVar -> PRen -> VNorm -> SolveT m STm
renameNorm m pren n = case n of
  VLam i q x t -> do
    t' <- renameClosure m pren [q] t
    return $ SLam i q x t'
  VPi i q x ty t -> do
    ty' <- rename m pren ty
    t' <- renameClosure m pren [q] t
    return $ SPi i q x ty' t'
  VU -> return SU
  VData (d, sp) -> renameSp m pren (SData d) sp
  VCtor ((c, pp), sp) -> do
    pp' <- mapSpineM (rename m pren) pp
    renameSp m pren (SCtor (c, pp')) sp

rename :: (Tc m) => MetaVar -> PRen -> VTm -> SolveT m STm
rename m pren tm = case tm of
  VNorm n -> renameNorm m pren n
  VLazy n -> renameLazy m pren n
  VNeu n -> renameNeu m pren n

unifySpines :: (Tc m) => Spine VTm -> Spine VTm -> m CanUnify
unifySpines Empty Empty = return Yes
unifySpines (sp :|> Arg _ q u) (sp' :|> Arg _ q' u') | q == q' = unifySpines sp sp' /\ enterQty q (unify u u')
unifySpines sp sp' = return $ No [DifferentSpineLengths sp sp']

unifyClauses :: (Tc m) => [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses [] [] = return Yes
unifyClauses (c : cs) (c' : cs') = unifyClause c c' /\ unifyClauses cs cs'
unifyClauses a b = return $ No [DifferentClauses a b]

unifyClause :: (Tc m) => Clause VPatB Closure -> Clause VPatB Closure -> m CanUnify
unifyClause (Possible p t) (Possible p' t') = unifyClosure (map fst p.binds) t (map fst p'.binds) t'
unifyClause (Impossible _) (Impossible _) = return Yes
unifyClause a b = return $ No [DifferentClauses [a] [b]]

data Problem = Problem
  { ctx :: Ctx,
    loc :: Loc,
    qty :: Qty,
    lhs :: VTm,
    rhs :: VTm,
    errs :: [UnifyError]
  }
  deriving (Show)

instance (Tc m) => Pretty m Problem where
  pretty (Problem ctx _ _ lhs rhs errs) = enterCtx (const ctx) $ do
    lhs' <- pretty lhs
    rhs' <- pretty rhs
    errs' <- intercalate ", " <$> mapM pretty errs
    return $ "lhs: " ++ lhs' ++ "\nrhs: " ++ rhs' ++ "\nerrors: " ++ errs'

addProblem :: (Tc m) => Problem -> m ()
addProblem p = modify (S.|> p)

addNewProblem :: (Tc m) => VTm -> VTm -> SolveError -> m ()
addNewProblem t t' e = do
  c <- getCtx
  q <- qty
  l <- view
  let p = Problem {ctx = c, qty = q, loc = l, lhs = t, rhs = t', errs = []}
  addProblem $ p {errs = [SolveError (WithProblem p e)]}

removeProblem :: (Tc m) => Int -> m ()
removeProblem i = modify (\(p :: Seq Problem) -> S.deleteAt i p)

getProblems :: (Tc m) => m (Seq Problem)
getProblems = view

enterProblem :: (Tc m) => Problem -> m a -> m a
enterProblem p = enterPat NotInPat . enterCtx (const p.ctx) . enterLoc p.loc . replaceQty p.qty

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
  solution <- lift $ uniqueSLams (reverse $ map (\a -> (a.mode, a.qty)) (toList sp)) rhs >>= eval []
  lift $ solveMetaVar m solution

unifyClosure :: (Tc m) => [Qty] -> Closure -> [Qty] -> Closure -> m CanUnify
unifyClosure qs1 cl1 qs2 cl2 = do
  l <- getLvl
  t1 <- evalInOwnCtx l cl1
  t2 <- evalInOwnCtx l cl2
  if cl1.numVars == cl2.numVars && all (uncurry (==)) (zip qs1 qs2)
    then enterTypelessClosure qs1 cl1 $ unify t1 t2
    else error "unifyClosure: different number of variables"

iDontKnow :: (Tc m) => m CanUnify
iDontKnow = return Maybe

unify :: (Tc m) => VTm -> VTm -> m CanUnify
unify t1 t2 = do
  t1' <- force t1
  t2' <- force t2
  unifyForced t1' t2'

etaConvert :: (Tc m) => VTm -> PiMode -> Qty -> Closure -> m CanUnify
etaConvert t m q c = do
  l <- getLvl
  x <- evalInOwnCtx l c
  x' <- vApp t (S.singleton (Arg m q (VNeu (VVar l))))
  enterTypelessClosure [q] c $ unify x x'

unifyForced :: (Tc m) => VTm -> VTm -> m CanUnify
unifyForced t1 t2 = case (t1, t2) of
  (VNorm (VLam m q _ c), VNorm (VLam m' q' _ c')) | m == m' -> unifyClosure [q] c [q'] c'
  (t, VNorm (VLam m' q' _ c')) -> etaConvert t m' q' c'
  (VNorm (VLam m q _ c), t) -> etaConvert t m q c
  (VNorm n1, VNorm n2) -> unifyNormRest n1 n2
  (VNeu (VFlex x, sp), VNeu (VFlex x', sp')) | x == x' -> unifySpines sp sp' \/ iDontKnow
  (VNeu (VFlex x, sp), _) -> unifyFlex x sp t2
  (_, VNeu (VFlex x', sp')) -> unifyFlex x' sp' t1
  (VNeu (VUnrepr c1, sp1), VNeu (VUnrepr c2, sp2)) -> unify (headAsValue c1) (headAsValue c2) /\ unifySpines sp1 sp2
  (_, VNeu (VUnrepr _, _)) -> do
    --- we actually need something more in the system to prove this??
    rt1 <- reprHere 1 t1
    rt2 <- reprHere 1 t2
    unify rt1 rt2
  (VNeu (VUnrepr _, _), _) -> do
    rt1 <- reprHere 1 t1
    rt2 <- reprHere 1 t2
    unify rt1 rt2
  (VNeu n1, VNeu n2) -> unifyNeuRest n1 n2
  (VLazy l1, VLazy l2) -> unifyLazy l1 l2
  (VLazy l, t) -> unifyLazyWithTermOr l t iDontKnow
  (t, VLazy l) -> unifyLazyWithTermOr l t iDontKnow
  _ -> return $ No [Mismatching t1 t2]

unifyNormRest :: (Tc m) => VNorm -> VNorm -> m CanUnify
unifyNormRest n1 n2 = case (n1, n2) of
  (VPi m q _ t c, VPi m' q' _ t' c') | m == m' -> unify t t' /\ unifyClosure [q] c [q'] c'
  (VU, VU) -> return Yes
  (VData (d, sp), VData (d', sp')) | d == d' -> unifySpines sp sp'
  (VCtor ((c, _), sp), VCtor ((c', _), sp'))
    | c == c' -> unifySpines sp sp'
  _ -> return $ No [Mismatching (VNorm n1) (VNorm n2)]

unifyLazy :: (Tc m) => VLazy -> VLazy -> m CanUnify
unifyLazy (n1, sp1) (n2, sp2) =
  ( ( case (n1, n2) of
        (VDef d1, VDef d2) | d1 == d2 -> return Yes
        (VLit l1, VLit l2) -> unifyLit l1 l2
        (VLazyCase c1, VLazyCase c2) -> unifyCases VLazy c1 c2
        (VLet q1 _ a1 t1 u1, VLet q2 _ a2 t2 u2) | q1 == q2 -> enterQty Zero (unify a1 a2) /\ enterQty q1 (unify t1 t2) /\ unifyClosure [q1] u1 [q2] u2
        (VRepr n1', VRepr n2') -> unify (headAsValue n1') (headAsValue n2')
        _ -> iDontKnow
    )
      /\ unifySpines sp1 sp2
  )
    \/ tryUnfold
  where
    tryUnfold = unifyLazyWithTermOr (n1, sp1) (VLazy (n2, sp2)) (unifyLazyWithTermOr (n2, sp2) (VLazy (n1, sp1)) iDontKnow)

unifyNeuRest :: (Tc m) => VNeu -> VNeu -> m CanUnify
unifyNeuRest (n1, sp1) (n2, sp2) = case (n1, n2) of
  (VRigid x, VRigid x') | x == x' -> do
    unifySpines sp1 sp2 \/ iDontKnow
  (VBlockedCase c1, VBlockedCase c2) -> unifyCases VNeu c1 c2 /\ unifySpines sp1 sp2
  (VPrim p1, VPrim p2) | p1 == p2 -> unifySpines sp1 sp2
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
