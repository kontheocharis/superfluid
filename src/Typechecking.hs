{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Use bimap" #-}
{-# HLINT ignore "Use first" #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

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
    Child,
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
    clauses,
  )
where

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
    Name (..),
    Param (..),
    Parent (..),
    PiMode (..),
    PrimGlobal (..),
    Qty (..),
    Spine,
    Tag (..),
    Tel,
    Try (..),
    enterLoc,
    lvlToIdx,
    mapSpineM,
    telToBinds,
    telWithNames,
    pattern Impossible,
    pattern Possible,
  )
import Constructions (ctorConstructions, ctorParamsClosure, dataConstructions, dataElimParamsClosure, dataFullVTy, dataMotiveParamsClosure)
import Context
import Control.Applicative (Alternative (empty), asum)
import Control.Monad (forM, unless)
import Control.Monad.Extra (fromMaybeM, when)
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable (Foldable (..), toList)
import Data.List (intercalate)
import Data.Map (Map)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Sequence (Seq (..), (><))
import qualified Data.Sequence as S
import Data.Set (Set)
import qualified Data.Set as SET
import Evaluation
  ( Eval (..),
    ensureIsCtor,
    ifIsData,
    isCtorTy,
    isTypeFamily,
    quote,
    vApp,
    ($$),
    ($$>),
  )
import Globals
  ( CtorConstructions (..),
    CtorGlobalInfo (..),
    DataConstructions (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    InstanceInfo (..),
    KnownGlobal (..),
    PrimGlobalInfo (..),
    Sig (..),
    addCaseRepr,
    addCtorRepr,
    addDataRepr,
    addDefRepr,
    addInstanceItem,
    addItem,
    dataIsIrrelevant,
    getCtorGlobal,
    getDataGlobal,
    getDefGlobal,
    hasName,
    knownData,
    lookupGlobal,
    modifyDataItem,
    modifyDefItem, instances,
  )
import Meta (freshMetaVar)
import Printing (Pretty (..), indentedFst)
import Substitution (Sub, Subst (..))
import Syntax
  ( Case (..),
    Closure (..),
    Env,
    HTel,
    HTm (..),
    HTy,
    SPat (..),
    STm (..),
    STy,
    VNeuHead (..),
    VNorm (..),
    VPatB (..),
    VTm (..),
    VTy,
    embed,
    embedCase,
    embedTel,
    extendTel,
    hApp,
    hLams,
    joinTels,
    sAppSpine,
    sGatherApps,
    sGatherLams,
    sGatherPis,
    sLams,
    unembed,
    uniqueSLams,
    vGetSpine,
    pattern VV, HCtx,
  )
import Unelaboration (Unelab)
import Unification
import Prelude hiding (pi)

data TcError
  = Mismatch [UnifyError]
  | PotentialMismatch VTm VTm
  | UnresolvedVariable Name
  | ImplicitMismatch PiMode PiMode
  | InvalidPattern
  | RemainingProblems [Problem]
  | ImpossibleCaseIsPossible VTm VTm
  -- | ImpossibleCaseMightBePossible VTm VTm Sub
  | ImpossibleCase VTm [UnifyError]
  | InvalidCaseSubject STm VTy
  | InvalidDataFamily VTy
  | InvalidCtorType STy
  | CannotSynthesizeType VTy [([Problem], STm, VTy)]
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
        CannotSynthesizeType t cs -> do
          t' <- pretty t
          cs' <-
            mapM
              ( \(_, a, b) -> do
                  a' <- pretty a
                  b' <- pretty b
                  return $ a' ++ " : " ++ b'
              )
              cs
          return $ "Cannot synthesize type: " <> t' <> "\nCandidates:\n" <> indentedFst (intercalate "\n" cs')
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
        -- ImpossibleCaseMightBePossible t1 t2 s -> do
        --   t1' <- pretty t1
        --   t2' <- pretty t2
        --   return undefined -- @@Todo
          -- sp <- pretty s
          -- s' <-
          --   if null sp
          --     then return ""
          --     else do
          --       return $ "\nThis could happen if " ++ sp
          -- return $ "Impossible case might be possible: " <> t1' <> " =? " <> t2' <> s'
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
    Parent m,
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

instance (Has m Ctx, Eval m, Tc m) => Unify m where
  onMetaFailed (MetaProblem m sp t) = addUnifyProblem (VNeu (VFlex m, sp)) t
  onMetaSolved (MetaProblem {}) = solveRemainingProblems

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

inferMeta :: (Tc m) => Maybe Name -> Qty -> m (STm, VTy)
inferMeta n q = do
  ty <- newMeta Nothing Zero
  vty <- evalHere ty
  checkMeta n vty q

prettyGoal :: (Tc m) => Goal -> m String
prettyGoal (Goal c n _ q ty) = enterCtx (const c) $ do
  c' <- getCtx >>= pretty
  ty' <- pretty ty
  let g = (if q /= Many then show q else "") ++ maybe "_" (\n' -> "?" ++ n'.unName) n ++ " : " ++ ty'
  return $ indentedFst c' ++ "\n" ++ replicate (length g + 4) '―' ++ "\n" ++ indentedFst g ++ "\n"

checkMeta :: (Tc m) => Maybe Name -> VTy -> Qty -> m (STm, VTy)
checkMeta n ty q = do
  m <- newMeta n q
  case n of
    Just _ -> do
      c <- getCtx
      addGoal (Goal c n m q ty)
    Nothing -> return ()
  return (m, ty)

newMeta :: (Tc m) => Maybe Name -> Qty -> m STm
newMeta n q = do
  bs <- accessCtx bounds
  m <- freshMetaVar n q
  return (SMeta m bs)

freshMeta :: (Tc m) => Qty -> m STm
freshMeta = newMeta Nothing

orPatBind :: (Tc m) => VTy -> m (STm, VTm) -> m (STm, VTm)
orPatBind ty f = do
  q <- qty
  ifInPat
    ( do
        n <- uniqueName
        (n', _) <- checkPatBind n ty
        vn <- evalPatHere (SPat n' [(q, n)])
        return (n', vn.vPat)
    )
    f

freshMetaOrPatBind :: (Tc m) => VTy -> m (STm, VTm)
freshMetaOrPatBind ty = orPatBind ty $ do
  q <- qty
  n' <- freshMeta q
  vn <- evalHere n'
  return (n', vn)

synthesizeOrPatBind :: (Tc m) => VTy -> m (STm, VTm)
synthesizeOrPatBind ty = do
  orPatBind ty $ do
    q <- qty
    n' <- freshMeta q
    vn <- evalHere n'
    synthesize (vn, ty)

insertFullRecord :: (Tc m) => (STm, VTy) -> m ([ProblemKind], STm, VTy)
insertFullRecord (tm, ty) = do
  f <- unfoldHere ty
  case f of
    VNorm (VPi m q _ a b) | m == Implicit || m == Instance -> do
      (v, vv) <- need q (freshMetaOrPatBind a)
      ty' <- b $$ [vv]
      (ps, tm'', ty'') <- insertFullRecord (SApp m q tm v, ty')
      case m of
        Instance -> return (Synthesize vv a : ps, tm'', ty'')
        _ -> return (ps, tm'', ty'')
    _ -> return ([], tm, ty)

insertFull :: (Tc m) => (STm, VTy) -> m (STm, VTy)
insertFull (tm, ty) = do
  f <- unfoldHere ty
  case f of
    VNorm (VPi Instance q _ a b) -> do
      (v, vv) <- need q (synthesizeOrPatBind a)
      ty' <- b $$ [vv]
      insertFull (SApp Instance q tm v, ty')
    VNorm (VPi Implicit q _ a b) -> do
      (v, vv) <- need q (freshMetaOrPatBind a)
      ty' <- b $$ [vv]
      insertFull (SApp Implicit q tm v, ty')
    _ -> return (tm, ty)

insert :: (Tc m) => (STm, VTy) -> m (STm, VTy)
insert (tm, ty) = case tm of
  SLam Implicit _ _ _ -> return (tm, ty)
  SLam Instance _ _ _ -> return (tm, ty)
  _ -> insertFull (tm, ty)

handleUnification :: (Tc m) => VTm -> VTm -> CanUnify -> m ()
handleUnification t1 t2 r = do
  p <- inPat
  case p of
    InImpossiblePat -> case r of
      Yes -> tcError $ ImpossibleCaseIsPossible t1 t2
      Maybe -> addUnifyProblem t1 t2 Blocking --  tcError $ ImpossibleCaseMightBePossible t1 t2 s
      No _ -> return ()
    InPossiblePat _ -> case r of
      Yes -> return ()
      Maybe -> addUnifyProblem t1 t2 Blocking -- applySubToCtx s
      No errs -> tcError $ ImpossibleCase t1 errs
    NotInPat -> case r of
      Yes -> return ()
      Maybe -> addUnifyProblem t1 t2 Blocking
      No errs -> tcError $ Mismatch errs

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
      b <- enterCtx (bind m x q a) (freshMeta Zero) >>= closeHere 1
      unifyHere ty (VNorm (VPi m q x a b))
      the m q x a b

unifyHere :: (Tc m) => VTm -> VTm -> m ()
unifyHere t1 t2 = do
  canUnifyHere t1 t2 >>= handleUnification t1 t2

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
  modifyCtx (bind Explicit x q ty)
  whenInPat
    ( \case
        InPossiblePat ns -> setInPat (InPossiblePat (ns ++ [(q, x)]))
        _ -> return ()
    )
  return (SVar (Idx 0), ty)

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

inPatNames :: InPat -> [(Qty, Name)]
inPatNames (InPossiblePat ns) = ns
inPatNames _ = []

lam :: (Tc m) => Mode -> PiMode -> Name -> Child m -> m (STm, VTy)
lam mode m x t = do
  forbidPat
  case mode of
    Check ty -> do
      ifForcePiType
        m
        ty
        ( \_ q x' a b -> do
            vb <- evalInOwnCtxHere b
            (t', _) <- enterCtx (bind m x q a) (t (Check vb))
            return (SLam m q x t', VNorm (VPi m q x' a b))
        )
        ( \m' q x' a b -> case m' of
            Implicit -> insertLam Implicit q x' a b (\s -> lam s m x t)
            Instance -> insertLam Instance q x' a b (\s -> lam s m x t)
            _ -> tcError $ ImplicitMismatch m m'
        )
    Infer -> do
      a <- freshMeta Zero >>= evalHere
      let q = Many
      (t', b) <- enterCtx (bind m x q a) $ t Infer >>= insert
      b' <- closeValHere 1 b
      return (SLam m q x t', VNorm (VPi m q x a b'))

insertLam :: (Tc m) => PiMode -> Qty -> Name -> VTy -> Closure -> Child m -> m (STm, VTy)
insertLam m q x' a b t = do
  vb <- evalInOwnCtxHere b
  (t', _) <- enterCtx (insertedBind m x' q a) (t (Check vb))
  return (SLam m q x' t', VNorm (VPi m q x' a b))

letIn :: (Tc m) => Mode -> Maybe Qty -> Name -> Child m -> Child m -> Child m -> m (STm, VTy)
letIn mode q x a t u = do
  forbidPat
  (a', _) <- expect Zero $ a (Check (VNorm VU))
  va <- evalHere a'
  q' <- fromMaybeM qty (return q)
  (t', _) <- expect q' $ t (Check va)
  vt <- evalHere t'
  (u', ty) <- enterCtx (define x q' vt va) $ u mode
  return (SLet q' x a' t' u', ty)

synthesize :: (Tc m) => (VTm, VTy) -> m (STm, VTy)
synthesize (tm, ty) =
  trySynthesize (tm, ty) >>= \case
    Right (v, vv) -> return (v, vv)
    Left _ -> do
      addSynthesizeProblem tm ty
      stm <- quoteHere tm
      return (stm, ty)

trySynthesize :: (Tc m) => (VTm, VTy) -> m (Either TcError (STm, VTy))
trySynthesize (tm, ty) = do
  linsts <- access localInstances
  insts <- access instances
  is <-
    findMatchingInstance
      ( map (\(i, t) -> (SVar i, t)) linsts
          ++ map (\(_, i) -> (SDef i.origin, i.ty)) insts
      )
  case is of
    [(ps, itm, ity')] -> do
      vitm <- evalHere itm
      unifyHere tm vitm
      unifyHere ty ity'
      mapM_ insertProblem ps >> solveRemainingProblems
      return $ Right (itm, ity')
    _ -> return $ Left (CannotSynthesizeType ty is)
  where
    findMatchingInstance :: (Tc m) => [(STm, VTy)] -> m [([Problem], STm, VTy)]
    findMatchingInstance [] = return []
    findMatchingInstance ((itm, ity) : rest) = do
      (ps, itm', ity') <- insertFullRecord (itm, ity)
      unification <- child . try $ do
        vitm' <- evalHere itm
        unifyHere tm vitm'
        unifyHere ty ity'
        ps' <- mapM (makeProblem []) ps
        mapM_ insertProblem ps' >> solveRemainingProblems
        return ps'
      is <- findMatchingInstance rest
      case unification of
        Right ps' -> do
          return $ (ps', itm', ity') : is
        Left _ -> return is

spine :: (Tc m) => (STm, VTy) -> Spine (Child m) -> m (STm, VTy)
spine (t, ty) Empty = return (t, ty)
spine (t, ty) (Arg m _ u :<| sp) = do
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Instance -> return (t, ty)
    Explicit -> insertFull (t, ty)
  ifForcePiType
    m
    ty'
    ( \_ q _ a b -> do
        (u', _) <- expect q $ u (Check a)
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
  (b', _) <- enterCtx (bind m x q av) $ b (Check (VNorm VU))
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

caseOf :: (Tc m) => Mode -> Child m -> Maybe (Child m) -> [Clause (Child m) (Child m)] -> m (STm, VTy)
caseOf mode s r cs = do
  forbidPat
  case mode of
    Infer -> do
      q <- qty
      retTy <- freshMeta q >>= evalHere
      caseOf (Check retTy) s r cs
    Check ty -> do
      (ss, ssTy) <- s Infer >>= insertFull
      (d, paramSp, indexSp, wideTyM) <- ensureDataAndGetWide ssTy (tcError $ InvalidCaseSubject ss ssTy)

      di <- access (getDataGlobal d)
      motive <- dataMotiveParamsClosure di
      motiveApplied <- motive $$> paramSp
      rr <- case r of
        Just r' -> expect Zero $ fst <$> r' (Check motiveApplied)
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

type ConstrainedClauses pat tm = [ConstrainedClause (Spine pat) tm]

type Clauses pat tm = [Clause (Spine pat) tm]

type ConstrainedClause pats tm = Clause (Constraints, pats) tm

type NextPat pat tm = (Maybe [pat], ConstrainedClauses pat tm) -- nonempty

nextPat :: (Tc m) => ConstrainedClauses pat tm -> m (NextPat pat tm)
nextPat = undefined

type Matches m = Map CtorGlobal [(Sub, [m (HTm, HTy)])]

equateSpines :: (Tc m) => Spine HTm -> Spine HTm -> m Sub
equateSpines = undefined

equateTerms :: (Tc m) => HTm -> HTm -> m Sub
equateTerms = undefined

getHoasEnv :: (Tc m) => m (Env HTm)
getHoasEnv = do
  es <- access ctxEntries
  return $ map (\e -> HVar e.lvl) es

unembedHere :: (Tc m) => STm -> m HTm
unembedHere t = do
  h <- getHoasEnv
  return $ unembed h t

embedHere :: (Tc m) => HTm -> m STm
embedHere t = do
  l <- getLvl
  return $ embed l t

enterSub :: (Tc m) => Sub -> m a -> m a
enterSub = undefined

class ApplySub m where
  applySub :: Sub -> m -> m

instance ApplySub VTm where
  applySub = undefined

instance (ApplySub a) => ApplySub (Spine a) where
  applySub = undefined

instance (ApplySub a, ApplySub b) => ApplySub (Clause a b) where
  applySub = undefined

binder :: (Has m Ctx) => PiMode -> Qty -> Name -> VTy -> (Lvl -> m a) -> m a
binder m q x a f = do
  l <- getLvl
  enterCtx (bind m x q a) $ f l

data Pat = LvlP Name Qty Lvl | CtorP (CtorGlobal, Spine VTm) (Spine Pat)

addVar :: (Tc m) => CaseElab -> m (Maybe STm)
addVar (CaseElab ctx ty cls) = do
  (ps, cls') <- nextPat cls
  case ps of
    Nothing -> return Nothing
    Just ps' -> do
      ty' <- unfoldHere ty
      case ty' of
        VNorm (VPi m q x a b) -> binder m q x a $ \l' -> do
          l <- getLvl
          b' <- b $$ [VV l']
          let cls'' = zipWith (\pt -> addConstraint $ Constraint l (VV l') pt (Param m q x a)) ps' cls'
          rest <- caseTree (CaseElab b' cls'')
          return . Just $ SLam m q x rest
        _ -> return Nothing

forceData :: (Tc m) => VTm -> m (DataGlobal, Spine HTm, Spine HTm)
forceData d = undefined

-- unifyPrfRelSp : (a : Tms Γ T) -> (b : Tms Γ T) -> (Γ' : Ctx) * (Γ' ~= Γ (a = b)) * m [enter Γ'] ()
unifyPrfRelSp :: (Tc m) => Spine HTm -> Spine HTm -> m ()
unifyPrfRelSp = undefined

unifyPrfRel :: (Tc m) => HTm -> HTm -> m ()
unifyPrfRel = undefined

canUnifyPrfRel :: (Tc m) => HTm -> HTm -> m CanUnify
canUnifyPrfRel = undefined

enterHTel :: (Tc m) => HTel -> (Spine HTm -> m a) -> m a
enterHTel = undefined

getDataGlobal' :: DataGlobal -> Sig -> (DataGlobalInfo, DataConstructions)
getDataGlobal' = undefined

getCtorGlobal' :: CtorGlobal -> Sig -> (CtorGlobalInfo, CtorConstructions)
getCtorGlobal' = undefined

eqTel :: Spine HTm -> Spine HTm -> HTel
eqTel = undefined

reflSp :: HTel -> Spine HTm -> Spine HTm
reflSp = undefined

patAsTm :: Pat -> HTm
patAsTm = undefined

tmAsPat :: HTm -> Pat
tmAsPat = undefined

runUnifyPL :: (Tc m, Unify n) => n a -> m a
runUnifyPL = undefined

splitConstraint :: (Tc m) => CaseElab -> m (Maybe STm)
splitConstraint (CaseElab ctx ty cls) = do
  -- Current context is:  Γχ (x : A)
  -- Rest of the goal is: Π xΓ T
  case cls of
    Clause (Constraints (co : cs), _) _ : clss -> case co of
      Constraint _ (VV x) (LvlP _ _ x') _ -> do
        -- We have that x = x'
        -- This will use the solution rule for the constraint x = x'
        (ctx', _, s) <- runUnifyPL $ unifyPL ctx (HVar x) (HVar x')
        Just <$> caseTree (CaseElab ctx' (sub s.forward ty) clss)
      Constraint _ (VV x) (CtorP _ _) param -> do
        -- We have that A = D δ ψ and x = ci πg

        -- Get the HOAS of the goal, i.e. Π xΓ T
        ty' <- quoteHere ty >>= unembedHere

        -- Get the current subject type, i.e. D δ ψ
        (d, delta, psi) <- forceData param.ty
        (di, dc) <- access (getDataGlobal' d)

        -- Create the spine (ψ, x)
        let psix = psi :|> Arg param.mode param.qty (HVar x)

        -- For each constructor ci (π : Πi [δ]) : D δ (ξi [δ,π]):
        elims <- forM di.ctors $ \c -> do
          (_, cc) <- access (getCtorGlobal' c)

          -- Enter the context of the constructor.
          enterHTel (cc.args delta) $ \pi -> do
            -- For each clause with pattern pj
            children <- fmap catMaybes . forM cls $ \cl' -> do
              case cl' of
                Clause (Constraints [], _) _ -> return Nothing
                Clause (Constraints (Constraint _ _ (LvlP _ _ p) _ : cs'), ps) t -> do
                  let cpat = tmAsPat (hApp (HCtor (c, delta)) pi)
                  newConstraint <- simpleConstraint (HVar p) cpat
                  return . Just $ Clause (Constraints (newConstraint : cs'), ps) t
                Clause (Constraints (Constraint _ _ (CtorP (cj, _) _) _ : _), _) _ | cj /= c -> return Nothing
                Clause (Constraints (Constraint _ _ (CtorP _ sp) _ : cs'), ps) t -> do
                  -- Current context is: Γχ (x : D δ ψ) (π : Πi)
                  -- equate pi to pj, gives back simple constraints.
                  -- give those constraints to make the child case clause j.
                  -- add this to matched clauses for i.
                  --
                  -- this constitutes a match for the constructor ci.
                  -- now to build the method for ci, call casetree recursively
                  -- with the configuration amended by the new constraints
                  newConstraints <- simpleConstraints pi sp
                  return . Just $ Clause (joinConstraints newConstraints (Constraints cs'), ps) t
            -- Create the spine (ξi[δ,π], ci π)
            let psix' = cc.returnIndices delta pi :|> Arg param.mode param.qty (hApp (HCtor (c, delta)) pi)

            -- Unify (ψ, x) with (ξi[δ,π], ci π), which will give back a new context Γ'
            -- that is isomorphic to
            --    Γχ (x : D δ ψ) (π : Πi) ((ψ, x) = (ξi[δ,π], ci π))
            -- through the substitution σ.
            (ctx', _, s) <- runUnifyPL $ unifyPLSpines ctx psix psix'
            -- @@Todo: do we care about status?

            -- Build the rest of the clause, which will first give:
            --    Γ' |- e' : (Π xΓ T) σ
            -- This is refined by specialisation by unification to:
            --    Γχ (x : D δ ψ) (π : Πi) ((ψ, x) = (ξi[δ,π], ci π)) |- e : Π xΓ T
            -- @@Todo: We need to apply sub to children too, and perhaps move xΓ to the context?
            e <- caseTree (CaseElab ctx' (sub s.forward ty) children)

            -- @@Todo: We need to substitute over propositional K somewhere around here..
            --
            -- Now we build e'' which is:
            --    Γχ (x : D δ ψ) (π : Πi) |- e'' : Π ((ψ, x) = (ξi[δ,π], ci π)) (Π xΓ T)
            -- The equalities are explicitly given by the motive we will set up later.
            eq <- here (`embedTel` eqTel psix psix')
            let e'' = sLams eq e

            -- The method is for constructor ci π
            pt <- here (`embed` hApp (HCtor (c, delta)) pi)
            let spt = SPat pt (telToBinds cc.argsArity)
            return (Clause spt (Just e''))

        -- Now we build the motive for the case.
        -- First, we have the required data indices and subject:
        --    (ψ' : Ψ[δ]) (x' : D δ ψ')
        let psixTe' = extendTel (dc.indices delta) (\psi' -> param {ty = hApp (HData d) (delta <> psi')})
        -- We also add the equalities between the subject and the data indices
        -- in the motive and the ones in the context.
        --    (ψ' : Ψ[δ]) (x' : D δ ψ') ((ψ, x) = (ψ', x'))
        let eq = eqTel psix
        let indTel = joinTels psixTe' eq

        -- We also need the reflexivity proofs to apply to the motive.
        --    refl [ψj] : Equal [Ψj] ψj ψj
        -- Where ψj = ψ1, ..., ψn, x
        psixRefl <- mapSpineM embedHere $ reflSp psixTe' psix

        caseBase <- here $ \lv ->
          embedCase lv $
            Case
              { dat = d,
                datParams = delta,
                subject = HVar x,
                subjectIndices = psi,
                -- The final motive is:
                --    Γχ (x : D δ ψ)  |-   λ ψ' x'. Π ((ψ, x) = (ψ', x'), xΓ) T   :   Π (ψ' : Ψ[δ], x' : D δ ψ') U
                elimTy = hLams indTel (const ty'),
                clauses = []
              }
        return . Just $ sAppSpine (SCase (caseBase {clauses = elims})) psixRefl
      _ -> return Nothing
    _ -> return Nothing

joinConstraints :: Constraints -> Constraints -> Constraints
joinConstraints = undefined

simpleConstraints :: Spine HTm -> Spine Pat -> m Constraints
simpleConstraints = undefined

simpleConstraint :: HTm -> Pat -> m Constraint
simpleConstraint = undefined

--
-- ty' <- unfoldHere ty
-- case ty' of
--   VNorm (VPi m q x a b) -> do
--     l' <- getLvl
--     ifIsData
--       l'
--       a
--       ( \d sp -> do
--           dsp <- traverse (traverse (quoteHere >=> unembedHere)) sp
--           di <- access (getDataGlobal d)
--           let dpp = S.take (length di.params) dsp
--           let dix = S.drop (length di.params) dsp
--           let matches = Map.fromList $ map (,[]) di.ctors
--           res <-
--             foldM
--               ( \acc (c, csp) -> case c of
--                   SCtor (c', pp) -> do
--                     ci' <- access (getCtorGlobal c')
--                     let cc = fromJust ci'.constructions
--                     let susp = binder m q x a $ \l -> do
--                           b' <- b $$ [VV l]
--                           caseTree b' cls'
--                           return $ SLam m q x rest
--                     return $ Map.adjust (++ [susp]) c' acc
--                   SVar i -> do
--                     l' <- here (`idxToLvl` i)
--                     mapM_
--                       ( \c' -> do
--                           ci' <- access (getCtorGlobal c')
--                           let cc = fromJust ci'.constructions
--                           let susp = binder m q x a $ \l -> do
--                                 csp' <- traverse (traverse unembedHere) csp
--                                 hcpp <- traverse (traverse unembedHere) pp
--                                 s <-
--                                   equateSpines hcpp dpp
--                                     <> equateSpines (cc.returnIndices hcpp csp') dix
--                                     <> equateTerms (hApp (HCtor (c', hcpp)) csp') (HVar l)
--                                 enterSub s $ do
--                                   b' <- b $$ [VV l]
--                                   rest <- caseTree b' cls'
--                                   return $ SLam m q x <$> rest
--                           return $ Map.adjust (++ [susp]) c' acc
--                       )
--                       di.ctors
--                     return acc
--                   _ -> tcError $ InvalidPattern
--               )
--               matches
--               ps'
--           return undefined
--       )
--       (throwError InvalidPattern)
--   _ -> throwError InvalidPattern

data Constraint = Constraint {lvl :: Lvl, lhs :: VTm, rhs :: Pat, param :: Param VTy}

data Constraints = Constraints {list :: [Constraint]}

emptyConstraints :: Constraints
emptyConstraints = Constraints []

addConstraint :: Constraint -> ConstrainedClause (Spine Pat) STm -> ConstrainedClause (Spine Pat) STm
addConstraint c (Clause (Constraints cs, sp) t) = Clause (Constraints (c : cs), sp) t

nextConstraint :: Constraints -> Maybe (Constraint, Constraints)
nextConstraint (Constraints []) = Nothing

-- CaseElab : (Γ : Ctx) -> Set
-- Operating in State Ctx
data CaseElab = CaseElab
  {
    ctx :: HCtx,
    ty :: VTy,
    cls :: [Clause (Constraints, Spine Pat) STm]
  }

-- split
caseTree :: (Tc m) => CaseElab -> m STm
caseTree c = do
  res <- asum <$> sequence [addVar c, splitConstraint c]
  case res of
    Just r -> return r
    Nothing -> error "no case tree tactic matched"

toPat :: (Tc m) => STm -> m Pat
toPat = undefined

clause :: (Tc m) => (STm, VTy) -> Clause (Spine (Child m)) (Child m) -> m (Clause (Spine Pat) STm)
clause (_, ty) (Possible Empty t) = do
  (t', _) <- t (Check ty)
  return $ Possible Empty t'
clause _ (Impossible Empty) = return $ Impossible Empty
clause (tm, ty) (Possible ps t) = do
  (ret, retTy) <- enterPat (InPossiblePat []) $ spine (tm, ty) ps
  (t', _) <- t (Check retTy)
  let (_, sp) = sGatherApps ret
  spp <- mapSpineM toPat sp
  return $ Possible spp t'
clause _ (Impossible _) = do
  return undefined -- @@Todo
  -- (ret, retTy) <- enterPat (InPossiblePat []) $ spine (tm, ty) ps

clausesWithEmptyConstraints :: Clauses a b -> ConstrainedClauses a b
clausesWithEmptyConstraints = map (bimap (emptyConstraints,) id)

clauses :: (Tc m) => DefGlobal -> Clauses (Child m) (Child m) -> VTy -> m (STm, VTy)
clauses d cls ty = enterCtx id $ do
  -- Strategy:
  -- - First we typecheck each clause
  -- - Then we turn to case tree
  -- - Invariant: in empty ctx
  cls' <- mapM (clause (SDef d, ty)) cls
  ct <- caseTree (CaseElab ty (clausesWithEmptyConstraints cls'))
  return (ct, ty)

defItem :: (Tc m) => Maybe Qty -> Name -> Set Tag -> Child m -> Clauses (Child m) (Child m) -> m ()
defItem mq n ts ty cl = do
  ensureNewName n
  let q = fromMaybe Many mq
  (ty', _) <- expect Zero $ ty (Check (VNorm VU))
  vty <- evalHere ty'
  modify (addItem n (DefInfo (DefGlobalInfo n q vty Nothing Nothing)) ts)
  (tm', _) <- expect q $ clauses (DefGlobal n) cl vty

  vtm <- evalHere tm'
  b <- normaliseProgram
  stm <- if b then quote (Lvl 0) vtm else return tm'

  -- Instances
  when (InstanceTag `SET.member` ts) $ do
    let inst = InstanceInfo (DefGlobal n) vty
    modify (addInstanceItem vty inst)

  modify (modifyDefItem (DefGlobal n) (\d -> d {tm = Just stm, vtm = Just vtm}))
  return ()

tel :: (Tc m) => Tel (Child m) -> m (Tel STy)
tel Empty = return Empty
tel (t :<| ts) = do
  (t', _) <- expect Zero $ t.ty (Check (VNorm VU))
  vt <- evalHere t'
  ts' <- enterCtx (bind t.mode t.name t.qty vt) $ tel ts
  return (Param t.mode t.qty t.name t' :<| ts')

dataItem :: (Tc m) => Name -> Set Tag -> Tel (Child m) -> Child m -> m ()
dataItem n ts te ty = do
  ensureNewName n
  te' <- tel te
  ty' <- enterTel te' $ do
    (ty', _) <- expect Zero $ ty (Check (VNorm VU))
    vty <- evalHere ty'
    i <- getLvl >>= (`isTypeFamily` vty)
    unless i (tcError $ InvalidDataFamily vty)
    return ty'
  modify
    ( addItem
        n
        ( DataInfo
            ( DataGlobalInfo
                { name = n,
                  params = te',
                  familyTy = ty',
                  ctors = [],
                  constructions = Nothing
                }
            )
        )
        ts
    )

endDataItem :: (Tc m) => DataGlobal -> m ()
endDataItem dat = do
  di <- access (getDataGlobal dat)
  cs <- dataConstructions di
  modify (modifyDataItem dat (\d -> d {constructions = Just cs}))

ctorItem :: (Tc m) => DataGlobal -> Name -> Maybe Qty -> Set Tag -> Child m -> m ()
ctorItem dat n mq ts ty = do
  let q' = fromMaybe Many mq
  di <- access (getDataGlobal dat)
  idx <- access (\s -> length (getDataGlobal dat s).ctors)
  (ty', q) <- enterTel di.params $ do
    ensureNewName n
    (ty', _) <- expect Zero $ ty (Check (VNorm VU))
    vty <- evalHere ty'
    i <- getLvl >>= (\l -> isCtorTy l dat vty)
    case i of
      Nothing -> tcError $ InvalidCtorType ty'
      Just (_, q) -> do
        ty'' <- unfoldHere vty >>= quoteHere
        return (ty'', q)
  let ci =
        CtorGlobalInfo
          { name = n,
            qty = q',
            ty = ty',
            index = idx,
            qtySum = q,
            dataGlobal = dat,
            constructions = Nothing
          }
  constructions <- ctorConstructions ci
  modify (addItem n (CtorInfo (ci {constructions = Just constructions})) ts)
  modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal n]}))

primItem :: (Tc m) => Name -> Maybe Qty -> Set Tag -> Child m -> m ()
primItem n mq ts ty = do
  ensureNewName n
  let q = fromMaybe Many mq
  (ty', _) <- expect Zero $ ty (Check (VNorm VU))
  vty <- evalHere ty'
  modify (addItem n (PrimInfo (PrimGlobalInfo n q vty)) ts)

reprItem :: (Tc m) => Qty -> Tel STm -> m VTy -> (Closure -> Set Tag -> Sig -> Sig) -> Set Tag -> Child m -> m STm
reprItem q te getGlob addGlob ts r = expect q $ do
  ty <- getGlob
  (r', _) <- enterTel te $ r (Check ty)
  vr <- closeHere (length te) r'
  modify (addGlob vr ts)
  return r'

reprDataItem :: (Tc m) => DataGlobal -> Set Tag -> Child m -> m (Tel STm)
reprDataItem dat ts c = do
  di <- access (getDataGlobal dat)
  tm <-
    reprItem
      Zero
      Empty
      (dataFullVTy di >>= reprHere 1)
      (addDataRepr dat)
      ts
      c
  let (ls, _) = sGatherLams tm
  return (telWithNames di.params (toList $ fmap (\p -> p.name) ls))

reprCtorItem :: (Tc m) => Tel STm -> CtorGlobal -> Set Tag -> Child m -> m ()
reprCtorItem te ctor ts c = do
  ci <- access (getCtorGlobal ctor)
  irr <- access (dataIsIrrelevant ci.dataGlobal)
  _ <-
    reprItem
      (if irr then Zero else Many)
      te
      (ctorParamsClosure ci >>= evalInOwnCtxHere >>= reprHere 1)
      (addCtorRepr ctor)
      ts
      c
  return ()

reprDefItem :: (Tc m) => DefGlobal -> Set Tag -> Child m -> m ()
reprDefItem def ts c = do
  di <- access (getDefGlobal def)
  _ <- reprItem di.qty Empty (return di.ty) (addDefRepr def) ts c
  return ()

reprCaseItem :: (Tc m) => Tel STm -> DataGlobal -> Set Tag -> Child m -> m ()
reprCaseItem te dat ts c = do
  di <- access (getDataGlobal dat)
  _ <-
    reprItem
      Many
      te
      (dataElimParamsClosure di >>= evalInOwnCtxHere)
      (addCaseRepr dat)
      ts
      c
  return ()

instantiateTel :: (Tc m) => Tel a -> m (Spine STm, Spine VTm)
instantiateTel Empty = return (Empty, Empty)
instantiateTel (Param m q _ _ :<| ts) = do
  mta <- freshMeta q
  mtas <- instantiateTel ts
  vmta <- evalHere mta
  return (Arg m q mta :<| fst mtas, Arg m q vmta :<| snd mtas)

global :: (Tc m) => Name -> GlobalInfo -> m (STm, VTy)
global n i = case i of
  DefInfo d -> do
    return (SDef (DefGlobal n), d.ty)
  DataInfo d -> do
    ty' <- dataFullVTy d
    return (SData (DataGlobal n), ty')
  CtorInfo c -> do
    di <- access (getDataGlobal c.dataGlobal)
    (metas, vmetas) <- instantiateTel di.params
    tyCl <- ctorParamsClosure c
    ty' <- tyCl $$> vmetas
    return (SCtor (CtorGlobal n, metas), ty')
  PrimInfo p -> return (SPrim (PrimGlobal n), p.ty)
data ProblemKind = Unify VTm VTm | Synthesize VTm VTy deriving (Show)

data Problem = Problem
  { ctx :: Ctx,
    qty :: Qty,
    loc :: Loc,
    kind :: ProblemKind,
    errs :: [UnifyError]
  }
  deriving (Show)

instance (Tc m) => Pretty m Problem where
  pretty (Problem ctx _ _ (Unify lhs rhs) errs) = enterCtx (const ctx) $ do
    lhs' <- pretty lhs
    rhs' <- pretty rhs
    errs' <- intercalate ", " <$> mapM pretty errs
    return $ "unify lhs: " ++ lhs' ++ "\rhs: " ++ rhs' ++ "\nerrors: " ++ errs'
  pretty (Problem ctx _ _ (Synthesize t ty) errs) = enterCtx (const ctx) $ do
    t' <- pretty t
    ty' <- pretty ty
    errs' <- intercalate ", " <$> mapM pretty errs
    return $ "synthesize term: " ++ t' ++ "\ntype: " ++ ty' ++ "\nerrors: " ++ errs'

addProblem :: (Tc m) => [UnifyError] -> ProblemKind -> m ()
addProblem err k = makeProblem err k >>= insertProblem

insertProblem :: (Tc m) => Problem -> m ()
insertProblem p = modify (:|> p)

makeProblem :: (Tc m) => [UnifyError] -> ProblemKind -> m Problem
makeProblem err k = do
  q <- qty
  c <- getCtx
  l <- view
  return $ Problem {qty = q, ctx = c, loc = l, kind = k, errs = err}

synthesizeProblem :: (Tc m) => VTm -> VTy -> m Problem
synthesizeProblem t ty = do
  q <- qty
  c <- getCtx
  l <- view
  return $ Problem {qty = q, ctx = c, loc = l, kind = Synthesize t ty, errs = []}

addSynthesizeProblem :: (Tc m) => VTm -> VTy -> m ()
addSynthesizeProblem t ty = addProblem [] $ Synthesize t ty

addUnifyProblem :: (Tc m) => VTm -> VTm -> SolveError -> m ()
addUnifyProblem t t' e = do addProblem [SolveError e] $ Unify t t'

removeProblem :: (Tc m) => Int -> m ()
removeProblem i = modify (\(p :: Seq Problem) -> S.deleteAt i p)

getProblems :: (Tc m) => m (Seq Problem)
getProblems = view

enterProblem :: (Tc m) => Problem -> m a -> m a
enterProblem p = enterCtx (const p.ctx) . enterLoc p.loc

data SolveAttempts = SolveAttempts Int | InSolveAttempts Int

solveRemainingProblems :: (Tc m) => m ()
solveRemainingProblems = do
  att <- view
  case att of
    InSolveAttempts _ -> return ()
    SolveAttempts n -> enter (const (InSolveAttempts n)) $ solveRemainingProblems' n
  where
    solveRemainingProblems' :: (Tc m) => Int -> m ()
    solveRemainingProblems' 0 = return ()
    solveRemainingProblems' n = do
      ps <- getProblems
      if null ps
        then return ()
        else do
          _ <-
            S.traverseWithIndex
              ( \i p -> enterProblem p $
                  case p.kind of
                    Unify lhs rhs -> do
                      lhs' <- resolveHere lhs
                      rhs' <- resolveHere rhs
                      u <- child . try $ canUnifyHere lhs' rhs'
                      case u of
                        Right Yes -> do
                          unifyHere lhs' rhs'
                          removeProblem i
                        _ -> return ()
                    Synthesize t ty -> do
                      t' <- resolveHere t
                      ty' <- resolveHere ty
                      s <- child . try $ trySynthesize (t', ty')
                      case s of
                        Right (Right (_, _)) -> do
                          _ <- synthesize (t', ty')
                          removeProblem i
                        _ -> return ()
              )
              ps
          solveRemainingProblems' (n - 1)
