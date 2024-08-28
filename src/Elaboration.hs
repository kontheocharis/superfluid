{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Elaboration
  ( Elab (..),
    ElabError (..),
    Ctx (..),
    emptyCtx,
    infer,
    checkProgram,
    check,
    InPat (..),
  )
where

import Algebra.Lattice ((/\))
import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (..),
    Glob (..),
    Has (..),
    HasNameSupply (..),
    HasProjectFiles,
    Idx (..),
    Lit (..),
    Loc (NoLoc),
    Lvl (..),
    MetaVar,
    Modify (modify),
    Name (..),
    PiMode (..),
    Spine,
    Times,
    View (..),
    globName,
    inv,
    lvlToIdx,
    mapSpine,
    nextLvl,
    nextLvls,
    pat,
    unMetaVar,
    pattern Impossible,
    pattern Possible,
  )
import Control.Monad (unless, zipWithM, zipWithM_)
import Control.Monad.Trans (MonadTrans (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Foldable (Foldable (..))
import qualified Data.IntMap as IM
import Data.Kind (Constraint)
import Data.List (intercalate, zipWith4, zipWith5)
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Debug.Trace (traceM, traceStack)
import Evaluation
  ( Eval (..),
    close,
    eval,
    evalInOwnCtx,
    evalPat,
    force,
    ifIsData,
    isCtorTy,
    isTypeFamily,
    quote,
    resolve,
    unelab,
    vApp,
    vRepr,
    ($$),
  )
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    KnownGlobal (..),
    PrimGlobalInfo (PrimGlobalInfo),
    addItem,
    globalInfoToTm,
    hasName,
    knownCtor,
    knownData,
    lookupGlobal,
    modifyDataItem,
    modifyDefItem,
  )
import Meta (freshMetaVar, lookupMetaVarName)
import Presyntax (PCtor (..), PData (..), PDef (..), PItem (..), PPat, PPrim (..), PProgram (..), PTm (..), PTy, pApp)
import Printing (Pretty (..), indented, indentedFst)
import Syntax (BoundState (Bound, Defined), Bounds, SPat (..), STm (..), toPSpine)
import Unification
  ( CanUnify (..),
    Problem (Problem),
    SolveError (..),
    Unify (),
    UnifyError (..),
    getProblems,
    loc,
    prevErrorString,
    unify,
    unifyErrorIsMetaRelated,
  )
import Value
  ( Closure (..),
    Env,
    Sub,
    VHead (..),
    VNeu (..),
    VPatB (..),
    VTm (..),
    VTy,
    isEmptySub,
    vars,
    pattern VGlob,
    pattern VHead,
    pattern VRepr,
    pattern VVar,
  )

data ElabError
  = Mismatch [UnifyError]
  | PotentialMismatch VTm VTm
  | UnresolvedVariable Name
  | ImplicitMismatch PiMode PiMode
  | InvalidPattern PTm
  | RemainingProblems [(UnifyError, Loc)]
  | ImpossibleCaseIsPossible VTm VTm
  | ImpossibleCaseMightBePossible VTm VTm Sub
  | ImpossibleCase VTm [UnifyError]
  | InvalidCaseSubject STm VTy
  | InvalidDataFamily VTy
  | InvalidCtorType VTy
  | DuplicateItem Name
  | Chain [ElabError]

data InPat = NotInPat | InPossiblePat [Name] | InImpossiblePat deriving (Eq)

instance (HasProjectFiles m, Elab m) => Pretty m ElabError where
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
        InvalidPattern p -> do
          p' <- pretty p
          return $ "Invalid pattern: " <> p'
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
        RemainingProblems ps -> do
          ps' <-
            mapM
              ( \(l, c) -> do
                  l' <- pretty l
                  c' <- pretty c
                  return $ c' ++ "\n" ++ l'
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

class (Eval m, Unify m, Has m Loc, Has m InPat, Has m Ctx) => Elab m where
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

  elabError :: ElabError -> m a
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

data Ctx = Ctx
  { env :: Env VTm,
    lvl :: Lvl,
    types :: [VTy],
    bounds :: Bounds,
    nameList :: [Name],
    names :: Map Name Lvl
  }

instance (Elab m) => View m [Name] where
  view = accessCtx (\c -> c.nameList)

instance (Elab m) => Modify m [Name] where
  modify f = modifyCtx (\c -> c {nameList = f c.nameList})

instance (Elab m) => Has m [Name]

instance (Elab m) => View m Lvl where
  view = accessCtx (\c -> c.lvl)

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
      con :: [(Name, VTy, Maybe VTm)]
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

ensureAllProblemsSolved :: (Elab m) => m ()
ensureAllProblemsSolved = do
  ps <- getProblems
  if S.null ps
    then return ()
    else do
      let ps' = fmap (\p -> (PrevError p.prevErrorString, p.loc)) ps
      elabError $ RemainingProblems (toList ps')

applySubToCtx :: (Elab m) => Sub -> m ()
applySubToCtx sub = do
  c <- getCtx
  let (env', bounds', ss) = replaceVars (c.lvl.unLvl - 1) (c.env, c.bounds)
  modifyCtx $ \(c' :: Ctx) -> c' {env = env', bounds = bounds'}
  sequence_ ss
  where
    replaceVars :: (Elab m) => Int -> (Env VTm, Bounds) -> (Env VTm, Bounds, [m ()])
    replaceVars _ ([], []) = ([], [], [])
    replaceVars startingAt (v : vs, b : bs) =
      let (vs', bs', ss) = replaceVars (startingAt - 1) (vs, bs)
       in let res = IM.lookup startingAt sub.vars
           in case res of
                Nothing -> (v : vs', b : bs', ss)
                Just v' ->
                  ( NE.head v' : vs',
                    Defined : bs',
                    ss
                      ++ map (unifyHere v) (NE.toList v')
                  )
    replaceVars _ _ = error "impossible"

bind :: Name -> VTy -> Ctx -> Ctx
bind x ty ctx =
  ctx
    { env = VNeu (VVar ctx.lvl) : ctx.env,
      lvl = nextLvl ctx.lvl,
      types = ty : ctx.types,
      bounds = Bound : ctx.bounds,
      names = M.insert x ctx.lvl ctx.names,
      nameList = x : ctx.nameList
    }

insertedBind :: Name -> VTy -> Ctx -> Ctx
insertedBind = bind

define :: Name -> VTm -> VTy -> Ctx -> Ctx
define x t ty ctx =
  ctx
    { env = t : ctx.env,
      lvl = nextLvl ctx.lvl,
      types = ty : ctx.types,
      bounds = Defined : ctx.bounds,
      names = M.insert x ctx.lvl ctx.names,
      nameList = x : ctx.nameList
    }

lookupName :: Name -> Ctx -> Maybe (Idx, VTy)
lookupName n ctx = case M.lookup n ctx.names of
  Just l -> let idx = lvlToIdx ctx.lvl l in Just (idx, ctx.types !! idx.unIdx)
  Nothing -> Nothing

inferMetaHere :: (Elab m) => Maybe Name -> m (STm, VTy)
inferMetaHere n = do
  ty <- newMetaHere Nothing
  vty <- evalHere ty
  m <- checkMetaHere n vty
  return (m, vty)

prettyGoal :: (Elab m) => STm -> VTy -> m String
prettyGoal n ty = do
  c <- getCtx >>= pretty
  n' <- pretty n
  ty' <- pretty ty
  let g = n' ++ " : " ++ ty'
  return $ indentedFst c ++ "\n" ++ replicate (length g + 4) '―' ++ "\n" ++ indentedFst g ++ "\n"

checkMetaHere :: (Elab m) => Maybe Name -> VTy -> m STm
checkMetaHere n ty = do
  m <- newMetaHere n
  case n of
    Just _ -> prettyGoal m ty >>= showMessage
    Nothing -> return ()
  return m

newMetaHere :: (Elab m) => Maybe Name -> m STm
newMetaHere n = do
  bs <- accessCtx (\c -> c.bounds)
  m <- freshMetaVar n
  return (SMeta m bs)

freshMetaHere :: (Elab m) => m STm
freshMetaHere = newMetaHere Nothing

freshMetaOrPatBind :: (Elab m) => m (STm, VTm)
freshMetaOrPatBind =
  ifInPat
    ( do
        n <- uniqueName
        (n', _) <- inferPatBind n
        vn <- evalPatHere (SPat n' [n])
        return (n', vn.vPat)
    )
    ( do
        n' <- freshMetaHere
        vn <- evalHere n'
        return (n', vn)
    )

insertFull :: (Elab m) => (STm, VTy) -> m (STm, VTy)
insertFull (tm, ty) = do
  f <- force ty
  case f of
    VPi Implicit _ _ b -> do
      (a, va) <- freshMetaOrPatBind
      ty' <- b $$ [va]
      insertFull (SApp Implicit tm a, ty')
    _ -> return (tm, ty)

insert :: (Elab m) => (STm, VTy) -> m (STm, VTy)
insert (tm, ty) = case tm of
  SLam Implicit _ _ -> return (tm, ty)
  _ -> insertFull (tm, ty)

evalHere :: (Elab m) => STm -> m VTm
evalHere t = do
  e <- accessCtx (\c -> c.env)
  eval e t

evalPatHere :: (Elab m) => SPat -> m VPatB
evalPatHere t = do
  e <- accessCtx (\c -> c.env)
  evalPat e t

handleUnification :: (Elab m) => VTm -> VTm -> CanUnify -> m ()
handleUnification t1 t2 r = do
  p <- inPat
  case p of
    InImpossiblePat -> case r of
      Yes -> elabError $ ImpossibleCaseIsPossible t1 t2
      Maybe s -> elabError $ ImpossibleCaseMightBePossible t1 t2 s
      No errs | not $ any unifyErrorIsMetaRelated errs -> return ()
      No errs -> elabError $ Mismatch errs
    InPossiblePat _ -> case r of
      Yes -> return ()
      Maybe s -> applySubToCtx s
      No errs -> elabError $ ImpossibleCase t1 errs
    NotInPat -> case r of
      Yes -> return ()
      Maybe _ -> elabError $ PotentialMismatch t1 t2
      No errs -> elabError $ Mismatch errs

canUnifyHere :: (Elab m) => VTm -> VTm -> m CanUnify
canUnifyHere t1 t2 = do
  l <- accessCtx (\c -> c.lvl)
  t1' <- resolveHere t1
  t2' <- resolveHere t2
  unify l t1' t2'

resolveHere :: (Elab m) => VTm -> m VTm
resolveHere t = do
  l <- accessCtx (\c -> c.env)
  resolve l t

unifyHere :: (Elab m) => VTm -> VTm -> m ()
unifyHere t1 t2 = do
  canUnifyHere t1 t2 >>= handleUnification t1 t2

closeValHere :: (Elab m) => Int -> VTm -> m Closure
closeValHere n t = do
  (l, e) <- accessCtx (\c -> (c.lvl, c.env))
  t' <- quote (nextLvls l n) t
  close n e t'

closeHere :: (Elab m) => Int -> STm -> m Closure
closeHere n t = do
  e <- accessCtx (\c -> c.env)
  close n e t

forcePiType :: (Elab m) => PiMode -> VTy -> m (VTy, Closure)
forcePiType m ty = do
  ty' <- force ty
  case ty' of
    VPi m' _ a b -> do
      if m == m'
        then return (a, b)
        else elabError $ ImplicitMismatch m m'
    _ -> do
      a <- freshMetaHere >>= evalHere
      v <- uniqueName
      b <- enterCtx (bind v a) freshMetaHere >>= closeHere 1
      unifyHere ty (VPi m v a b)
      return (a, b)

forbidPat :: (Elab m) => PTm -> m ()
forbidPat p = ifInPat (elabError $ InvalidPattern p) (return ())

inferPatBind :: (Elab m) => Name -> m (STm, VTy)
inferPatBind x = do
  ty <- freshMetaHere >>= evalHere
  x' <- checkPatBind x ty
  return (x', ty)

checkPatBind :: (Elab m) => Name -> VTy -> m STm
checkPatBind x ty = do
  modifyCtx (bind x ty)
  whenInPat
    ( \case
        InPossiblePat ns -> setInPat (InPossiblePat (ns ++ [x]))
        _ -> return ()
    )
  return $ SVar (Idx 0)

reprHere :: (Elab m) => Times -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

name :: (Elab m) => Name -> m (STm, VTy)
name n =
  ifInPat
    ( do
        l <- access (lookupGlobal n)
        case l of
          Just c@(CtorInfo _) -> return (globalInfoToTm n c)
          _ -> inferPatBind n
    )
    ( do
        r <- accessCtx (lookupName n)
        case r of
          Just (i, t) -> return (SVar i, t)
          Nothing -> do
            l <- access (lookupGlobal n)
            case l of
              Just x -> return (globalInfoToTm n x)
              Nothing -> elabError $ UnresolvedVariable n
    )

ensureNewName :: (Elab m) => Name -> m ()
ensureNewName n = do
  r <- access (hasName n)
  if r
    then elabError $ DuplicateItem n
    else return ()

checkDef :: (Elab m) => PDef -> m ()
checkDef def = do
  ensureNewName def.name
  ty' <- check def.ty VU >>= evalHere
  modify (addItem def.name (DefInfo (DefGlobalInfo ty' Nothing Nothing)) def.tags)
  tm' <- check def.tm ty'
  vtm <- evalHere tm'
  b <- normaliseProgram
  stm <- if b then quote (Lvl 0) vtm else return tm'
  modify (modifyDefItem (DefGlobal def.name) (\d -> d {tm = Just stm, vtm = Just vtm}))
  return ()

checkCtor :: (Elab m) => DataGlobal -> Int -> PCtor -> m ()
checkCtor dat idx ctor = do
  ensureNewName ctor.name
  ty' <- check ctor.ty VU >>= evalHere
  i <- getLvl >>= (\l -> isCtorTy l dat ty')
  unless i (elabError $ InvalidCtorType ty')
  modify (addItem ctor.name (CtorInfo (CtorGlobalInfo ty' idx dat)) ctor.tags)
  modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal ctor.name]}))

getLvl :: (Elab m) => m Lvl
getLvl = accessCtx (\c -> c.lvl)

checkData :: (Elab m) => PData -> m ()
checkData dat = do
  ensureNewName dat.name
  ty' <- check dat.ty VU >>= evalHere
  i <- getLvl >>= (`isTypeFamily` ty')
  unless i (elabError $ InvalidDataFamily ty')
  modify (addItem dat.name (DataInfo (DataGlobalInfo ty' [])) dat.tags)
  zipWithM_ (checkCtor (DataGlobal dat.name)) [0 ..] dat.ctors

checkPrim :: (Elab m) => PPrim -> m ()
checkPrim prim = do
  ensureNewName prim.name
  ty' <- check prim.ty VU >>= evalHere
  modify (addItem prim.name (PrimInfo (PrimGlobalInfo ty')) prim.tags)
  return ()

checkItem :: (Elab m) => PItem -> m ()
checkItem i = do
  r <- case i of
    PDef def -> checkDef def
    PData dat -> checkData dat
    PPrim prim -> checkPrim prim
    PDataRep {} -> return () -- @@Todo
    PDefRep {} -> return () -- @@Todo
    PLocatedItem l i' -> enterLoc l $ checkItem i'
  ensureAllProblemsSolved
  return r

checkProgram :: (Elab m) => PProgram -> m ()
checkProgram (PProgram items) = mapM_ checkItem items

inPatNames :: InPat -> [Name]
inPatNames (InPossiblePat ns) = ns
inPatNames _ = []

evalInOwnCtxHere :: (Elab m) => Closure -> m VTm
evalInOwnCtxHere t = do
  l <- accessCtx (\c -> c.lvl)
  evalInOwnCtx l t

data Mode = Check VTy | Infer

type Child m = (Mode -> m (STm, VTy))

lam :: (Elab m) => Mode -> PiMode -> Name -> Child m -> m (STm, VTy)
lam (Check (VPi m' x' a b)) m x t | m == m' = do
  vb <- evalInOwnCtxHere b
  (t', _) <- enterCtx (bind x a) (t (Check vb))
  return (SLam m x t', VPi m' x' a b)
lam Infer m x t = do
  a <- freshMetaHere >>= evalHere
  (t', b) <- enterCtx (bind x a) $ t Infer >>= insert
  b' <- closeValHere 1 b
  return (SLam m x t', VPi m x a b')

insertLam :: (Elab m) => Name -> VTy -> Closure -> Child m -> m (STm, VTy)
insertLam x' a b t = do
  vb <- evalInOwnCtxHere b
  (t', _) <- enterCtx (insertedBind x' a) (t (Check vb))
  return (SLam Implicit x' t', VPi Implicit x' a b)

letIn :: (Elab m) => Mode -> Name -> Child m -> Child m -> Child m -> m (STm, VTy)
letIn mode x a t u = do
  (a', _) <- a (Check VU)
  va <- evalHere a'
  (t', _) <- t (Check va)
  vt <- evalHere t'
  (u', ty) <- enterCtx (define x vt va) $ u mode
  return (SLet x a' t' u', ty)

checkSpine :: (Elab m) => (STm, VTy) -> Spine (Child m) -> m (STm, VTy)
checkSpine (t, ty) Empty = return (t, ty)
checkSpine (t, ty) (Arg m u :<| sp) = do
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Explicit -> insertFull (t, ty)
    Instance -> error "unimplemented"
  (a, b) <- forcePiType m ty'
  (u', _) <- u (Check a)
  uv <- evalHere u'
  b' <- b $$ [uv]
  checkSpine (SApp m t' u', b') sp

app :: (Elab m) => Child m -> Spine (Child m) -> m (STm, VTy)
app s sp = do
  (s', sTy) <- s Infer
  checkSpine (s', sTy) sp

univ :: (Elab m) => m (STm, VTy)
univ = return (SU, VU)

piTy :: (Elab m) => PiMode -> Name -> Child m -> Child m -> m (STm, VTy)
piTy m x a b = do
  (a', _) <- a (Check VU)
  av <- evalHere a'
  (b', _) <- enterCtx (bind x av) $ b (Check VU)
  return (SPi m x a' b', VU)

-- check' :: (Elab m) => PTm -> VTy -> m (STm, VTy)
-- check' term typ = do
--   term' <- check term typ
--   return (term', typ)

repr :: (Elab m) => Mode -> Times -> Child m -> m (STm, VTy)
repr (Check ty@(VNeu (VRepr m' t'))) m t | m == m' = do
  (tc, _) <- t (Check (VNeu (VHead t')))
  return (SRepr m tc, ty)
repr (Check ty) m t | m < mempty = do
  (t', ty') <- t Infer >>= insert
  reprTy <- reprHere (inv m) ty
  unifyHere reprTy ty'
  return (SRepr m t', ty)
repr (Check ty) m t = checkByInfer (repr Infer m t) ty
repr Infer m t = do
  (t', ty) <- t Infer
  reprTy <- reprHere m ty
  return (SRepr m t', reprTy)

checkByInfer :: (Elab m) => m (STm, VTy) -> VTy -> m (STm, VTy)
checkByInfer t ty = do
  (t', ty') <- t >>= insert
  unifyHere ty ty'
  return (t', ty)

wildPat :: (Elab m) => Mode -> m (STm, VTy)
wildPat (Check ty) = do
  n <- uniqueName
  n' <- checkPatBind n ty
  return (n', ty)
wildPat Infer = uniqueName >>= inferPatBind

pat :: (Elab m) => Mode -> InPat -> Child m -> (SPat -> VTy -> m a) -> m a
pat m o p f = enterCtx id $ do
  (p', t, ns) <- enterPat o $ do
    (p', t') <- p m
    ns <- inPatNames <$> inPat
    return (p', t', ns)
  f (SPat p' ns) t

matchPat :: (Elab m) => (SPat, VTy) -> (STm, VTy) -> m ()
matchPat (sp, spTy) (ss, ssTy) = do
  vs <- evalHere ss
  vp <- evalPatHere sp
  u <- canUnifyHere ssTy spTy /\ canUnifyHere vp.vPat vs
  handleUnification vp.vPat vs u

caseOf :: (Elab m) => Mode -> Child m -> [Clause (Child m) (Child m)] -> m (STm, VTy)
caseOf Infer s cs = do
  retTy <- freshMetaHere >>= evalHere
  caseOf (Check retTy) s cs
caseOf (Check ty) s cs = do
  (ss, ssTy) <- s Infer >>= insert
  d <- ifIsData ssTy return (elabError $ InvalidCaseSubject ss ssTy)
  scs <-
    mapM
      ( \case
          Possible p t -> pat Infer (InPossiblePat []) p $ \sp spTy -> do
            matchPat (sp, spTy) (ss, ssTy)
            (st, _) <- t (Check ty)
            return $ Possible sp st
          Impossible p -> pat Infer InImpossiblePat p $ \sp spTy -> do
            matchPat (sp, spTy) (ss, ssTy)
            return $ Impossible sp
      )
      cs
  return (SCase d ss scs, ty)

meta :: (Elab m) => Mode -> Maybe Name -> m (STm, VTy)
meta Infer n = inferMetaHere n
meta (Check ty) n = do
  m <- checkMetaHere n ty
  return (m, ty)

lit :: (Elab m) => Mode -> Lit (Child m) -> m (STm, VTy)
lit (Check ty) l = checkByInfer (lit Infer l) ty
lit Infer l = do
  (l', ty, args) <- case l of
    StringLit s -> return (StringLit s, KnownString, Empty)
    CharLit c -> return (CharLit c, KnownChar, Empty)
    NatLit n -> return (NatLit n, KnownNat, Empty)
    FinLit f bound -> do
      (bound', _) <- bound (Check (VGlob (DataGlob (knownData KnownNat)) Empty))
      vbound' <- evalHere bound'
      return (FinLit f bound', KnownFin, S.singleton (Arg Explicit vbound'))
  return (SLit l', VGlob (DataGlob (knownData ty)) args)

-- Presyntax exists below here

pKnownCtor :: KnownGlobal CtorGlobal -> [PTm] -> PTm
pKnownCtor k ts = pApp (PName (knownCtor k).globalName) (map (Arg Explicit) ts)

pKnownData :: KnownGlobal DataGlobal -> [PTm] -> PTm
pKnownData d ts = pApp (PName (knownData d).globalName) (map (Arg Explicit) ts)

elab :: (Elab m) => PTm -> Mode -> m (STm, VTy)
elab p Infer = infer p
elab p (Check ty) = check p ty

check :: (Elab m) => PTm -> VTy -> m (STm, VTy)
check term typ = do
  typ' <- force typ
  case (term, typ') of
    (PLocated l t, ty) -> enterLoc l (check t ty)
    (PLam m x t, VPi m' x' a b) | m == m' -> do
      forbidPat term
      lam (Check (VPi m' x' a b)) m x (elab t)
    (t, VPi Implicit x' a b) -> do
      insertLam x' a b (elab t)
    (PUnit, ty@VU) -> check (pKnownData KnownUnit []) ty
    (PUnit, ty) -> check (pKnownCtor KnownTt []) ty
    (PLet x a t u, ty) -> do
      forbidPat term
      letIn (Check ty) x (elab a) (elab t) (elab u)
    (PRepr m t, ty) -> do
      forbidPat term
      repr (Check ty) m (elab t)
    (PHole n, ty) -> do
      forbidPat term
      meta (Check ty) (Just n)
    (PWild, ty) ->
      ifInPat
        (wildPat (Check ty))
        (meta (Check ty) Nothing)
    (PLambdaCase cs, ty) -> do
      n <- uniqueName
      check (PLam Explicit n (PCase (PName n) cs)) ty
    (PCase s cs, ty) -> do
      caseOf (Check ty) (elab s) (map (bimap elab elab) cs)
    (te, ty) -> checkByInfer (infer te) ty

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterLoc l $ infer t
  PName x -> name x
  PSigma x a b -> infer $ pKnownData KnownSigma [a, PLam Explicit x b]
  PUnit -> infer $ pKnownData KnownUnit []
  PPair t1 t2 -> infer $ pKnownCtor KnownPair [t1, t2]
  PLam m x t -> do
    forbidPat term
    lam Infer m x (elab t)
  PApp {} -> do
    let (s, sp) = toPSpine term
    app (elab s) (mapSpine elab sp)
  PU -> forbidPat term >> univ
  PPi m x a b -> do
    forbidPat term
    piTy m x (elab a) (elab b)
  PLet x a t u -> do
    forbidPat term
    letIn Infer x (elab a) (elab t) (elab u)
  PRepr m x -> do
    forbidPat term
    repr Infer m (elab x)
  PHole n -> do
    forbidPat term
    meta Infer (Just n)
  PWild ->
    ifInPat
      (wildPat Infer)
      (meta Infer Nothing)
  PLambdaCase cs -> do
    n <- uniqueName
    infer $ PLam Explicit n (PCase (PName n) cs)
  PCase s cs -> do
    forbidPat term
    caseOf Infer (elab s) (map (bimap elab elab) cs)
  PLit l -> lit Infer (fmap elab l)
