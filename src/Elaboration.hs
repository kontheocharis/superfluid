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
import Common (Arg (..), Clause (..), CtorGlobal (..), DataGlobal (..), DefGlobal (..), Glob (..), Has (..), HasNameSupply (..), HasProjectFiles, Idx (..), Lit (..), Loc (NoLoc), Lvl (..), MetaVar, Modify (modify), Name (..), PiMode (..), Spine, Tag, Times, View (..), globName, inv, lvlToIdx, mapSpine, nextLvl, nextLvls, pat, unMetaVar, pattern Impossible, pattern Possible)
import Control.Monad (unless, zipWithM, zipWithM_)
import Control.Monad.Extra (when)
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
import Data.Set (Set)
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
    getDataGlobal,
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
  | InvalidPattern
  | InvalidNonPattern
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
        InvalidPattern -> do
          return "Invalid in pattern position"
        InvalidNonPattern -> do
          return "Invalid in non-pattern position"
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

ifForcePiType :: (Elab m) => PiMode -> VTy -> (PiMode -> Name -> VTy -> Closure -> m a) -> (PiMode -> Name -> VTy -> Closure -> m a) -> m a
ifForcePiType m ty the els = do
  ty' <- force ty
  case ty' of
    VPi m' x a b -> do
      if m == m'
        then the m' x a b
        else els m' x a b
    _ -> do
      a <- freshMetaHere >>= evalHere
      x <- uniqueName
      b <- enterCtx (bind x a) freshMetaHere >>= closeHere 1
      unifyHere ty (VPi m x a b)
      the m x a b

forbidPat :: (Elab m) => m ()
forbidPat = ifInPat (elabError InvalidPattern) (return ())

ensurePat :: (Elab m) => m ()
ensurePat = ifInPat (return ()) (elabError InvalidPattern)

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
  when r $ elabError $ DuplicateItem n

getLvl :: (Elab m) => m Lvl
getLvl = accessCtx (\c -> c.lvl)

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
            _ -> elabError $ ImplicitMismatch m m'
        )
    Infer -> do
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
  forbidPat
  (a', _) <- a (Check VU)
  va <- evalHere a'
  (t', _) <- t (Check va)
  vt <- evalHere t'
  (u', ty) <- enterCtx (define x vt va) $ u mode
  return (SLet x a' t' u', ty)

spine :: (Elab m) => (STm, VTy) -> Spine (Child m) -> m (STm, VTy)
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
    (\m' _ _ _ -> elabError $ ImplicitMismatch m m')

app :: (Elab m) => Child m -> Spine (Child m) -> m (STm, VTy)
app s sp = do
  (s', sTy) <- s Infer
  spine (s', sTy) sp

univ :: (Elab m) => m (STm, VTy)
univ = do
  forbidPat
  return (SU, VU)

piTy :: (Elab m) => PiMode -> Name -> Child m -> Child m -> m (STm, VTy)
piTy m x a b = do
  forbidPat
  (a', _) <- a (Check VU)
  av <- evalHere a'
  (b', _) <- enterCtx (bind x av) $ b (Check VU)
  return (SPi m x a' b', VU)

repr :: (Elab m) => Mode -> Times -> Child m -> m (STm, VTy)
repr mode m t = do
  forbidPat
  case mode of
    Check ty@(VNeu (VRepr m' t')) | m == m' -> do
      (tc, _) <- t (Check (VNeu (VHead t')))
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

pat :: (Elab m) => InPat -> Child m -> (SPat -> VTy -> m ()) -> (SPat -> VTy -> m a) -> m a
pat inPt pt runInsidePatScope runOutsidePatScope = enterCtx id $ do
  (p', t, ns) <- enterPat inPt $ do
    (p', t') <- pt Infer >>= insert
    ns <- inPatNames <$> inPat
    runInsidePatScope (SPat p' ns) t'
    return (p', t', ns)
  runOutsidePatScope (SPat p' ns) t

matchPat :: (Elab m) => VTm -> VTy -> SPat -> VTy -> m ()
matchPat vs ssTy sp spTy = do
  vp <- evalPatHere sp
  u <- canUnifyHere ssTy spTy /\ canUnifyHere vp.vPat vs
  handleUnification vp.vPat vs u

caseOf :: (Elab m) => Mode -> Child m -> [Clause (Child m) (Child m)] -> m (STm, VTy)
caseOf mode s cs = do
  forbidPat
  case mode of
    Infer -> do
      retTy <- freshMetaHere >>= evalHere
      caseOf (Check retTy) s cs
    Check ty -> do
      (ss, ssTy) <- s Infer
      d <- ifIsData ssTy return (elabError $ InvalidCaseSubject ss ssTy)
      vs <- evalHere ss
      scs <-
        mapM
          ( \case
              Possible p t -> pat (InPossiblePat []) p (matchPat vs ssTy) $ \sp _ -> do
                (st, _) <- t (Check ty)
                return $ Possible sp st
              Impossible p -> pat InImpossiblePat p (matchPat vs ssTy) $ \sp _ -> do
                return $ Impossible sp
          )
          cs
      return (SCase d ss scs, ty)

meta :: (Elab m) => Mode -> Maybe Name -> m (STm, VTy)
meta mode n = do
  forbidPat
  case mode of
    Infer -> inferMetaHere n
    Check ty -> do
      m <- checkMetaHere n ty
      return (m, ty)

lit :: (Elab m) => Mode -> Lit (Child m) -> m (STm, VTy)
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

defItem :: (Elab m) => Name -> Set Tag -> Child m -> Child m -> m ()
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

dataItem :: (Elab m) => Name -> Set Tag -> Child m -> m ()
dataItem n ts ty = do
  ensureNewName n
  (ty', _) <- ty (Check VU)
  vty <- evalHere ty'
  i <- getLvl >>= (`isTypeFamily` vty)
  unless i (elabError $ InvalidDataFamily vty)
  modify (addItem n (DataInfo (DataGlobalInfo vty [])) ts)

ctorItem :: (Elab m) => DataGlobal -> Name -> Set Tag -> Child m -> m ()
ctorItem dat n ts ty = do
  ensureNewName n
  idx <- access (\s -> length (getDataGlobal dat s).ctors)
  (ty', _) <- ty (Check VU)
  vty <- evalHere ty'
  i <- getLvl >>= (\l -> isCtorTy l dat vty)
  unless i (elabError $ InvalidCtorType vty)
  modify (addItem n (CtorInfo (CtorGlobalInfo vty idx dat)) ts)
  modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal n]}))

-- Presyntax exists below here

pKnownCtor :: KnownGlobal CtorGlobal -> [PTm] -> PTm
pKnownCtor k ts = pApp (PName (knownCtor k).globalName) (map (Arg Explicit) ts)

pKnownData :: KnownGlobal DataGlobal -> [PTm] -> PTm
pKnownData d ts = pApp (PName (knownData d).globalName) (map (Arg Explicit) ts)

elab :: (Elab m) => PTm -> Mode -> m (STm, VTy)
elab p Infer = infer p
elab p (Check ty) = check p ty

checkEval :: (Elab m) => PTm -> VTy -> m (VTm, VTy)
checkEval p ty = do
  (t, ty') <- check p ty
  v <- evalHere t
  return (v, ty')

check :: (Elab m) => PTm -> VTy -> m (STm, VTy)
check term typ = do
  typ' <- force typ
  case (term, typ') of
    (PLocated l t, ty) -> enterLoc l (check t ty)
    (PLam m x t, ty) -> lam (Check ty) m x (elab t)
    (t, VPi Implicit x' a b) -> insertLam x' a b (elab t)
    (PUnit, ty@VU) -> check (pKnownData KnownUnit []) ty
    (PUnit, ty) -> check (pKnownCtor KnownTt []) ty
    (PLet x a t u, ty) -> letIn (Check ty) x (elab a) (elab t) (elab u)
    (PRepr m t, ty) -> repr (Check ty) m (elab t)
    (PHole n, ty) -> meta (Check ty) (Just n)
    (PWild, ty) ->
      ifInPat
        (wildPat (Check ty))
        (meta (Check ty) Nothing)
    (PLambdaCase cs, ty) -> do
      n <- uniqueName
      check (PLam Explicit n (PCase (PName n) cs)) ty
    (PCase s cs, ty) -> caseOf (Check ty) (elab s) (map (bimap elab elab) cs)
    (te, ty) -> checkByInfer (infer te) ty

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterLoc l $ infer t
  PName x -> name x
  PSigma x a b -> infer $ pKnownData KnownSigma [a, PLam Explicit x b]
  PUnit -> infer $ pKnownData KnownUnit []
  PPair t1 t2 -> infer $ pKnownCtor KnownPair [t1, t2]
  PLam m x t -> lam Infer m x (elab t)
  PApp {} -> do
    let (s, sp) = toPSpine term
    app (elab s) (mapSpine elab sp)
  PU -> univ
  PPi m x a b -> piTy m x (elab a) (elab b)
  PLet x a t u -> letIn Infer x (elab a) (elab t) (elab u)
  PRepr m x -> repr Infer m (elab x)
  PHole n -> meta Infer (Just n)
  PWild ->
    ifInPat
      (wildPat Infer)
      (meta Infer Nothing)
  PLambdaCase cs -> do
    n <- uniqueName
    infer $ PLam Explicit n (PCase (PName n) cs)
  PCase s cs -> caseOf Infer (elab s) (map (bimap elab elab) cs)
  PLit l -> lit Infer (fmap elab l)

checkDef :: (Elab m) => PDef -> m ()
checkDef def = defItem def.name def.tags (elab def.ty) (elab def.tm)

checkCtor :: (Elab m) => DataGlobal -> PCtor -> m ()
checkCtor dat ctor = ctorItem dat ctor.name ctor.tags (elab ctor.ty)

checkData :: (Elab m) => PData -> m ()
checkData dat = do
  dataItem dat.name dat.tags (elab dat.ty)
  mapM_ (checkCtor (DataGlobal dat.name)) dat.ctors

checkPrim :: (Elab m) => PPrim -> m ()
checkPrim prim = do
  ensureNewName prim.name
  (ty', _) <- checkEval prim.ty VU
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
