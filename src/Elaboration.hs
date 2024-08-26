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
    nextLvl,
    nextLvls,
    pat,
    unMetaVar,
    pattern Impossible,
    pattern Possible,
  )
import Control.Monad (unless, zipWithM, zipWithM_)
import Control.Monad.Trans (MonadTrans (..))
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
import Unification (CanUnify (..), Unify (), UnifyError, unify, unifyErrorIsMetaRelated)
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
  | ImpossibleCaseIsPossible VTm VTm
  | ImpossibleCaseMightBePossible VTm VTm Sub
  | ImpossibleCase VTm [UnifyError]
  | InvalidCaseSubject PTm VTy
  | InvalidDataFamily VTy
  | InvalidCtorType VTy
  | DuplicateItem Name
  | Chain [ElabError]

data InPat = NotInPat | InPossiblePat [Name] | InImpossiblePat

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

pop :: Ctx -> Ctx
pop = popN 1

popN :: Int -> Ctx -> Ctx
popN 0 ctx = ctx
popN n ctx =
  ctx
    { env = drop n ctx.env,
      lvl = Lvl (ctx.lvl.unLvl - n),
      types = drop n ctx.types,
      bounds = drop n ctx.bounds,
      names = M.fromList $ zip (drop n ctx.nameList) (map Lvl [0 ..]),
      nameList = drop n ctx.nameList
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
unifyHere t1 t2 = canUnifyHere t1 t2 >>= handleUnification t1 t2

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

checkSpine :: (Elab m) => (STm, VTy) -> Spine PTm -> m (STm, VTy)
checkSpine (t, ty) Empty = return (t, ty)
checkSpine (t, ty) (Arg m u :<| sp) = do
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Explicit -> insertFull (t, ty)
    Instance -> error "unimplemented"
  (a, b) <- forcePiType m ty'
  u' <- check u a
  uv <- evalHere u'
  b' <- b $$ [uv]
  checkSpine (SApp m t' u', b') sp

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

ifIsData :: (Elab m) => VTy -> (DataGlobal -> m a) -> m a -> m a
ifIsData v a b = do
  v' <- force v
  case v' of
    VGlob (DataGlob g@(DataGlobal _)) _ -> a g
    _ -> b

reprHere :: (Elab m) => Times -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

inferName :: (Elab m) => Name -> m (STm, VTy)
inferName n =
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

checkDef :: (Elab m) => PDef -> m ()
checkDef def = do
  ty' <- check def.ty VU >>= evalHere
  modify (addItem def.name (DefInfo (DefGlobalInfo ty' Nothing)) def.tags)
  tm' <- check def.tm ty' >>= evalHere
  modify (modifyDefItem (DefGlobal def.name) (\d -> d {tm = Just tm'}))
  return ()

checkCtor :: (Elab m) => DataGlobal -> Int -> PCtor -> m ()
checkCtor dat idx ctor = do
  ty' <- check ctor.ty VU >>= evalHere
  i <- getLvl >>= (\l -> isCtorTy l dat ty')
  unless i (elabError $ InvalidCtorType ty')
  modify (addItem ctor.name (CtorInfo (CtorGlobalInfo ty' idx dat)) ctor.tags)
  modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal ctor.name]}))

getLvl :: (Elab m) => m Lvl
getLvl = accessCtx (\c -> c.lvl)

checkData :: (Elab m) => PData -> m ()
checkData dat = do
  ty' <- check dat.ty VU >>= evalHere
  i <- getLvl >>= (`isTypeFamily` ty')
  unless i (elabError $ InvalidDataFamily ty')
  modify (addItem dat.name (DataInfo (DataGlobalInfo ty' [])) dat.tags)
  zipWithM_ (checkCtor (DataGlobal dat.name)) [0 ..] dat.ctors

checkPrim :: (Elab m) => PPrim -> m ()
checkPrim prim = do
  ty' <- check prim.ty VU >>= evalHere
  modify (addItem prim.name (PrimInfo (PrimGlobalInfo ty')) prim.tags)
  return ()

checkItem :: (Elab m) => PItem -> m ()
checkItem = \case
  PDef def -> checkDef def
  PData dat -> checkData dat
  PPrim prim -> checkPrim prim
  PDataRep {} -> return () -- @@Todo
  PDefRep {} -> return () -- @@Todo
  PLocatedItem l i -> enterLoc l $ checkItem i

checkProgram :: (Elab m) => PProgram -> m ()
checkProgram (PProgram items) = mapM_ checkItem items

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterLoc l $ infer t
  PName x -> inferName x
  PSigma x a b ->
    infer $
      pApp
        (PName (knownData KnownSigma).globalName)
        [Arg Explicit a, Arg Explicit (PLam Explicit x b)]
  PPair t1 t2 ->
    infer $
      pApp (PName (knownCtor KnownPair).globalName) [Arg Explicit t1, Arg Explicit t2]
  PLam m x t -> do
    forbidPat term
    a <- freshMetaHere >>= evalHere
    (t', b) <- enterCtx (bind x a) $ infer t >>= insert
    b' <- closeValHere 1 b
    return (SLam m x t', VPi m x a b')
  PApp {} -> do
    let (subject, sp) = toPSpine term
    (s, sTy) <- infer subject
    checkSpine (s, sTy) sp
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
    return (SLet x a' t' u', b)
  PRepr m x -> do
    forbidPat term
    (x', ty) <- infer x
    reprTy <- reprHere m ty
    return (SRepr m x', reprTy)
  PHole n -> do
    forbidPat term
    inferMetaHere (Just n)
  PWild ->
    ifInPat
      (uniqueName >>= inferPatBind)
      (inferMetaHere Nothing)
  PCase s cs -> do
    forbidPat term
    retTy <- freshMetaHere >>= evalHere
    c <- checkCase s cs retTy
    return (c, retTy)
  PLit l -> do
    (l', ty, args) <- case l of
      StringLit s -> return (StringLit s, KnownString, Empty)
      CharLit c -> return (CharLit c, KnownChar, Empty)
      NatLit n -> return (NatLit n, KnownNat, Empty)
      FinLit f bound -> do
        bound' <- check bound (VGlob (DataGlob (knownData KnownNat)) Empty)
        vbound' <- evalHere bound'
        return (FinLit f bound', KnownFin, S.singleton (Arg Explicit vbound'))
    return (SLit l', VGlob (DataGlob (knownData ty)) args)

checkCase :: (Elab m) => PTm -> [Clause PTm PTm] -> VTy -> m STm
checkCase s cs retTy = do
  (ss, vsTy) <- infer s
  vs <- evalHere ss
  d <- ifIsData vsTy return (elabError $ InvalidCaseSubject s vsTy)
  scs <-
    mapM
      ( \c -> enterCtx id $ case c of
          Possible p t -> do
            sp <- enterPat (InPossiblePat []) $ checkPatAgainstSubject p vs vsTy
            st <- check t retTy
            return $ Possible sp st
          Impossible p -> do
            sp <- enterPat InImpossiblePat $ checkPatAgainstSubject p vs vsTy
            return $ Impossible sp
      )
      cs
  return (SCase d ss scs)

inPatNames :: InPat -> [Name]
inPatNames (InPossiblePat ns) = ns
inPatNames _ = []

checkPatAgainstSubject :: (Elab m) => PPat -> VTm -> VTy -> m SPat
checkPatAgainstSubject p vs vsTy = do
  (sp, spTy) <- infer p >>= insert
  ns <- inPatNames <$> inPat
  a <- canUnifyHere vsTy spTy
  vp <- evalPatHere (SPat sp ns)
  b <- canUnifyHere vp.vPat vs
  handleUnification vp.vPat vs (a /\ b)
  return $ SPat sp ns

evalInOwnCtxHere :: (Elab m) => Closure -> m VTm
evalInOwnCtxHere t = do
  l <- accessCtx (\c -> c.lvl)
  evalInOwnCtx l t

check :: (Elab m) => PTm -> VTy -> m STm
check term typ = do
  typ' <- force typ
  case (term, typ') of
    (PLocated l t, ty) -> enterLoc l $ check t ty
    (PLam m x t, VPi m' _ a b) | m == m' -> do
      forbidPat term
      vb <- evalInOwnCtxHere b
      SLam m x <$> enterCtx (bind x a) (check t vb)
    (t, VPi Implicit x' a b) -> do
      vb <- evalInOwnCtxHere b
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
      reprTy <- reprHere (inv m) ty
      unifyHere reprTy ty'
      return $ SRepr m t'
    (PHole n, ty) -> do
      forbidPat term
      checkMetaHere (Just n) ty
    (PWild, ty) ->
      ifInPat
        (uniqueName >>= (`checkPatBind` ty))
        (checkMetaHere Nothing ty)
    (PCase s cs, ty) -> checkCase s cs ty
    (te, ty) -> do
      (te', ty') <- infer te >>= insert
      unifyHere ty ty'
      return te'
