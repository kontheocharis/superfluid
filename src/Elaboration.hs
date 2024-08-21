{-# LANGUAGE FlexibleContexts #-}

module Elaboration
  ( Elab (..),
    ElabError (..),
    Ctx (..),
    emptyCtx,
    infer,
    checkProgram,
    check,
    unelab,
  )
where

import Algebra.Lattice ((/\))
import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal (..),
    DataGlobal (..),
    Glob (..),
    HasNameSupply (..),
    HasProjectFiles,
    Idx (..),
    Lit (..),
    Loc (NoLoc),
    Lvl (..),
    Name (..),
    PiMode (..),
    Spine,
    Times,
    globName,
    inv,
    lvlToIdx,
    nextLvl,
    nextLvls,
    pat,
    unMetaVar,
    pattern Impossible,
    pattern Possible, MetaVar,
  )
import Control.Monad (unless, zipWithM, zipWithM_)
import qualified Data.IntMap as IM
import Data.List (intercalate, zipWith4)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Debug.Trace (traceM)
import Evaluation (Eval (..), close, eval, evalInOwnCtx, force, isCtorTy, isTypeFamily, quote, vApp, vRepr, ($$))
import Globals (CtorGlobalInfo (..), DataGlobalInfo (..), DefGlobalInfo (..), GlobalInfo (..), HasSig (accessSig, modifySig), KnownGlobal (..), PrimGlobalInfo (PrimGlobalInfo), addItem, globalInfoToTm, knownCtor, knownData, lookupGlobal, modifyDataItem)
import Meta (HasMetas (freshMetaVar, lookupMetaVarName))
import Presyntax (PCtor (..), PData (..), PDef (..), PItem (..), PPat, PPrim (..), PProgram (..), PTm (..), PTy, pApp)
import Printing (Pretty (..), indentedFst)
import Syntax (BoundState (Bound, Defined), Bounds, SPat (..), STm (..), toPSpine)
import Unification (CanUnify (..), Unify (), unify)
import Value
  ( Closure (..),
    Env,
    Sub,
    VHead (..),
    VNeu (..),
    VTm (..),
    VTy,
    isEmptySub,
    vars,
    pattern VHead,
    pattern VRepr,
    pattern VVar,
  )

data ElabError
  = Mismatch VTm VTm
  | PotentialMismatch VTm VTm
  | UnresolvedVariable Name
  | ImplicitMismatch PiMode PiMode
  | InvalidPattern PTm
  | ImpossibleCaseIsPossible VTm VTm
  | ImpossibleCaseMightBePossible VTm VTm Sub
  | ImpossibleCase VTm
  | InvalidCaseSubject PTm
  | InvalidDataFamily VTy
  | InvalidCtorType VTy
  | DuplicateItem Name
  | Chain [ElabError]

data InPat = NotInPat | InPossiblePat [Name] | InImpossiblePat

instance Show InPat where
  show NotInPat = "not in pat"
  show (InPossiblePat ns) = "in possible pat with " ++ show ns
  show InImpossiblePat = "in impossible pat"

instance (Elab m) => Pretty m VTm where
  pretty v = do
    n <- accessCtx (\c -> c.nameList)
    quote (Lvl (length n)) v >>= unelab n >>= pretty

instance (Elab m) => Pretty m STm where
  pretty t = do
    n <- accessCtx (\c -> c.nameList)
    unelab n t >>= pretty

instance (Elab m) => Pretty m Sub where
  pretty sub = do
    let l = IM.size sub.vars
    vars <-
      mapM
        ( \(x, v) -> do
            l' <- pretty (VNeu (VVar (Lvl x)))
            v' <- pretty v
            return $ l' <> " = " <> v'
        )
        (IM.toList sub.vars)
    return $ intercalate ", " vars

instance (HasProjectFiles m, Elab m) => Pretty m ElabError where
  pretty e = do
    loc <- accessCtx (\c -> c.currentLoc)
    loc' <- pretty loc
    err' <- err
    return $ loc' <> "\n" <> err'
    where
      err = case e of
        Mismatch t1 t2 -> do
          t1' <- pretty t1
          t2' <- pretty t2
          return $ "Mismatch: " <> t1' <> " and " <> t2'
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
        ImpossibleCase t -> do
          t' <- pretty t
          return $ "Impossible case: " <> t'
        InvalidCaseSubject t -> do
          t' <- pretty t
          return $ "Invalid case subject: " <> t'
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

class (Eval m, Unify m) => Elab m where
  getCtx :: m Ctx
  setCtx :: Ctx -> m ()
  elabError :: ElabError -> m a

  showMessage :: String -> m ()

  inPat :: m InPat
  inPat = accessCtx (\c -> c.inPat)

  setInPat :: InPat -> m ()
  setInPat p = modifyCtx (\c -> c {inPat = p})

  enterPat :: InPat -> m a -> m a
  enterPat p a = do
    b <- inPat
    setInPat p
    a' <- a
    setInPat b
    return a'

  whenInPat :: (InPat -> m a) -> m a
  whenInPat f = do
    p <- inPat
    f p

  ifInPat :: m a -> m a -> m a
  ifInPat a b = whenInPat $ \case
    NotInPat -> b
    _ -> a

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

data Ctx = Ctx
  { env :: Env VTm,
    lvl :: Lvl,
    inPat :: InPat,
    types :: [VTy],
    bounds :: Bounds,
    nameList :: [Name],
    names :: Map Name Lvl,
    currentLoc :: Loc
  }

con :: Ctx -> [(Name, VTy, Maybe VTm)]
con c =
  zipWith4
    ( \n t b e ->
        ( n,
          t,
          case b of
            Bound -> Nothing
            Defined -> Just e
        )
    )
    c.nameList
    c.types
    c.bounds
    c.env

instance (Elab m) => Pretty m Ctx where
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
        (reverse $ con c)

emptyCtx :: Ctx
emptyCtx =
  Ctx
    { env = [],
      lvl = Lvl 0,
      inPat = NotInPat,
      types = [],
      bounds = [],
      nameList = [],
      names = M.empty,
      currentLoc = NoLoc
    }

applySubToCtx :: (Elab m) => Sub -> m ()
applySubToCtx sub = do
  ctx <- getCtx
  env' <-
    mapM
      ( \t -> case t of
          VNeu (VApp (VRigid i) sp) -> case IM.lookup i.unLvl sub.vars of
            Just t' -> vApp t' sp
            Nothing -> return t
          _ -> return t
      )
      ctx.env
  modifyCtx $ \c -> c {env = env'} -- @@Fixme: this aint quite right chief

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

located :: Loc -> Ctx -> Ctx
located l ctx = ctx {currentLoc = l}

inferMetaHere :: (Elab m) => Maybe Name -> m (STm, VTy)
inferMetaHere n = do
  ty <- newMetaHere Nothing
  vty <- evalHere ty
  m <- checkMetaHere n vty
  return (m, vty)

prettyGoal :: (Elab m) => Name -> VTy -> m String
prettyGoal n ty = do
  c <- getCtx >>= pretty
  n' <- pretty (PHole n)
  ty' <- pretty ty
  let g = n' ++ " : " ++ ty'
  return $ indentedFst c ++ "\n" ++ replicate (length g + 4) '―' ++ "\n" ++ indentedFst g

checkMetaHere :: (Elab m) => Maybe Name -> VTy -> m STm
checkMetaHere n ty = do
  m <- newMetaHere n
  case n of
    Just n' -> prettyGoal n' ty >>= showMessage
    Nothing -> return ()
  return m

newMetaHere :: (Elab m) => Maybe Name -> m STm
newMetaHere n = do
  bs <- accessCtx (\c -> c.bounds)
  m <- freshMetaVar n
  return (SMeta m bs)

freshMetaHere :: (Elab m) => m STm
freshMetaHere = newMetaHere Nothing

insertFull :: (Elab m) => (STm, VTy) -> m (STm, VTy)
insertFull (tm, ty) = do
  traceM " Here"
  getCtx >>= pretty >>= traceM
  -- tm' <- pretty tm
  -- ty' <- pretty ty
  -- ty' <- pretty ty
  -- traceM $ "Inserting " ++ ty'
  f <- force ty
  traceM $ "Forced"
  case f of
    VPi Implicit _ _ b -> do
      meta <- freshMetaHere
      vmeta <- evalHere meta
      ty' <- b $$ [vmeta]
      -- vm <- pretty $ vmeta
      -- traceM $ "The result is "  ++ vm
      insertFull (SApp Implicit tm meta, ty')
    _ -> return (tm, ty)

insert :: (Elab m) => (STm, VTy) -> m (STm, VTy)
insert (tm, ty) = case tm of
  SLam Implicit _ _ -> return (tm, ty)
  _ -> insertFull (tm, ty)

evalHere :: (Elab m) => STm -> m VTm
evalHere t = do
  e <- accessCtx (\c -> c.env)
  eval e t

handleUnification :: (Elab m) => VTm -> VTm -> CanUnify -> m ()
handleUnification t1 t2 r = do
  p <- inPat
  case p of
    InImpossiblePat -> case r of
      Yes -> elabError $ ImpossibleCaseIsPossible t1 t2
      Maybe s -> elabError $ ImpossibleCaseMightBePossible t1 t2 s
      No _ -> return ()
    InPossiblePat _ -> case r of
      Yes -> return ()
      Maybe s -> applySubToCtx s
      No _ -> elabError $ ImpossibleCase t1
    NotInPat -> case r of
      Yes -> return ()
      Maybe _ -> elabError $ PotentialMismatch t1 t2
      No _ -> elabError $ Mismatch t1 t2

canUnifyHere :: (Elab m) => VTm -> VTm -> m CanUnify
canUnifyHere t1 t2 = do
  l <- accessCtx (\c -> c.lvl)
  unify l t1 t2

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
  traceM $ "ATTEMPT Forcing " ++ show ty
  ty'' <- pretty ty'
  traceM $ "Forcing " ++ ty''
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
  traceM " Here"
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Explicit -> insertFull (t, ty)
    Instance -> error "unimplemented"
  traceM "HEREE"
  (a, b) <- forcePiType m ty'
  u' <- check u a
  uv <- evalHere u'
  b' <- b $$ [uv]
  xs <- pretty $ SApp m t' u'
  bs <- pretty b'

  traceM $ "checked spine: " ++ xs ++ bs

  -- bp <- pretty =<< evalInOwnCtxHere b

  -- traceM $ "the type of the subject is " ++ bp

  checkSpine (SApp m t' u', b') sp

lastIdx :: STm
lastIdx = SVar (Idx 0)

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
        InPossiblePat ns -> setInPat (InPossiblePat (x : ns))
        _ -> return ()
    )
  return lastIdx

ifIsData :: (Elab m) => VTy -> (DataGlobal -> m a) -> m a -> m a
ifIsData v a b = do
  v' <- force v
  case v' of
    VGlobal (DataGlob g@(DataGlobal _)) _ -> a g
    _ -> b

reprHere :: (Elab m) => Times -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

inferName :: (Elab m) => Name -> m (STm, VTy)
inferName n =
  ifInPat
    ( do
        l <- accessSig (lookupGlobal n)
        case l of
          Just c@(CtorInfo _) -> return (globalInfoToTm n c)
          _ -> inferPatBind n
    )
    ( do
        r <- accessCtx (lookupName n)
        case r of
          Just (i, t) -> return (SVar i, t)
          Nothing -> do
            l <- accessSig (lookupGlobal n)
            case l of
              Just x -> return (globalInfoToTm n x)
              Nothing -> elabError $ UnresolvedVariable n
    )

checkDef :: (Elab m) => PDef -> m ()
checkDef def = do
  ty' <- check def.ty VU >>= evalHere
  tm' <- check def.tm ty' >>= evalHere
  modifySig (addItem def.name (DefInfo (DefGlobalInfo ty' tm')))
  return ()

checkCtor :: (Elab m) => DataGlobal -> Int -> PCtor -> m ()
checkCtor dat idx ctor = do
  ty' <- check ctor.ty VU >>= evalHere
  i <- getLvl >>= (\l -> isCtorTy l dat ty')
  unless i (elabError $ InvalidCtorType ty')
  modifySig (addItem ctor.name (CtorInfo (CtorGlobalInfo ty' idx dat)))
  modifySig (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal ctor.name]}))

getLvl :: (Elab m) => m Lvl
getLvl = accessCtx (\c -> c.lvl)

checkData :: (Elab m) => PData -> m ()
checkData dat = do
  ty' <- check dat.ty VU >>= evalHere
  i <- getLvl >>= (`isTypeFamily` ty')
  unless i (elabError $ InvalidDataFamily ty')
  modifySig (addItem dat.name (DataInfo (DataGlobalInfo ty' [])))
  zipWithM_ (checkCtor (DataGlobal dat.name)) [0 ..] dat.ctors

checkPrim :: (Elab m) => PPrim -> m ()
checkPrim prim = do
  ty' <- check prim.ty VU >>= evalHere
  modifySig (addItem prim.name (PrimInfo (PrimGlobalInfo ty')))
  return ()

checkItem :: (Elab m) => PItem -> m ()
checkItem = \case
  PDef def -> checkDef def
  PData dat -> checkData dat
  PPrim prim -> checkPrim prim
  PDataRep {} -> return () -- @@Todo
  PDefRep {} -> return () -- @@Todo
  PLocatedItem l i -> enterCtx (located l) $ checkItem i

checkProgram :: (Elab m) => PProgram -> m ()
checkProgram (PProgram items) = mapM_ checkItem items

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterCtx (located l) $ infer t
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
    (ss, vsTy) <- infer s
    vs <- evalHere ss
    d <- ifIsData vsTy return (elabError $ InvalidCaseSubject s)
    retTy <- freshMetaHere >>= evalHere
    scs <-
      mapM
        ( \case
            Possible p t -> do
              sp <- enterPat (InPossiblePat []) $ checkPatAgainstSubject p vs vsTy
              st <- check t retTy
              return $ Possible sp st
            Impossible p -> do
              sp <- enterPat InImpossiblePat $ checkPatAgainstSubject p vs vsTy
              return $ Impossible sp
        )
        cs
    return (SCase d ss scs, retTy)
  PLit l -> do
    (l', ty, args) <- case l of
      StringLit s -> return (StringLit s, KnownString, Empty)
      CharLit c -> return (CharLit c, KnownChar, Empty)
      NatLit n -> return (NatLit n, KnownNat, Empty)
      FinLit f bound -> do
        bound' <- check bound (VGlobal (DataGlob (knownData KnownNat)) Empty)
        vbound' <- evalHere bound'
        return (FinLit f bound', KnownFin, S.singleton (Arg Explicit vbound'))
    return (SLit l', VGlobal (DataGlob (knownData ty)) args)

currentPatBinds :: (Elab m) => m [Name]
currentPatBinds = do
  p <- accessCtx (\c -> c.inPat)
  case p of
    InPossiblePat ns -> return ns
    _ -> return []

checkPatAgainstSubject :: (Elab m) => PPat -> VTm -> VTy -> m SPat
checkPatAgainstSubject p vs vsTy = do
  (sp, spTy) <- infer p
  ns <- currentPatBinds
  a <- canUnifyHere vsTy spTy
  vp <- evalHere sp
  b <- canUnifyHere vp vs
  handleUnification vp vs (a /\ b)
  return $ SPat sp ns

evalInOwnCtxHere :: (Elab m) => Closure -> m VTm
evalInOwnCtxHere t = do
  lvl <- accessCtx (\c -> c.lvl)
  evalInOwnCtx lvl t

check :: (Elab m) => PTm -> VTy -> m STm
check term typ = do
  typ' <- force typ
  case (term, typ') of
    (PLocated l t, ty) -> enterCtx (located l) $ check t ty
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
    (PCase s cs, ty) -> do
      forbidPat term
      (ss, vsTy) <- infer s
      vs <- evalHere ss
      d <- ifIsData vsTy return (elabError $ InvalidCaseSubject s)
      scs <-
        mapM
          ( \case
              Possible p t -> do
                sp <- enterPat (InPossiblePat []) $ checkPatAgainstSubject p vs vsTy
                st <- check t ty
                return $ Possible sp st
              Impossible p -> do
                sp <- enterPat InImpossiblePat $ checkPatAgainstSubject p vs vsTy
                return $ Impossible sp
          )
          cs
      return (SCase d ss scs)
    (te, ty) -> do
      (te', ty') <- infer te >>= insert
      unifyHere ty ty'
      return te'

unelabMeta :: (HasMetas m) => [Name] -> MetaVar -> Bounds -> m (PTm, [Arg PTm])
unelabMeta _ m [] = do
  n <- lookupMetaVarName m
  case n of
    Just n' -> return (PHole n', [])
    Nothing -> return (PHole (Name $ "m" ++ show m.unMetaVar), [])
unelabMeta (n:ns) m (Bound : bs) = do
  (t, ts) <- unelabMeta ns m bs
  return (t, Arg Explicit (PName n) : ts)
unelabMeta (_:ns) m (Defined : bs) = unelabMeta ns m bs
unelabMeta _ _ _ = error "impossible"

unelab :: (HasMetas m) => [Name] -> STm -> m PTm
unelab ns (SPi m x a b) = PPi m x <$> unelab ns a <*> unelab (x : ns) b
unelab ns (SLam m x t) = PLam m x <$> unelab (x : ns) t
unelab ns (SLet x ty t u) = PLet x <$> unelab ns ty <*> unelab ns t <*> unelab (x : ns) u
unelab ns (SMeta m bs) = do
  (t, ts) <- unelabMeta ns m bs
  return $ pApp t ts
unelab ns (SVar i) = return $ PName (ns !! i.unIdx)
unelab ns (SApp m t u) = PApp m <$> unelab ns t <*> unelab ns u
unelab ns (SCase _ t cs) =
  PCase
    <$> unelab ns t
    <*> mapM
      ( \c ->
          Clause
            <$> unelab (c.pat.binds ++ ns) c.pat.asTm
            <*> traverse (unelab (c.pat.binds ++ ns)) c.branch
      )
      cs
unelab _ SU = return PU
unelab _ (SGlobal g) = return $ PName (globName g)
unelab ns (SLit l) = PLit <$> traverse (unelab ns) l
unelab ns (SRepr m t) = PRepr m <$> unelab ns t
