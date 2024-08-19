{-# LANGUAGE FlexibleContexts #-}

module Elaboration
  ( ElabError (..),
    Ctx,
    infer,
    check,
  )
where

import Algebra.Lattice ((/\), (\/))
import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal (..),
    DataGlobal (..),
    Glob (..),
    Idx (..),
    Lit (..),
    Loc,
    Lvl (..),
    Name,
    PiMode (..),
    Pos,
    Spine,
    Times,
    inv,
    lvlToIdx,
    nextLvl,
    nextLvls,
    pat,
    pattern Impossible,
    pattern Possible,
  )
import Control.Monad.Except (MonadError (throwError))
import Data.Functor (void)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation (Eval (..), close, eval, evalInOwnCtx, force, quote, vRepr, ($$))
import Globals (GlobalInfo (..), HasSig (accessSig), KnownGlobal (..), globalInfoToTm, knownData, lookupGlobal)
import Presyntax (PPat, PTm (..))
import Syntax (SPat, STm (..), STy, toPSpine)
import Unification (CanUnify (..), Unify (), unify)
import Value
  ( Closure (..),
    Env,
    Sub,
    VTm (..),
    VTy,
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
  | ImpossibleCaseIsPossible VTm
  | ImpossibleCaseMightBePossible VTm
  | ImpossibleCase VTm
  | InvalidCaseSubject PTm

data InPat = NotInPat | InPossiblePat | InImpossiblePat

class (Eval m, Unify m, MonadError ElabError m) => Elab m where
  getCtx :: m Ctx
  setCtx :: Ctx -> m ()

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

  ifInPat :: m a -> m a -> m a
  ifInPat a b = do
    b' <- inPat
    case b' of
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
    names :: Map Name Lvl,
    currentLoc :: Loc
  }

applySubToCtx :: Sub -> Ctx -> Ctx
applySubToCtx sub ctx = undefined

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
located l ctx = ctx {currentLoc = l}

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

handleUnification :: (Elab m) => CanUnify -> m ()
handleUnification r = do
  p <- inPat
  let t1 = undefined
  let t2 = undefined -- @@Todo
  case p of
    InImpossiblePat -> case r of
      Yes -> throwError $ ImpossibleCaseIsPossible t1
      Maybe _ -> throwError $ ImpossibleCaseMightBePossible t1
      No -> return ()
    InPossiblePat -> case r of
      Yes -> return ()
      Maybe s -> modifyCtx (applySubToCtx s)
      No -> throwError $ ImpossibleCase t1
    NotInPat -> case r of
      Yes -> return ()
      Maybe _ -> throwError $ PotentialMismatch t1 t2
      No -> throwError $ Mismatch t1 t2

unifyHere :: (Elab m) => VTm -> VTm -> m CanUnify
unifyHere t1 t2 = do
  l <- accessCtx (\c -> c.lvl)
  unify l t1 t2

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
        else throwError $ ImplicitMismatch m m'
    _ -> do
      a <- freshMeta >>= evalHere
      v <- uniqueName
      b <- closeHere 1 =<< enterCtx (bind v a) freshMeta
      unifyHere ty (VPi m v a b) >>= handleUnification
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

forbidPat :: (Elab m) => PTm -> m ()
forbidPat p = ifInPat (throwError $ InvalidPattern p) (return ())

newPatBind :: (Elab m) => Name -> m (STm, VTy)
newPatBind x = do
  ty <- evalHere =<< freshMeta
  modifyCtx (bind x ty)
  return (lastIdx, ty)

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
          _ -> newPatBind n
    )
    ( do
        r <- accessCtx (lookupName n)
        case r of
          Just (i, t) -> return (SVar i, t)
          Nothing -> do
            l <- accessSig (lookupGlobal n)
            case l of
              Just x -> return (globalInfoToTm n x)
              Nothing -> throwError $ UnresolvedVariable n
    )

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterCtx (located l) $ infer t
  PName x -> inferName x
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
    reprTy <- reprHere m ty
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
    (ss, vsTy) <- infer s
    vs <- evalHere ss
    d <- ifIsData vsTy return (throwError $ InvalidCaseSubject s)
    retTy <- freshMeta >>= evalHere
    scs <-
      mapM
        ( \case
            Possible p t -> do
              sp <- checkPatAgainstSubject InPossiblePat p vs vsTy
              st <- check t retTy
              return $ Possible sp st
            Impossible p -> do
              sp <- checkPatAgainstSubject InImpossiblePat p vs vsTy
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

checkPatAgainstSubject :: (Elab m) => InPat -> PPat -> VTm -> VTy -> m SPat
checkPatAgainstSubject i p vs vsTy = enterPat i $ do
  (sp, spTy) <- infer p
  a <- unifyHere vsTy spTy
  vp <- evalHere sp
  b <- unifyHere vp vs
  handleUnification (a /\ b)
  return sp

check :: (Elab m) => PTm -> VTy -> m STm
check term typ = do
  typ' <- force typ
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
      reprTy <- reprHere (inv m) ty
      unifyHere reprTy ty' >>= handleUnification
      return $ SRepr m t'
    (te, ty) -> do
      (te', ty') <- infer te >>= insert
      unifyHere ty ty' >>= handleUnification
      return te'
