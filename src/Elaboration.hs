{-# LANGUAGE FlexibleContexts #-}

module Elaboration
  ( ElabError (..),
    Ctx,
    infer,
    check,
  )
where

import Common
  ( Arg (..),
    CtorGlobal (..),
    DataGlobal (..),
    Glob (..),
    Idx (..),
    Loc,
    Lvl (..),
    Name,
    PiMode (..),
    Pos,
    Spine,
    inv,
    lvlToIdx,
    nextLvl,
    nextLvls,
    pat, Times,
  )
import Control.Monad.Except (MonadError (throwError))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Sequence (Seq (..))
import Evaluation (Eval (..), close, eval, evalInOwnCtx, force, quote, vRepr, ($$))
import Presyntax (PTm (..))
import Syntax (STm (..), STy, toPSpine)
import Unification (Unify (ifInPat), enterPat, unify)
import Value
  ( Closure (..),
    Env,
    VTm (..),
    VTy,
    pattern VHead,
    pattern VRepr,
    pattern VVar,
  )

data ElabError
  = Mismatch PTm PTm
  | UnresolvedVariable Name
  | ImplicitMismatch PiMode PiMode
  | InvalidPattern PTm
  | InvalidCaseSubject PTm

class (Eval m, Unify m, MonadError ElabError m) => Elab m where
  getCtx :: m Ctx
  setCtx :: Ctx -> m ()

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
    types :: [VTy],
    names :: Map Name Lvl,
    currentLoc :: Loc
  }

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

unifyHere :: (Elab m) => VTm -> VTm -> m ()
unifyHere t1 t2 = do
  l <- accessCtx (\c -> c.lvl)
  _ <- unify l t1 t2 -- @@Todo: check if in pattern
  return ()

closeValHere :: (Elab m) => Int -> VTm -> m Closure
closeValHere n t = do
  (l, e) <- accessCtx (\c -> (c.lvl, c.env))
  t' <- quote (nextLvls l n) t
  close n e t'

closeHere :: (Elab m) => Int -> STm -> m Closure
closeHere n t = do
  e <- accessCtx (\c -> c.env)
  close n e t

forceHere :: (Elab m) => VTm -> m VTm
forceHere t = do
  l <- accessCtx (\c -> c.lvl)
  force l t

forcePiType :: (Elab m) => PiMode -> VTy -> m (VTy, Closure)
forcePiType m ty = do
  ty' <- forceHere ty
  case ty' of
    VPi m' _ a b -> do
      if m == m'
        then return (a, b)
        else throwError $ ImplicitMismatch m m'
    _ -> do
      a <- freshMeta >>= evalHere
      v <- uniqueName
      b <- closeHere 1 =<< enterCtx (bind v a) freshMeta
      unifyHere ty (VPi m v a b)
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

symbolicArgsForClosure :: Lvl -> Closure -> [VTm]
symbolicArgsForClosure l (Closure n _ t) = map (VNeu . VVar . Lvl . (+ l.unLvl)) [0 .. n - 1]

forbidPat :: (Elab m) => PTm -> m ()
forbidPat p = ifInPat (throwError $ InvalidPattern p) (return ())

newPatBind :: (Elab m) => Name -> m (STm, VTy)
newPatBind x = do
  ty <- evalHere =<< freshMeta
  modifyCtx (bind x ty)
  return (lastIdx, ty)

ifIsCtorName :: (Elab m) => Idx -> Name -> (CtorGlobal -> m a) -> m a -> m a
ifIsCtorName i n a b = do
  v <- accessCtx (definedValue i) >>= forceHere
  case v of
    VGlobal (CtorGlob g@(CtorGlobal s)) Empty | s == n -> a g
    _ -> b

ifIsData :: (Elab m) => VTy -> (DataGlobal -> m a) -> m a -> m a
ifIsData v a b = do
  v' <- forceHere v
  case v' of
    VGlobal (DataGlob g@(DataGlobal s)) _ -> a g
    _ -> b

reprHere :: (Elab m) => Times -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterCtx (located l) $ infer t
  PName x -> do
    n <- accessCtx (lookupName x)
    case n of
      Just (i, t) ->
        ifInPat
          (ifIsCtorName i x (\g -> return (SGlobal (CtorGlob g), t)) (newPatBind x))
          (return (SVar i, t))
      Nothing -> ifInPat (newPatBind x) (throwError $ UnresolvedVariable x)
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
    (s', sTy) <- infer s
    vs <- evalHere s'
    d <- ifIsData sTy return (throwError $ InvalidCaseSubject s)

    mapM
      ( \c -> do
          sPat <- enterPat $ do
            sPat <- check c.pat sTy
            vPat <- evalHere sPat
            unifyHere vPat vs
            return sPat
          -- Dependent pattern matching

          return undefined
      )
      cs

    return undefined
  PLit l -> return undefined

check :: (Elab m) => PTm -> VTy -> m STm
check term typ = do
  typ' <- forceHere typ
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
      unifyHere reprTy ty'
      return $ SRepr m t'
    (te, ty) -> do
      (te', ty') <- infer te >>= insert
      unifyHere ty ty'
      return te'
