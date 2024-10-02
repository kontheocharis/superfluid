{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Evaluation
  ( Eval (..),
    quote,
    quotePat,
    nf,
    resolve,
    force,
    eval,
    isTypeFamily,
    isCtorTy,
    ifIsData,
    ($$),
    vApp,
    vRepr,
    vAppNeu,
    evalPat,
    quoteSpine,
    ensureIsCtor,
    vLams,
    vCase,
    vReprTel,
    reprInfSig,
    uniqueVLams,
    evalInOwnCtx,
    extendEnvByNVars,
    mapGlobalInfoM,
    close,
  )
where

import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal (..),
    DataGlobal (..),
    Glob (..),
    Has (..),
    HasNameSupply (..),
    Idx (..),
    Logger (..),
    Lvl (..),
    MetaVar,
    Name (..),
    Param (..),
    PiMode (..),
    Positive (..),
    Spine,
    Tag (..),
    Tel,
    composeN,
    composeNM,
    globName,
    inv,
    lvlToIdx,
    mapSpine,
    mapSpineM,
    nextLvl,
    nextLvls,
    pattern Impossible,
    pattern Possible,
  )
import Control.Exception (assert)
import Control.Monad (foldM, (>=>))
import Control.Monad.Extra (firstJustM)
import Control.Monad.State (StateT (..))
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.Trans (MonadTrans (..))
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Foldable (toList)
import Data.List.Extra (firstJust)
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), fromList, (><))
import qualified Data.Sequence as S
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    PrimGlobalInfo (..),
    Sig (..),
    getCaseRepr,
    getCtorGlobal,
    getCtorRepr,
    getDataRepr,
    getDefRepr,
    getGlobalRepr,
    getGlobalTags,
    mapSigContentsM,
    removeRepresentedItems,
    unfoldDef,
  )
import Language.C (Position)
import Literals (unfoldLit)
import Meta (SolvedMetas, lookupMetaVar)
import Syntax
  ( BoundState (..),
    Bounds,
    Case (..),
    Closure (..),
    Env,
    SCase,
    SPat (..),
    STm (..),
    VBlockedCase,
    VLazy,
    VLazyCase,
    VLazyHead (..),
    VNeu (..),
    VNeuHead (..),
    VNorm (..),
    VPat,
    VPatB (..),
    VTm (..),
    VTy,
    WTm (WNeu, WNorm),
    mapClosureM,
    sAppSpine,
    sGlobWithParams,
    sLams,
    uniqueSLams,
    weakAsValue,
    pattern VHead,
    pattern VMeta,
    pattern VVar,
  )

class (Logger m, Has m SolvedMetas, Has m Sig, HasNameSupply m) => Eval m where
  normaliseProgram :: m Bool
  setNormaliseProgram :: Bool -> m ()

  reduceUnfoldDefs :: m Bool
  setReduceUnfoldDefs :: Bool -> m ()

infixl 8 $$

($$) :: (Eval m) => Closure -> [VTm] -> m VTm
Closure _ env t $$ us = eval (reverse us ++ env) t

vAppNeu :: VNeu -> Spine VTm -> VNeu
vAppNeu (a, sp) sp' = (a, sp >< sp')

vAppLazy :: VLazy -> Spine VTm -> VLazy
vAppLazy (a, sp) u = (a, sp >< u)

vApp :: (Eval m) => VTm -> Spine VTm -> m VTm
vApp a Empty = return a
vApp (VNorm (VLam _ _ c)) (Arg _ u :<| us) = do
  c' <- c $$ [u]
  vApp c' us
vApp (VNeu n) u = return . VNeu $ vAppNeu n u
vApp (VLazy n) u = return . VLazy $ vAppLazy n u
vApp a b = error $ "impossible application: " ++ show a ++ " applied to " ++ show b

uniqueVLams :: (Eval m) => [PiMode] -> Closure -> m VTm
uniqueVLams ms t = do
  sp <- fromList <$> mapM (\m -> Arg m <$> uniqueName) ms
  vLams sp t

vLams :: (Eval m) => Spine Name -> Closure -> m VTm
vLams Empty t = do
  t $$ []
vLams (Arg m x :<| sp) t = do
  let inner = sLams sp t.body
  return $ VNorm (VLam m x (Closure (t.numVars + 1) t.env inner))

vMatch :: VPat -> VTm -> Maybe (Env VTm)
vMatch (VNeu (VVar _)) u = Just [u]
vMatch (VNorm (VCtor ((CtorGlobal c, _), ps))) (VNorm (VCtor ((CtorGlobal c', _), xs)))
  | c == c' && length ps == length xs =
      foldM
        ( \acc (Arg _ p, Arg _ x) -> do
            env <- vMatch p x
            return $ acc ++ env
        )
        []
        (S.zip ps xs)
vMatch _ _ = Nothing

vWhnf :: (Eval m) => Lvl -> VTm -> m (Maybe WTm)
vWhnf l x = do
  x' <- force x
  case x' of
    VNorm n -> return . Just $ WNorm n
    VNeu n -> return . Just $ WNeu n
    VLazy n -> vUnfoldLazy l n

vUnfoldLazy :: (Eval m) => Lvl -> VLazy -> m (Maybe WTm)
vUnfoldLazy l (n, sp) = do
  n' <- vUnfoldLazyHead l n
  case n' of
    Just m -> do
      res <- vApp (weakAsValue m) sp
      vWhnf l res
    Nothing -> return Nothing

-- Returns: Just t if t is a weak head normal form, Nothing otherwise.
vUnfoldLazyHead :: (Eval m) => Lvl -> VLazyHead -> m (Maybe WTm)
vUnfoldLazyHead l = \case
  VDef d -> do
    d' <- access (unfoldDef d)
    case d' of
      Just t -> vWhnf l t
      _ -> return Nothing
  VLit n -> return $ Just (WNorm (unfoldLit n))
  VLazyCase c -> do
    s <- vUnfoldLazy l c.subject
    case s of
      Just s' -> do
        c' <- vCase (c {subject = weakAsValue s'})
        vWhnf l c'
      Nothing -> return Nothing
  VReprLit i n -> do
    nr <- vRepr l i (VNorm (unfoldLit n))
    vWhnf l nr
  VReprLazyCase i c -> do
    s' <- vUnfoldLazy l c.subject
    case s' of
      Just s'' -> do
        c' <- vCase (c {subject = weakAsValue s''})
        cr <- vRepr l i c'
        vWhnf l cr
      Nothing -> vWhnfReprCase l i vLazyCaseToSpine c
  VReprBlockedCase i c -> vWhnfReprCase l i vBlockedCaseToSpine c
  VReprDef i d -> vWhnfReprGlob l i (DefGlob d) []
  VReprCtor i (c, xs) -> vWhnfReprGlob l i (CtorGlob c) xs
  VReprData i d -> vWhnfReprGlob l i (DataGlob d) []

vWhnfReprCase ::
  (Eval m) =>
  Lvl ->
  Positive ->
  (Case n VTm VPatB Closure -> m (Spine VTm)) ->
  Case n VTm VPatB Closure ->
  m (Maybe WTm)
vWhnfReprCase l i toSpine c = do
  d' <- access (getCaseRepr c.dat)
  case d' of
    Just t -> do
      t' <- t $$ map (\a -> a.arg) (toList c.datParams)
      sp <- toSpine c
      res <- vApp t' sp
      rres <- case i of
        One -> return res
        OnePlus i' -> vRepr l i' res
      vWhnf l rres
    _ -> return Nothing

vWhnfReprGlob :: (Eval m) => Lvl -> Positive -> Glob -> [VTm] -> m (Maybe WTm)
vWhnfReprGlob l i g xs = do
  d' <- access (getGlobalRepr g)
  case d' of
    Just t -> do
      t' <- t $$ xs
      tr <- case i of
        One -> return t'
        OnePlus i' -> vRepr l i' t'
      vWhnf l tr
    Nothing -> return Nothing

vCase :: (Eval m) => Case VTm VTm VPatB Closure -> m VTm
vCase c = do
  v' <- force c.subject
  case v' of
    VNorm _ -> do
      firstJustM
        ( \case
            Possible p t -> case vMatch p.vPat v' of
              Just env -> Just <$> t $$ env
              Nothing -> return Nothing
            Impossible _ -> return Nothing
        )
        c.clauses
        >>= \case
          Just x' -> return x'
          Nothing -> error "impossible"
    VNeu n -> return $ VNeu (VBlockedCase (c {subject = n}), Empty)
    VLazy n -> return $ VLazy (VLazyCase (c {subject = n}), Empty)

postCompose :: (Eval m) => (STm -> STm) -> Closure -> m Closure
postCompose f (Closure n env t) = return $ Closure n env (f t)

preCompose :: (Eval m) => Closure -> (STm -> STm) -> m Closure
preCompose (Closure n env t) f = do
  assert (n == 1) $ return ()
  return $
    Closure
      n
      env
      ( SApp
          Explicit
          ( sAppSpine
              ( sLams
                  (S.fromList $ map (\i -> Arg Explicit $ Name ("c" ++ show i)) [1 .. length env])
                  (SLam Explicit (Name "x") t)
              )
              (S.fromList $ map (Arg Explicit . SVar . Idx) (reverse [1 .. length env]))
          )
          (f (SVar (Idx 0)))
      )

unreprClosure :: (Eval m) => Closure -> m Closure
unreprClosure t = do
  a <- postCompose SUnrepr t
  preCompose a SRepr

reprClosure :: (Eval m) => Closure -> m Closure
reprClosure t = do
  a <- postCompose SRepr t
  preCompose a SUnrepr

sCaseToSpine :: (Eval m) => SCase -> m (Spine STm)
sCaseToSpine = caseToSpine id (\p -> uniqueSLams (map (const Explicit) p.binds)) True

vLazyCaseToSpine :: (Eval m) => VLazyCase -> m (Spine VTm)
vLazyCaseToSpine = caseToSpine VLazy (\p -> uniqueVLams (map (const Explicit) p.binds)) False

vBlockedCaseToSpine :: (Eval m) => VBlockedCase -> m (Spine VTm)
vBlockedCaseToSpine = caseToSpine VNeu (\p -> uniqueVLams (map (const Explicit) p.binds)) False

caseToSpine :: (Eval m) => (s -> t) -> (p -> c -> m t) -> Bool -> Case s t p c -> m (Spine t)
caseToSpine sToT uniqueLams withDataParams c = do
  firstPart <-
    foldM
      ( \acc -> \case
          Possible p t -> do
            t' <- uniqueLams p t
            return $ acc :|> Arg Explicit t'
          Impossible _ -> return acc
      )
      (if withDataParams then c.datParams else Empty :|> Arg Explicit c.elimTy)
      c.clauses
  return $ firstPart >< c.subjectIndices >< S.singleton (Arg Explicit (sToT c.subject))

mapDataGlobalInfoM :: (Eval m) => (STm -> m STm) -> DataGlobalInfo -> m DataGlobalInfo
mapDataGlobalInfoM f (DataGlobalInfo n params fullTy ty ctors motiveTy elimTy indexArity) = do
  params' <- traverse (traverse f) params
  fullTy' <- quote (Lvl 0) fullTy >>= f >>= eval []
  ty' <- mapClosureM f ty
  motiveTy' <- traverse (mapClosureM f) motiveTy
  elimTy' <- traverse (mapClosureM f) elimTy
  return $ DataGlobalInfo n params' fullTy' ty' ctors motiveTy' elimTy' indexArity

mapCtorGlobalInfoM :: (Eval m) => (STm -> m STm) -> CtorGlobalInfo -> m CtorGlobalInfo
mapCtorGlobalInfoM f (CtorGlobalInfo n ty idx dataGlobal argArity) = do
  ty' <- mapClosureM f ty
  return $ CtorGlobalInfo n ty' idx dataGlobal argArity

mapDefGlobalInfoM :: (Eval m) => (STm -> m STm) -> DefGlobalInfo -> m DefGlobalInfo
mapDefGlobalInfoM f (DefGlobalInfo n ty vtm tm) = do
  ty' <- quote (Lvl 0) ty >>= f >>= eval []
  vtm' <- traverse (quote (Lvl 0) >=> f >=> eval []) vtm
  b <- normaliseProgram
  tm' <- if b then traverse (quote (Lvl 0)) vtm' else traverse f tm
  return $ DefGlobalInfo n ty' vtm' tm'

mapPrimGlobalInfoM :: (Eval m) => (STm -> m STm) -> PrimGlobalInfo -> m PrimGlobalInfo
mapPrimGlobalInfoM f (PrimGlobalInfo n ty) = do
  ty' <- quote (Lvl 0) ty >>= f >>= eval []
  return $ PrimGlobalInfo n ty'

mapGlobalInfoM :: (Eval m) => (STm -> m STm) -> GlobalInfo -> m GlobalInfo
mapGlobalInfoM f i = case i of
  DataInfo d -> DataInfo <$> mapDataGlobalInfoM f d
  CtorInfo c -> CtorInfo <$> mapCtorGlobalInfoM f c
  DefInfo d -> DefInfo <$> mapDefGlobalInfoM f d
  PrimInfo p -> PrimInfo <$> mapPrimGlobalInfoM f p

vReprTel :: (Eval m) => Lvl -> Positive -> Tel STm -> m (Tel STm)
vReprTel _ _ Empty = return Empty
vReprTel l m (Param m' n a :<| xs) = do
  a' <- (\a' -> a'.body) <$> postCompose (composeN m SRepr) (Closure 0 [] a)
  xs' <- vReprTel l m xs
  xs'' <- traverse (traverse (\x -> (\x' -> x'.body) <$> composeNM m reprClosure (Closure 0 [] x))) xs'
  return $ Param m' n a' :<| xs''

vReprNorm :: (Eval m) => Lvl -> Positive -> VNorm -> m VTm
vReprNorm l m (VPi e v ty t) = do
  ty' <- vRepr l m ty
  t' <- composeNM m reprClosure t
  return . VNorm $ VPi e v ty' t'
vReprNorm _ m (VLam e v t) = do
  t' <- composeNM m reprClosure t
  return . VNorm $ VLam e v t'
vReprNorm _ _ VU = return (VNorm VU)
vReprNorm l m (VData (d, sp)) = do
  sp' <- mapSpineM (vRepr l m) sp
  return $ VLazy (VReprData m d, sp')
vReprNorm l m (VCtor ((c, pp), sp)) = do
  pp' <- mapM (vRepr l m) pp
  sp' <- mapSpineM (vRepr l m) sp
  return $ VLazy (VReprCtor m (c, pp'), sp')

vReprLazy :: (Eval m) => Lvl -> Positive -> VLazy -> m VTm
vReprLazy l m (n, sp) = do
  sp' <- mapSpineM (vRepr l m) sp
  let n' = case n of
        VDef d -> VReprDef m d
        VLit t -> VReprLit m t
        VLazyCase c -> VReprLazyCase m c
        VReprLit t c -> VReprLit (t <> m) c
        VReprLazyCase t c -> VReprLazyCase (t <> m) c
        VReprBlockedCase t c -> VReprBlockedCase (t <> m) c
        VReprDef t d -> VReprDef (t <> m) d
        VReprCtor t (c, pp) -> VReprCtor (t <> m) (c, pp)
        VReprData t d -> VReprData (t <> m) d
  return $ VLazy (n', sp')

vReprNeu :: (Eval m) => Lvl -> Positive -> VNeu -> m VTm
vReprNeu l m (n, sp) = do
  sp' <- mapSpineM (vRepr l m) sp
  case n of
    VFlex x -> return $ VNeu (VReprFlex m x, sp')
    VRigid x -> return $ VNeu (VReprRigid m x, sp')
    VBlockedCase c -> return $ VLazy (VReprBlockedCase m c, sp')
    VPrim p -> return $ VNeu (VReprPrim m p, sp')
    VUnrepr x -> do
      x' <- x $$ []
      case m of
        One -> return x'
        OnePlus m' -> vRepr l m' x'
    VReprFlex t x -> return $ VNeu (VReprFlex (t <> m) x, sp')
    VReprRigid t x -> return $ VNeu (VReprRigid (t <> m) x, sp')
    VReprPrim t p -> return $ VNeu (VReprPrim (t <> m) p, sp')

vRepr :: (Eval m) => Lvl -> Positive -> VTm -> m VTm
vRepr l t (VNorm n) = vReprNorm l t n
vRepr l t (VNeu n) = vReprNeu l t n
vRepr l t (VLazy n) = vReprLazy l t n

reprInfSig :: (Eval m) => m ()
reprInfSig = do
  s <- view
  let s' = removeRepresentedItems s
  s'' <- mapSigContentsM (mapGlobalInfoM sReprInf) s'
  modify (const s'')

sReprInfGlob :: (Eval m) => Glob -> [STm] -> m STm
sReprInfGlob g xs = do
  d' <- access (getGlobalRepr g)
  case d' of
    Just r' -> do
      r'' <- closureToLam r'
      let res = sAppSpine r'' (S.fromList (map (Arg Explicit) xs))
      sReprInf res
    Nothing -> do
      xs' <- mapM sReprInf xs
      return $ sGlobWithParams g xs'

sReprInfCase :: (Eval m) => SCase -> m STm
sReprInfCase c = do
  r <- access (getCaseRepr c.dat)
  case r of
    Just r' -> do
      r'' <- closureToLam r'
      sp <- sCaseToSpine c
      let res = sAppSpine r'' sp
      sReprInf res
    Nothing -> do
      datParams' <- mapSpineM sReprInf c.datParams
      subject' <- sReprInf c.subject
      subjectIndices' <- mapSpineM sReprInf c.subjectIndices
      elimTy' <- sReprInf c.elimTy
      clauses' <- traverse (bitraverse return sReprInf) c.clauses
      return $ SCase (Case c.dat datParams' subject' subjectIndices' elimTy' clauses')

sReprInf :: (Eval m) => STm -> m STm
sReprInf (SPi m x a b) = do
  a' <- sReprInf a
  b' <- sReprInf b
  return $ SPi m x a' b'
sReprInf (SLam m x t) = do
  t' <- sReprInf t
  return $ SLam m x t'
sReprInf SU = return SU
sReprInf (SLit t) = SLit <$> traverse sReprInf t
sReprInf (SApp m a b) = do
  a' <- sReprInf a
  b' <- sReprInf b
  return $ SApp m a' b'
sReprInf (SData d) = sReprInfGlob (DataGlob d) []
sReprInf (SCtor (c, xs)) = sReprInfGlob (CtorGlob c) xs
sReprInf (SDef d) = sReprInfGlob (DefGlob d) []
sReprInf (SPrim p) = sReprInfGlob (PrimGlob p) []
sReprInf (SCase c) = sReprInfCase c
sReprInf (SRepr x) = sReprInf x
sReprInf (SUnrepr x) = sReprInf x
sReprInf (SMeta m bs) = do
  warnMsg $ "found metavariable while representing program: " ++ show m
  return $ SMeta m bs
sReprInf (SLet x ty t y) = do
  ty' <- sReprInf ty
  t' <- sReprInf t
  y' <- sReprInf y
  return $ SLet x ty' t' y'
sReprInf (SVar i) = return $ SVar i

close :: (Eval m) => Int -> Env VTm -> STm -> m Closure
close n env t = return $ Closure n env t

closureArgs :: Int -> Int -> [VTm]
closureArgs n envLen = map (VNeu . VVar . Lvl . (+ envLen)) (reverse [0 .. n - 1])

extendEnvByNVars :: Int -> Env VTm -> Env VTm
extendEnvByNVars numVars env = closureArgs numVars (length env) ++ env

evalInOwnCtx :: (Eval m) => Lvl -> Closure -> m VTm
evalInOwnCtx l cl = cl $$ closureArgs cl.numVars l.unLvl

closureToLam :: (Eval m) => Closure -> m STm
closureToLam c = do
  r'' <- evalInOwnCtx (Lvl (length c.env)) c >>= quote (nextLvls (Lvl (length c.env)) c.numVars)
  uniqueSLams (replicate c.numVars Explicit) r''

evalPat :: (Eval m) => Env VTm -> SPat -> m VPatB
evalPat env pat = do
  (n, _) <- runStateT (evalPat' env pat.asTm) (length env - length pat.binds)
  return $ VPatB n pat.binds
  where
    evalPat' :: (Eval m) => Env VTm -> STm -> StateT Int m VTm
    evalPat' e pat' = case pat' of
      (SCtor (c, pp)) -> do
        pp' <- mapM (lift . eval e) pp
        return $ VNorm (VCtor ((c, pp'), Empty))
      (SApp m a b) -> do
        a' <- evalPat' e a
        b' <- evalPat' e b
        lift $ vApp a' (S.singleton (Arg m b'))
      (SVar (Idx _)) -> do
        s <- get
        put (s + 1)
        return $ VNeu (VVar (Lvl s))
      _ -> error $ "impossible: found pat " ++ show pat'

eval :: (Eval m) => Env VTm -> STm -> m VTm
eval env (SPi m v ty1 ty2) = do
  ty1' <- eval env ty1
  c <- close 1 env ty2
  return $ VNorm (VPi m v ty1' c)
eval env (SLam m v t) = do
  c <- close 1 env t
  return $ VNorm (VLam m v c)
eval env (SLet _ _ t1 t2) = do
  t1' <- eval env t1
  eval (t1' : env) t2
eval env (SApp m t1 t2) = do
  t1' <- eval env t1
  t2' <- eval env t2
  vApp t1' (S.singleton (Arg m t2'))
eval env (SCase (Case dat pp t i r cs)) = do
  t' <- eval env t
  cs' <-
    mapM
      ( \p ->
          bitraverse
            (evalPat (extendEnvByNVars (length p.pat.binds) env))
            (close (length p.pat.binds) env)
            p
      )
      cs
  r' <- eval env r
  i' <- mapSpineM (eval env) i
  pp' <- mapSpineM (eval env) pp
  vCase (Case dat pp' t' i' r' cs')
eval _ SU = return (VNorm VU)
eval l (SLit i) = do
  i' <- traverse (eval l) i
  return $ VLazy (VLit i', Empty)
eval env (SMeta m bds) = do
  m' <- vMeta m
  vAppBinds env m' bds
eval env (SData d) = return $ VNorm (VData (d, Empty))
eval env (SCtor (c, pp)) = do
  pp' <- mapM (eval env) pp
  return $ VNorm (VCtor ((c, pp'), Empty))
eval env (SDef d) = do
  return $ VLazy (VDef d, Empty)
eval env (SPrim p) = do
  return $ VNeu (VPrim p, Empty)
eval env (SVar (Idx i)) = return $ env !! i
eval env (SRepr t) = do
  t' <- eval env t
  undefined

vAppBinds :: (Eval m) => Env VTm -> VTm -> Bounds -> m VTm
vAppBinds env v binds = case (drop (length env - length binds) env, binds) of
  (_, []) -> return v
  (x : env', Bound : binds') -> do
    v' <- vApp v (S.singleton (Arg Explicit x))
    vAppBinds env' v' binds'
  (_ : env', Defined : binds') -> vAppBinds env' v binds'
  ([], _) -> error "impossible"

vMeta :: (Eval m) => MetaVar -> m VTm
vMeta m = do
  mt <- lookupMetaVar m
  case mt of
    Just t -> return t
    Nothing -> return $ VNeu (VMeta m)

force :: (Eval m) => VTm -> m VTm
force v@(VNeu (VFlex m, sp)) = do
  mt <- lookupMetaVar m
  case mt of
    Just t -> do
      t' <- vApp t sp
      force t'
    Nothing -> return v
force v = return v

quoteSpine :: (Eval m) => Lvl -> STm -> Spine VTm -> m STm
quoteSpine _ t Empty = return t
quoteSpine l t (sp :|> Arg m u) = do
  t' <- quoteSpine l t sp
  u' <- quote l u
  return $ SApp m t' u'

quoteClosure :: (Eval m) => Lvl -> Closure -> m STm
quoteClosure l cl = do
  a <- evalInOwnCtx l cl
  quote (nextLvls l cl.numVars) a

quotePat :: (Eval m) => Lvl -> VPatB -> m SPat
quotePat l p = do
  p' <- quotePat' l p.vPat
  return $ SPat p' p.binds
  where
    quotePat' :: (Eval m) => Lvl -> VTm -> m STm
    -- quotePat' l' (VNeu (VApp vh sp)) = do
    --   sp' <- mapSpineM (quotePat' l') sp
    --   vh' <- quotePatHead l' vh
    --   return $ sAppSpine vh' sp'
    quotePat' _ _ = error "impossible"

-- quotePatHead :: (Eval m) => Lvl -> VHead -> m STm
-- quotePatHead _ (VFlex _) = error "impossible"
-- quotePatHead _ (VRigid _) = return $ SVar (Idx 0)
-- quotePatHead _ (VGlobal g pp) = do
--   pp' <- mapM (quote l) pp
--   return $ SGlobal g pp'

-- (VApp h sp) -> do
--   h' <- quoteHead l h
--   quoteSpine l h' sp
-- (VReprApp m v sp) -> do
--   v' <- quoteNeu l v
--   quoteSpine l (SRepr m v') sp
-- (VCaseApp (Case dat pp v i r cs) sp) -> do
--   v' <- quote l (VNeu v)
--   cs' <- mapM (bitraverse (quotePat l) (quoteClosure l)) cs
--   r' <- quote l r
--   pp' <- mapSpineM (quote l) pp
--   i' <- mapSpineM (quote l) i
--   quoteSpine l (SCase (Case dat pp' v' i' r' cs')) sp

quoteLazy :: (Eval m) => Lvl -> VLazy -> m STm
quoteLazy = undefined

-- quoteNeuRepr :: (Eval m) => Lvl -> VNeuHead -> m STm
-- quoteNeuRepr l t h = do
--   m' <- quoteNeu l (h, Empty)
--   return $ SRepr t m'

quoteNeu :: (Eval m) => Lvl -> VNeu -> m STm
quoteNeu l (n, sp) = do
  n' <- case n of
    VFlex m -> return $ SMeta m []
    VRigid l' -> return $ SVar (lvlToIdx l l')
    VBlockedCase b -> undefined
    VPrim p -> return $ SPrim p
  -- VUnrepr c -> do
  --   c' <- c $$ []
  --   cq <- quote l c'
  --   return $ SRepr (Finite (-1)) cq
  -- VReprFlex t m -> quoteNeuRepr l t (VFlex m)
  -- VReprRigid t x -> quoteNeuRepr l t (VRigid x)
  -- VReprPrim t p -> quoteNeuRepr l t (VPrim p)
  quoteSpine l n' sp

quoteNorm :: (Eval m) => Lvl -> VNorm -> m STm
quoteNorm l n = case n of
  VLam m x t -> do
    t' <- quoteClosure l t
    return $ SLam m x t'
  VPi m x ty t -> do
    ty' <- quote l ty
    t' <- quoteClosure l t
    return $ SPi m x ty' t'
  VU -> return SU
  VData (d, sp) -> quoteSpine l (SData d) sp
  VCtor ((c, pp), sp) -> do
    pp' <- mapM (quote l) pp
    quoteSpine l (SCtor (c, pp')) sp

quote :: (Eval m) => Lvl -> VTm -> m STm
quote l (VNorm n) = quoteNorm l n
quote l (VLazy n) = quoteLazy l n
quote l (VNeu n) = quoteNeu l n

-- case vt' of
--   VLam m x t -> do
--     t' <- quoteClosure l t
--     return $ SLam m x t'
--   VPi m x ty t -> do
--     ty' <- quote l ty
--     t' <- quoteClosure l t
--     return $ SPi m x ty' t'
--   VU -> return SU
--   -- VLit lit -> SLit <$> traverse (quote l) lit
--   VNeu n -> quoteNeu l n

-- @@TODO: The below should happen in quote
-- ts <- access (getGlobalTags (globName g))
-- case (UnfoldTag `elem` ts, g) of
--   (True, DefGlob d) -> do
--     g' <- access (unfoldDef d)
--     case g' of
--       Just t -> return t
--       _ -> do
--         pp' <- mapM (eval env) pp
--         return $ VNeu (VHead (VGlobal g pp'))
--   _ -> do
--     pp' <- mapM (eval env) pp
--     return $ VNeu (VHead (VGlobal g pp'))

nf :: (Eval m) => Env VTm -> STm -> m STm
nf env t = do
  t' <- eval env t
  quote (envLvl env) t'

resolve :: (Eval m) => Env VTm -> VTm -> m VTm
resolve env t = do
  t' <- quote (envLvl env) t
  eval env t'

envLvl :: Env VTm -> Lvl
envLvl env = Lvl (length env)

isTypeFamily :: (Eval m) => Lvl -> VTm -> m Bool
isTypeFamily l t = do
  t' <- vWhnf l t
  case t' of
    Just (WNorm (VPi _ _ _ b)) -> do
      b' <- evalInOwnCtx l b
      isTypeFamily (nextLvl l) b'
    Just (WNorm VU) -> return True
    _ -> return False

isCtorTy :: (Eval m) => Lvl -> DataGlobal -> VTm -> m (Maybe (Spine ()))
isCtorTy l d t = do
  t' <- vWhnf l t
  case t' of
    Just (WNorm (VPi _ _ _ b)) -> do
      b' <- evalInOwnCtx l b
      isCtorTy (nextLvl l) d b'
    Just (WNorm (VData (d', sp))) | d == d' -> return (Just (mapSpine (const ()) sp))
    _ -> return Nothing

ifIsData :: (Eval m) => Lvl -> VTy -> (DataGlobal -> Spine VTm -> m a) -> m a -> m a
ifIsData l v a b = do
  v' <- vWhnf l v
  case v' of
    Just (WNorm (VData (d, sp))) -> a d sp
    _ -> b

ensureIsCtor :: (Eval m) => Lvl -> VTm -> CtorGlobal -> m () -> m ()
ensureIsCtor l v c a = do
  v' <- vWhnf l v
  case v' of
    Just (WNorm (VCtor ((c', _), _))) | c == c' -> return ()
    _ -> a
