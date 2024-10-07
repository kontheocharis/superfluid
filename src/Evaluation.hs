{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
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
    vWhnf,
    vUnfold,
    vUnfoldLazy,
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
    DefGlobal (..),
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
    PrimGlobal (..),
    Spine,
    Tag (..),
    Tel,
    composeN,
    composeNM,
    composeZ,
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
    getGlobalRepr,
    getGlobalTags,
    mapSigContentsM,
    removeRepresentedItems,
    unfoldDef,
  )
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
    VHead (..),
    VLazy,
    VLazyCase,
    VLazyHead (..),
    VNeu,
    VNeuHead (..),
    VNorm (..),
    VPat,
    VPatB (..),
    VTm (..),
    VTy,
    WTm (WNeu, WNorm),
    headAsValue,
    mapClosureM,
    mapHeadM,
    sAppSpine,
    sGlobWithParams,
    sLams,
    sReprTimes,
    uniqueSLams,
    weakAsValue,
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

vAppNorm :: (Eval m) => VNorm -> Spine VTm -> m VTm
vAppNorm ((VLam _ _ c)) (Arg _ u :<| us) = do
  c' <- c $$ [u]
  res <- vApp c' us
  -- msg $ "applying \n" ++ show u ++ "\n to \n" ++ show c ++ "\n gets us \n" ++ show res
  return res
vAppNorm ((VData (n, us))) u = return . VNorm $ VData (n, us >< u)
vAppNorm ((VCtor (n, us))) u = return . VNorm $ VCtor (n, us >< u)
vAppNorm a b = error $ "impossible application: " ++ show a ++ " applied to " ++ show b

vApp :: (Eval m) => VTm -> Spine VTm -> m VTm
vApp a Empty = return a
vApp (VNeu n) u = return . VNeu $ vAppNeu n u
vApp (VLazy n) u = return . VLazy $ vAppLazy n u
vApp (VNorm n) u = vAppNorm n u

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

vUnfold :: (Eval m) => Lvl -> VTm -> m VTm
vUnfold l x = do
  x' <- vWhnf l x
  case x' of
    Just x'' -> return x''
    Nothing -> force x

vWhnf :: (Eval m) => Lvl -> VTm -> m (Maybe VTm)
vWhnf l x = do
  x' <- force x
  msg $ "Getting whnf of " ++ show x'
  res <- case x' of
    VNorm _ -> return Nothing
    VNeu _ -> return Nothing
    VLazy n -> vUnfoldLazy l n
  msg $ "Got " ++ show res
  return res


vUnfoldLazy :: (Eval m) => Lvl -> VLazy -> m (Maybe VTm)
vUnfoldLazy l (n, sp) = do
  msg $ "Getting the lazy of " ++ show (n, sp)
  n' <- vUnfoldLazyHead l n
  msg $ "Got lazy head " ++ show n'
  res <- case n' of
    Just m -> Just <$> vApp m sp
    Nothing -> return Nothing
  msg $ "Got lazy " ++ show res
  return res

vUnfoldLazyHead :: (Eval m) => Lvl -> VLazyHead -> m (Maybe VTm)
vUnfoldLazyHead l = \case
  VDef d -> access (unfoldDef d)
  VLit n -> return $ Just (VNorm (unfoldLit n))
  VLazyCase c -> do
    s <- vUnfoldLazy l c.subject
    case s of
      Just s' -> Just <$> vCase (c {subject = s'})
      Nothing -> return Nothing
  VRepr h -> do
    h' <- vWhnf l (headAsValue h)
    case h' of
      Just t -> Just <$> vRepr l 1 t
      Nothing -> vWhnfReprHead l 1 h

vWhnfReprHead :: (Eval m) => Lvl -> Int -> VHead -> m (Maybe VTm)
vWhnfReprHead _ 0 _ = return Nothing
vWhnfReprHead l i h = case h of
  VNeuHead h' -> vWhnfReprNeuHead h'
  VLazyHead h' -> vWhnfReprLazyHead h'
  VDataHead h' -> vWhnfReprGlob (DataGlob h') []
  VCtorHead (h', pp) -> vWhnfReprGlob (CtorGlob h') pp
  where
    vWhnfReprNeuHead :: (Eval m) =>  VNeuHead -> m (Maybe VTm)
    vWhnfReprNeuHead = \case
      VFlex _ -> return Nothing
      VRigid _ -> return Nothing
      VBlockedCase c -> vWhnfReprCase vBlockedCaseToSpine c
      VPrim _ -> return Nothing
      VUnrepr _ | i <= 0 -> return Nothing
      VUnrepr x -> Just <$> vRepr l (i - 1) (headAsValue x)

    vWhnfReprLazyHead :: (Eval m) =>  VLazyHead -> m (Maybe VTm)
    vWhnfReprLazyHead = \case
      VLit n -> Just <$> vRepr l i (VNorm (unfoldLit n))
      VLazyCase c -> vWhnfReprCase vLazyCaseToSpine c
      VDef d -> vWhnfReprGlob (DefGlob d) []
      VRepr _ -> return Nothing

    vWhnfReprCase ::
      (Eval m) =>
      (Case n VTm VPatB Closure -> m (Spine VTm)) ->
      Case n VTm VPatB Closure ->
      m (Maybe VTm)
    vWhnfReprCase toSpine c
      | i > 0 = do
          d' <- access (getCaseRepr c.dat)
          case d' of
            Just t -> do
              t' <- t $$ map (\a -> a.arg) (toList c.datParams)
              sp <- toSpine c
              res <- vApp t' sp
              Just <$> vRepr l i res
            _ -> return Nothing
      | otherwise = return Nothing

    vWhnfReprGlob :: (Eval m) =>  Glob -> [VTm] -> m (Maybe VTm)
    vWhnfReprGlob g xs
      | i > 0 = do
          d' <- access (getGlobalRepr g)
          case d' of
            Just t -> do
              res <- t $$ xs
              Just <$> vRepr l i res
            Nothing -> return Nothing
      | otherwise = return Nothing

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

postCompose :: (STm -> STm) -> Closure -> Closure
postCompose f (Closure n env t) = Closure n env (f t)

preCompose :: Closure -> (STm -> STm) -> Closure
preCompose (Closure n env t) f =
  assert (n == 1) $
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

reprClosure :: Int -> Closure -> Closure
reprClosure i t = preCompose (postCompose (sReprTimes i) t) (sReprTimes (-i))

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

vReprNTimes :: Int -> VHead -> VHead
vReprNTimes i = composeZ i (VLazyHead . VRepr) (VNeuHead . VUnrepr)

vRepr :: (Eval m) => Lvl -> Int -> VTm -> m VTm
vRepr _ 0 t = return t
vRepr l i t = do
  t' <- force t
  case t' of
    VNorm n -> vReprNorm n
    VNeu n -> vReprNeu n
    VLazy n -> vReprLazy n
  where
    vReprNorm :: (Eval m) => VNorm -> m VTm
    vReprNorm (VPi e v a b) = do
      ty' <- vRepr l i a
      let t' = reprClosure i b
      return . VNorm $ VPi e v ty' t'
    vReprNorm (VLam e v a) = do
      let t' = reprClosure i a
      return . VNorm $ VLam e v t'
    vReprNorm VU = return (VNorm VU)
    vReprNorm (VData (d, sp)) = do
      sp' <- mapSpineM (vRepr l i) sp
      vApp (headAsValue (vReprNTimes i (VDataHead d))) sp'
    vReprNorm (VCtor ((c, pp), sp)) = do
      -- pp' <- mapM (vRepr l i) pp
      sp' <- mapSpineM (vRepr l i) sp
      vApp (headAsValue (vReprNTimes i (VCtorHead (c, pp)))) sp'

    vReprNeu :: (Eval m) => VNeu -> m VTm
    vReprNeu (n, sp) = do
      sp' <- mapSpineM (vRepr l i) sp
      case n of
        VUnrepr x | i > 0 -> do
          x' <- vRepr l (i - 1) (headAsValue x)
          vApp x' sp'
        _ -> do
          vApp (headAsValue (vReprNTimes i (VNeuHead n))) sp'

    vReprLazy :: (Eval m) => VLazy -> m VTm
    vReprLazy (n, sp) = do
      sp' <- mapSpineM (vRepr l i) sp
      vApp (headAsValue (vReprNTimes i (VLazyHead n))) sp'

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
eval _ (SData d) = return $ VNorm (VData (d, Empty))
eval env (SCtor (c, pp)) = do
  pp' <- mapM (eval env) pp
  return $ VNorm (VCtor ((c, pp'), Empty))
eval _ (SDef d) = do
  return $ VLazy (VDef d, Empty)
eval _ (SPrim p) = do
  return $ VNeu (VPrim p, Empty)
eval env (SVar (Idx i)) = return $ env !! i
eval env (SRepr t) = do
  t' <- eval env t
  vRepr (envLvl env) 1 t'
eval env (SUnrepr t) = do
  t' <- eval env t
  vRepr (envLvl env) (-1) t'

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
    quotePat' l' (VNorm (VCtor ((c, pp), sp))) = do
      sp' <- mapSpineM (quotePat' l') sp
      pp' <- mapM (quote l') pp
      return $ sAppSpine (SCtor (c, pp')) sp'
    quotePat' _ (VNeu (VVar _)) = return $ SVar (Idx 0)
    quotePat' _ _ = error "impossible"

quoteCaseSpine :: (Eval m) => (Lvl -> s -> m STm) -> Lvl -> Case s VTm VPatB Closure -> Spine VTm -> m STm
quoteCaseSpine quoteSubject l (Case dat pp v i r cs) sp = do
  v' <- quoteSubject l v
  cs' <- mapM (bitraverse (quotePat l) (quoteClosure l)) cs
  r' <- quote l r
  pp' <- mapSpineM (quote l) pp
  i' <- mapSpineM (quote l) i
  quoteSpine l (SCase (Case dat pp' v' i' r' cs')) sp

quoteReprSpine :: (Eval m) => Lvl -> Int -> VTm -> Spine VTm -> m STm
quoteReprSpine l t n sp = do
  m' <- quote l n
  let hd = composeZ t SRepr SUnrepr m'
  quoteSpine l hd sp

quoteLazy :: (Eval m) => Lvl -> VLazy -> m STm
quoteLazy l (n, sp) = do
  case n of
    VDef d -> do
      ts <- access (getGlobalTags d.globalName)
      if UnfoldTag `elem` ts
        then do
          g' <- access (unfoldDef d)
          case g' of
            Just t -> do
              res <- vApp t sp
              quote l res
            _ -> quoteSpine l (SDef d) sp
        else quoteSpine l (SDef d) sp
    VLit t -> do
      t' <- traverse (quote l) t
      quoteSpine l (SLit t') sp
    VLazyCase c -> quoteCaseSpine quoteLazy l c sp
    VRepr n' -> quoteReprSpine l 1 (headAsValue n') sp

quoteNeu :: (Eval m) => Lvl -> VNeu -> m STm
quoteNeu l (n, sp) = case n of
    VFlex m -> quoteSpine l (SMeta m []) sp
    VRigid l' -> quoteSpine l (SVar (lvlToIdx l l')) sp
    VBlockedCase c -> quoteCaseSpine quoteNeu l c sp
    VPrim p -> quoteSpine l (SPrim p) sp
    VUnrepr n' -> quoteReprSpine l (-1) (headAsValue n') sp

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
quote l t = do
  t' <- force t
  case t' of
    (VNorm n) -> quoteNorm l n
    (VLazy n) -> quoteLazy l n
    (VNeu n) -> quoteNeu l n

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
  t' <- vUnfold l t
  case t' of
    VNorm (VPi _ _ _ b) -> do
      b' <- evalInOwnCtx l b
      isTypeFamily (nextLvl l) b'
    VNorm VU -> return True
    _ -> return False

isCtorTy :: (Eval m) => Lvl -> DataGlobal -> VTm -> m (Maybe (Spine ()))
isCtorTy l d t = do
  t' <- vUnfold l t
  case t' of
    VNorm (VPi _ _ _ b) -> do
      b' <- evalInOwnCtx l b
      isCtorTy (nextLvl l) d b'
    VNorm (VData (d', sp)) | d == d' -> return (Just (mapSpine (const ()) sp))
    _ -> return Nothing

ifIsData :: (Eval m) => Lvl -> VTy -> (DataGlobal -> Spine VTm -> m a) -> m a -> m a
ifIsData l v a b = do
  v' <- vUnfold l v
  case v' of
    VNorm (VData (d, sp)) -> a d sp
    _ -> b

ensureIsCtor :: (Eval m) => Lvl -> VTm -> CtorGlobal -> m () -> m ()
ensureIsCtor l v c a = do
  v' <- vUnfold l v
  case v' of
    VNorm (VCtor ((c', _), _)) | c == c' -> return ()
    _ -> a
