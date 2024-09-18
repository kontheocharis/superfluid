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
    unfoldDefs,
    quoteSpine,
    ensureIsCtor,
    vLams,
    vCase,
    vReprTel,
    reprInfSig,
    uniqueVLams,
    evalInOwnCtx,
    extendEnvByNVars,
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
    Spine,
    Tel,
    Times (..),
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
import Control.Monad.State (StateT (..))
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.Trans (MonadTrans (..))
import Data.Bitraversable (Bitraversable (bitraverse))
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
    getGlobalRepr,
    unfoldDef, mapSigContentsM, removeRepresentedItems,
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
    VCase,
    VHead (..),
    VNeu (..),
    VPat,
    VPatB (..),
    VTm (..),
    VTy,
    mapClosureM,
    sAppSpine,
    sLams,
    uniqueSLams,
    pattern VGlob,
    pattern VHead,
    pattern VMeta,
    pattern VRepr,
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

vAppNeu :: VNeu -> Spine VTm -> VTm
vAppNeu (VApp h us) u = VNeu (VApp h (us >< u))
vAppNeu (VReprApp m h us) u = VNeu (VReprApp m h (us >< u))
vAppNeu (VCaseApp c us) u = VNeu (VCaseApp c (us >< u))

vApp :: (Eval m) => VTm -> Spine VTm -> m VTm
vApp a Empty = return a
vApp (VLam _ _ c) (Arg _ u :<| us) = do
  c' <- c $$ [u]
  vApp c' us
vApp (VNeu n) u = return $ vAppNeu n u
vApp a b = error $ "impossible " ++ show a ++ " AND " ++ show b

uniqueVLams :: (Eval m) => [PiMode] -> Closure -> m VTm
uniqueVLams ms t = do
  sp <- fromList <$> mapM (\m -> Arg m <$> uniqueName) ms
  vLams sp t

vLams :: (Eval m) => Spine Name -> Closure -> m VTm
vLams Empty t = do
  t $$ []
vLams (Arg m x :<| sp) t = do
  let inner = sLams sp t.body
  return $ VLam m x (Closure (t.numVars + 1) t.env inner)

vMatch :: VPat -> VTm -> Maybe (Env VTm)
vMatch (VNeu (VVar _)) u = Just [u]
vMatch (VNeu (VApp (VGlobal (CtorGlob (CtorGlobal c)) _) ps)) (VNeu (VApp (VGlobal (CtorGlob (CtorGlobal c')) _) xs))
  | c == c' && length ps == length xs =
      foldM
        ( \acc (Arg _ p, Arg _ x) -> do
            env <- vMatch p x
            return $ acc ++ env
        )
        []
        (S.zip ps xs)
vMatch _ _ = Nothing

vCase :: (Eval m) => Case VTm VTm VPatB Closure -> m VTm
vCase c@(Case dat xs v i e cs) = do
  v' <- force v
  case v' of
    VLit l -> vCase (Case dat xs (unfoldLit l) i e cs)
    VNeu n ->
      fromMaybe (return $ VNeu (VCaseApp (c {subject = n}) Empty)) $
        firstJust
          ( \clause -> do
              case clause of
                Possible p t -> case vMatch p.vPat v of
                  Just env -> Just $ t $$ env
                  Nothing -> Nothing
                Impossible _ -> Nothing
          )
          cs
    _ -> error "impossible"

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

reprClosure :: (Eval m) => Times -> Closure -> m Closure
reprClosure m t = do
  a <- postCompose (SRepr m) t
  preCompose a (SRepr (inv m))

caseToSpine :: (Eval m) => SCase -> m (Spine STm)
caseToSpine c = do
  firstPart <-
    foldM
      ( \acc -> \case
          Possible p t -> do
            t' <- uniqueSLams (map (const Explicit) p.binds) t
            return $ acc :|> Arg Explicit t'
          Impossible _ -> return acc
      )
      (c.datParams :|> Arg Explicit c.elimTy)
      c.clauses
  return $ firstPart >< c.subjectIndices >< S.singleton (Arg Explicit c.subject)

mapDataGlobalInfoM :: (Eval m) => (STm -> m STm) -> DataGlobalInfo -> m DataGlobalInfo
mapDataGlobalInfoM f (DataGlobalInfo params fullTy ty ctors motiveTy elimTy indexArity) = do
  params' <- traverse (traverse f) params
  fullTy' <- quote (Lvl 0) fullTy >>= f >>= eval []
  ty' <- mapClosureM f ty
  motiveTy' <- traverse (mapClosureM f) motiveTy
  elimTy' <- traverse (mapClosureM f) elimTy
  return $ DataGlobalInfo params' fullTy' ty' ctors motiveTy' elimTy' indexArity

mapCtorGlobalInfoM :: (Eval m) => (STm -> m STm) -> CtorGlobalInfo -> m CtorGlobalInfo
mapCtorGlobalInfoM f (CtorGlobalInfo ty idx dataGlobal argArity) = do
  ty' <- mapClosureM f ty
  return $ CtorGlobalInfo ty' idx dataGlobal argArity

mapDefGlobalInfoM :: (Eval m) => (STm -> m STm) -> DefGlobalInfo -> m DefGlobalInfo
mapDefGlobalInfoM f (DefGlobalInfo ty vtm tm) = do
  ty' <- quote (Lvl 0) ty >>= f >>= eval []
  vtm' <- traverse (quote (Lvl 0) >=> f >=> eval []) vtm
  tm' <- traverse f tm
  return $ DefGlobalInfo ty' vtm' tm'

mapPrimGlobalInfoM :: (Eval m) => (STm -> m STm) -> PrimGlobalInfo -> m PrimGlobalInfo
mapPrimGlobalInfoM f (PrimGlobalInfo ty) = do
  ty' <- quote (Lvl 0) ty >>= f >>= eval []
  return $ PrimGlobalInfo ty'

mapGlobalInfoM :: (Eval m) => (STm -> m STm) -> GlobalInfo -> m GlobalInfo
mapGlobalInfoM f i = case i of
  DataInfo d -> DataInfo <$> mapDataGlobalInfoM f d
  CtorInfo c -> CtorInfo <$> mapCtorGlobalInfoM f c
  DefInfo d -> DefInfo <$> mapDefGlobalInfoM f d
  PrimInfo p -> PrimInfo <$> mapPrimGlobalInfoM f p

vReprTel :: (Eval m) => Lvl -> Times -> Tel STm -> m (Tel STm)
vReprTel _ _ Empty = return Empty
vReprTel l m (Param m' n a :<| xs) = do
  a' <- (\a' -> a'.body) <$> postCompose (SRepr m) (Closure 0 [] a)
  xs' <- vReprTel l m xs
  xs'' <- traverse (traverse (\x -> (\x' -> x'.body) <$> reprClosure m (Closure 0 [] x))) xs'
  return $ Param m' n a' :<| xs''

vRepr :: (Eval m) => Lvl -> Times -> VTm -> m VTm
vRepr _ (Finite 0) t = return t
vRepr l m (VPi e v ty t) = do
  ty' <- vRepr l m ty
  t' <- reprClosure m t
  return $ VPi e v ty' t'
vRepr _ m (VLam e v t) = do
  t' <- reprClosure m t
  return $ VLam e v t'
vRepr _ _ VU = return VU
vRepr _ _ (VLit i) = return $ VLit i
vRepr l m (VNeu n@(VApp (VGlobal g pp) sp))
  | m > mempty = do
      r <- access (getGlobalRepr g)
      case r of
        Just r' -> do
          r'' <- r' $$ pp
          res <- vApp r'' sp
          vRepr l m res
        Nothing -> return $ VNeu (VRepr m n)
  | otherwise = return $ VNeu (VRepr m n)
vRepr _ m (VNeu n@(VCaseApp {})) = do
  return $ VNeu (VRepr m n)
vRepr l m (VNeu h@(VReprApp m' v sp))
  | (m > Finite 0 && m' < Finite 0)
      || (m > Finite 0 && m' > Finite 0)
      || (m < Finite 0 && m' < Finite 0) = do
      sp' <- mapSpineM (vRepr l m) sp
      let mm' = m <> m'
      if mm' == mempty
        then do
          return $ vAppNeu v sp'
        else
          return $ VNeu (VReprApp mm' v sp')
  | otherwise = return $ VNeu (VReprApp m h Empty)
vRepr _ m (VNeu n@(VApp (VFlex _) _)) = do
  return $ VNeu (VRepr m n)
vRepr l m (VNeu (VApp h sp)) = do
  sp' <- mapSpineM (vRepr l m) sp
  return (VNeu (VReprApp m (VApp h Empty) sp'))

reprInfSig :: (Eval m) => m ()
reprInfSig = do
  s <- view
  let s' = removeRepresentedItems s
  s'' <- mapSigContentsM (mapGlobalInfoM sReprInf) s'
  modify (const s'')

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
sReprInf (SGlobal g xs) = do
  r <- access (getGlobalRepr g)
  case r of
    Just r' -> do
      r'' <- closureToLam r'
      let res = sAppSpine r'' (S.fromList (map (Arg Explicit) xs))
      sReprInf res
    Nothing -> do
      xs' <- mapM sReprInf xs
      return $ SGlobal g xs'
sReprInf (SCase c) = do
  r <- access (getCaseRepr c.dat)
  case r of
    Just r' -> do
      r'' <- closureToLam r'
      sp <- caseToSpine c
      let res = sAppSpine r'' sp
      sReprInf res
    Nothing -> do
      datParams' <- mapSpineM sReprInf c.datParams
      subject' <- sReprInf c.subject
      subjectIndices' <- mapSpineM sReprInf c.subjectIndices
      elimTy' <- sReprInf c.elimTy
      clauses' <- traverse (bitraverse return sReprInf) c.clauses
      return $ SCase (Case c.dat datParams' subject' subjectIndices' elimTy' clauses')
sReprInf (SRepr _ x) = sReprInf x
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
      (SGlobal (CtorGlob (CtorGlobal c)) pp) -> do
        pp' <- mapM (lift . eval e) pp
        return $ VNeu (VApp (VGlobal (CtorGlob (CtorGlobal c)) pp') Empty)
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
  return $ VPi m v ty1' c
eval env (SLam m v t) = do
  c <- close 1 env t
  return $ VLam m v c
eval env (SLet _ _ t1 t2) = do
  t1' <- eval env t1
  eval (t1' : env) t2
eval env (SApp m t1 t2) = do
  t1' <- eval env t1
  t2' <- eval env t2
  vApp t1' (S.singleton (Arg m t2'))
eval env (SCase (Case dat pp t i r cs)) = do
  t' <- eval env t
  cs' <- mapM (\p -> do bitraverse (evalPat (extendEnvByNVars (length p.pat.binds) env)) (close (length p.pat.binds) env) p) cs
  r' <- eval env r
  i' <- mapSpineM (eval env) i
  pp' <- mapSpineM (eval env) pp
  vCase (Case dat pp' t' i' r' cs')
eval _ SU = return VU
eval l (SLit i) = VLit <$> traverse (eval l) i
eval env (SMeta m bds) = do
  m' <- vMeta m
  vAppBinds env m' bds
eval env (SGlobal g pp) = do
  pp' <- mapM (eval env) pp
  return $ VNeu (VHead (VGlobal g pp'))
eval env (SVar (Idx i)) = return $ env !! i
eval env (SRepr m t) = do
  t' <- eval env t
  vRepr (envLvl env) m t'

vAppBinds :: (Eval m) => Env VTm -> VTm -> Bounds -> m VTm
vAppBinds env v binds = case (drop (length env - length binds) env, binds) of
  (_, []) -> return v
  (x : env', Bound : binds') -> do
    -- v' <- vAppBinds env' v binds'
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
force v@(VNeu (VApp (VFlex m) sp)) = do
  mt <- lookupMetaVar m
  case mt of
    Just t -> do
      t' <- vApp t sp
      force t'
    Nothing -> return v
force v = return v

unfoldDefs :: (Eval m) => VTm -> m VTm
unfoldDefs s = case s of
  VNeu (VApp (VGlobal (DefGlob g) _) sp) -> do
    g' <- access (unfoldDef g)
    case g' of
      Just t -> vApp t sp >>= unfoldDefs
      _ -> return s
  _ -> return s

quoteSpine :: (Eval m) => Lvl -> STm -> Spine VTm -> m STm
quoteSpine _ t Empty = return t
quoteSpine l t (sp :|> Arg m u) = do
  t' <- quoteSpine l t sp
  u' <- quote l u
  return $ SApp m t' u'

quoteHead :: (Eval m) => Lvl -> VHead -> m STm
quoteHead _ (VFlex m) = return $ SMeta m []
quoteHead l (VRigid l') = return $ SVar (lvlToIdx l l')
quoteHead l (VGlobal g pp) = do
  pp' <- mapM (quote l) pp
  return $ SGlobal g pp'

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
    quotePat' l' (VNeu (VApp vh sp)) = do
      sp' <- mapSpineM (quotePat' l') sp
      vh' <- quotePatHead l' vh
      return $ sAppSpine vh' sp'
    quotePat' _ _ = error "impossible"
    quotePatHead :: (Eval m) => Lvl -> VHead -> m STm
    quotePatHead _ (VFlex _) = error "impossible"
    quotePatHead _ (VRigid _) = return $ SVar (Idx 0)
    quotePatHead _ (VGlobal g pp) = do
      pp' <- mapM (quote l) pp
      return $ SGlobal g pp'

quoteNeu :: (Eval m) => Lvl -> VNeu -> m STm
quoteNeu l vt = case vt of
  (VApp h sp) -> do
    h' <- quoteHead l h
    quoteSpine l h' sp
  (VReprApp m v sp) -> do
    v' <- quoteNeu l v
    quoteSpine l (SRepr m v') sp
  (VCaseApp (Case dat pp v i r cs) sp) -> do
    v' <- quote l (VNeu v)
    cs' <- mapM (bitraverse (quotePat l) (quoteClosure l)) cs
    r' <- quote l r
    pp' <- mapSpineM (quote l) pp
    i' <- mapSpineM (quote l) i
    quoteSpine l (SCase (Case dat pp' v' i' r' cs')) sp

quote :: (Eval m) => Lvl -> VTm -> m STm
quote l vt = do
  vt' <- force vt
  case vt' of
    VLam m x t -> do
      t' <- quoteClosure l t
      return $ SLam m x t'
    VPi m x ty t -> do
      ty' <- quote l ty
      t' <- quoteClosure l t
      return $ SPi m x ty' t'
    VU -> return SU
    VLit lit -> SLit <$> traverse (quote l) lit
    VNeu n -> quoteNeu l n

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
  t' <- force t >>= unfoldDefs
  case t' of
    (VPi _ _ _ b) -> do
      b' <- evalInOwnCtx l b
      isTypeFamily (nextLvl l) b'
    VU -> return True
    _ -> return False

isCtorTy :: (Eval m) => Lvl -> DataGlobal -> VTm -> m (Maybe (Spine ()))
isCtorTy l d t = do
  t' <- force t >> unfoldDefs t
  case t' of
    (VPi _ _ _ b) -> do
      b' <- evalInOwnCtx l b
      isCtorTy (nextLvl l) d b'
    (VNeu (VApp (VGlobal (DataGlob d') _) sp)) | d == d' -> return (Just (mapSpine (const ()) sp))
    _ -> return Nothing

ifIsData :: (Eval m) => VTy -> (DataGlobal -> Spine VTm -> m a) -> m a -> m a
ifIsData v a b = do
  v' <- force v >>= unfoldDefs
  case v' of
    VGlob (DataGlob g@(DataGlobal _)) sp -> a g sp
    _ -> b

ensureIsCtor :: (Eval m) => VTm -> CtorGlobal -> m () -> m ()
ensureIsCtor v c a = do
  v' <- force v >>= unfoldDefs
  case v' of
    VNeu (VApp (VGlobal (CtorGlob c') _) _) | c == c' -> return ()
    _ -> a
