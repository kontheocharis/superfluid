{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Evaluation
  ( Eval (..),
    quote,
    nf,
    resolve,
    force,
    eval,
    isTypeFamily,
    isCtorTy,
    unelab,
    ($$),
    vApp,
    vRepr,
    vLams,
    uniqueVLams,
    evalInOwnCtx,
    close,
  )
where

import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal (..),
    DataGlobal,
    Glob (..),
    Has (..),
    HasNameSupply (..),
    Idx (..),
    Lvl (..),
    MetaVar,
    Name (..),
    PiMode (..),
    Spine,
    Times (..),
    View (..),
    globName,
    inv,
    lvlToIdx,
    mapSpineM,
    nextLvl,
    nextLvls,
    unMetaVar,
    pattern Impossible,
    pattern Possible,
  )
import Control.Arrow ((***))
import Control.Monad (foldM)
import Control.Monad.State (StateT (..), modify)
import Control.Monad.State.Class (MonadState (..), gets)
import Control.Monad.Trans (MonadTrans (..))
import Data.Bitraversable (Bitraversable (bitraverse))
import qualified Data.IntMap as IM
import Data.List.Extra (firstJust, intercalate)
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), fromList, (><))
import qualified Data.Sequence as S
import Debug.Trace (trace, traceM)
import Globals (Sig, getCaseRepr, getGlobalRepr)
import Meta (HasMetas, SolvedMetas, lookupMetaVar, lookupMetaVarName)
import Presyntax (PTm (..), pApp)
import Printing (Pretty (..))
import Syntax (BoundState (..), Bounds, SPat (..), STm (..), sAppSpine, sLams, uniqueSLams)
import Value
  ( Closure (..),
    Env,
    Sub,
    VHead (..),
    VNeu (..),
    VPat,
    VPatB (..),
    VTm (..),
    vars,
    pattern VGl,
    pattern VMeta,
    pattern VVar,
  )

class (Has m SolvedMetas, Has m Sig, HasNameSupply m) => Eval m where
  reduceUnderBinders :: m Bool
  setReduceUnderBinders :: Bool -> m ()

  reduceUnfoldDefs :: m Bool
  setReduceUnfoldDefs :: Bool -> m ()

infixl 8 $$

($$) :: (Eval m) => Closure -> [VTm] -> m VTm
Closure _ env t $$ us = eval (us ++ env) t

vAppNeu :: VNeu -> Spine VTm -> VTm
vAppNeu (VApp h us) u = VNeu (VApp h (us >< u))
vAppNeu (VReprApp m h us) u = VNeu (VReprApp m h (us >< u))
vAppNeu (VCaseApp dat c cls us) u = VNeu (VCaseApp dat c cls (us >< u))

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
vMatch (VNeu (VApp (VGlobal (CtorGlob (CtorGlobal c))) ps)) (VNeu (VApp (VGlobal (CtorGlob (CtorGlobal c'))) xs))
  | c == c' && length ps == length xs =
      foldM
        ( \acc (Arg _ p, Arg _ x) -> do
            env <- vMatch p x
            return $ env ++ acc
        )
        []
        (S.zip ps xs)
vMatch _ _ = Nothing

vCase :: (Eval m) => DataGlobal -> VTm -> [Clause VPatB Closure] -> m VTm
vCase dat v cs =
  case v of
    VNeu n -> return $ VNeu (VCaseApp dat n cs Empty)
    _ ->
      fromMaybe (return . error $ "Expected neutral, got " ++ show v) $
        firstJust
          ( \clause -> do
              case clause of
                Possible p t -> case vMatch p.vPat v of
                  Just env -> Just $ t $$ env
                  Nothing -> Nothing
                Impossible _ -> Nothing
          )
          cs

evalToNeu :: (Eval m) => Env VTm -> STm -> m VNeu
evalToNeu env t = do
  t' <- eval env t
  case t' of
    VNeu n -> return n
    _ -> error $ "expected neutral term, got " ++ show t'

postCompose :: (Eval m) => (STm -> STm) -> Closure -> m Closure
postCompose f (Closure n env t) = return $ Closure n env (f t)

preCompose :: (Eval m) => Closure -> (STm -> STm) -> m Closure
preCompose (Closure n env t) f = do
  v <- uniqueName
  return $ Closure n env (SApp Explicit (SLam Explicit v t) (f (SVar (Idx 0))))

reprClosure :: (Eval m) => Times -> Closure -> m Closure
reprClosure m t = do
  a <- postCompose (SRepr m) t
  preCompose a (SRepr (inv m))

caseToSpine :: (Eval m) => VNeu -> [Clause VPatB Closure] -> m (Spine VTm)
caseToSpine v cls = do
  foldM
    ( \acc -> \case
        Possible p t -> do
          t' <- uniqueVLams (map (const Explicit) p.binds) t
          return $ Arg Explicit t' :<| acc
        Impossible _ -> return acc
    )
    (Arg Explicit (VNeu v) :<| Empty)
    cls

vRepr :: (Eval m) => Lvl -> Times -> VTm -> m VTm
vRepr l (Finite 0) t = return t
vRepr l m (VPi e v ty t) = do
  ty' <- vRepr l m ty
  t' <- reprClosure m t
  return $ VPi e v ty' t'
vRepr l m (VLam e v t) = do
  t' <- reprClosure m t
  return $ VLam e v t'
vRepr l _ VU = return VU
vRepr l _ (VLit i) = return $ VLit i
vRepr l m (VNeu (VApp (VGlobal g) sp)) = do
  g' <- access (getGlobalRepr g)
  sp' <- mapSpineM (vRepr l m) sp
  vApp g' sp'
vRepr l m (VNeu (VCaseApp dat v cs sp)) = do
  f <- access (getCaseRepr dat)
  cssp <- caseToSpine v cs
  cssp' <- mapSpineM (vRepr l m) cssp
  a <- vApp f cssp'
  vApp a sp
vRepr l m (VNeu (VApp h sp)) = do
  sp' <- mapSpineM (vRepr l m) sp
  return $ VNeu (VReprApp m h sp')
vRepr l m (VNeu (VReprApp m' v sp)) = do
  sp' <- mapSpineM (vRepr l m) sp
  let mm' = m <> m'
  if mm' == mempty
    then
      return $ VNeu (VApp v sp')
    else
      return $ VNeu (VReprApp mm' v sp')

close :: (Eval m) => Int -> Env VTm -> STm -> m Closure
close n env t = do
  b <- reduceUnderBinders
  if b
    then do
      t' <- nf (extendEnvByNVars n env) t
      return $ Closure n env t'
    else return $ Closure n env t

closureArgs :: Int -> Int -> [VTm]
closureArgs n envLen = map (VNeu . VVar . Lvl . (+ envLen)) [0 .. n - 1]

extendEnvByNVars :: Int -> Env VTm -> Env VTm
extendEnvByNVars numVars env = closureArgs numVars (length env) ++ env

evalInOwnCtx :: (Eval m) => Closure -> m VTm
evalInOwnCtx cl = cl $$ closureArgs cl.numVars (length cl.env)

-- evalPat :: (Eval m) => Env VTm -> SPat -> m VPatB
-- evalPat env pat = do
--   pat' <- eval (extendEnvByNVars (length pat.binds) env) pat.asTm
--   return (VPatB pat' pat.binds)

type NumPatBinds = Int

evalPat :: (Eval m) => Env VTm -> SPat -> m VPatB
evalPat env pat = do
  (n, _) <- runStateT (evalPat' env pat.asTm) (length env)
  return $ VPatB n pat.binds
  where
    evalPat' :: (Eval m) => Env VTm -> STm -> StateT NumPatBinds m VTm
    evalPat' e pat' = case pat' of
      (SGlobal (CtorGlob (CtorGlobal c))) -> do
        return $ VNeu (VApp (VGlobal (CtorGlob (CtorGlobal c))) Empty)
      (SApp m a b) -> do
        a' <- evalPat' e a
        b' <- evalPat' e b
        lift $ vApp a' (S.singleton (Arg m b'))
      (SVar (Idx 0)) -> state (\s -> (VNeu (VVar (Lvl s)), s + 1))
      _ -> error "impossible"

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
eval env (SCase dat t cs) = do
  t' <- eval env t
  cs' <- mapM (\p -> do bitraverse (evalPat env) (close (length p.pat.binds) env) p) cs
  vCase dat t' cs'
eval _ SU = return VU
eval l (SLit i) = VLit <$> traverse (eval l) i
eval env (SMeta m bds) = do
  m' <- vMeta m
  vAppBinds env m' bds
eval _ (SGlobal g) = do
  return $ VGl g
eval env (SVar (Idx i)) = return $ env !! i
eval env (SRepr m t) = do
  t' <- eval env t
  vRepr (envLvl env) m t'

vAppBinds :: (Eval m) => Env VTm -> VTm -> Bounds -> m VTm
vAppBinds env v binds = case (env, binds) of
  (_, []) -> return v
  (x : env', Bound : binds') -> do
    v' <- vAppBinds env' v binds'
    vApp v' (S.singleton (Arg Explicit x))
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

quoteSpine :: (Eval m) => Lvl -> STm -> Spine VTm -> m STm
quoteSpine l t Empty = return t
quoteSpine l t (sp :|> Arg m u) = do
  t' <- quoteSpine l t sp
  u' <- quote l u
  return $ SApp m t' u'

quoteHead :: Lvl -> VHead -> STm
quoteHead _ (VFlex m) = SMeta m []
quoteHead l (VRigid l') = SVar (lvlToIdx l l')
quoteHead _ (VGlobal g) = SGlobal g

quoteClosure :: (Eval m) => Lvl -> Closure -> m STm
quoteClosure l cl = do
  a <- evalInOwnCtx cl
  quote (nextLvls l cl.numVars) a

quotePat :: (Eval m) => Lvl -> VPatB -> m SPat
quotePat l p = do
  p' <- quotePat' l p.vPat
  return $ SPat p' p.binds
  where
    quotePat' :: (Eval m) => Lvl -> VTm -> m STm
    quotePat' l' (VNeu (VApp vh sp)) = do
      sp' <- mapSpineM (quotePat' l') sp
      return $ sAppSpine (quotePatHead l' vh) sp'
    quotePat' _ _ = error "impossible"
    quotePatHead :: Lvl -> VHead -> STm
    quotePatHead _ (VFlex _) = error "impossible"
    quotePatHead _ (VRigid _) = SVar (Idx 0)
    quotePatHead _ (VGlobal g) = SGlobal g

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
    VNeu (VApp h sp) -> quoteSpine l (quoteHead l h) sp
    VNeu (VReprApp m v sp) -> quoteSpine l (SRepr m (quoteHead l v)) sp
    VNeu (VCaseApp dat v cs sp) -> do
      v' <- quote l (VNeu v)
      cs' <- mapM (bitraverse (quotePat l) (quoteClosure l)) cs
      quoteSpine l (SCase dat v' cs') sp

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
  t' <- force t
  case t' of
    (VPi _ _ _ b) -> do
      b' <- evalInOwnCtx b
      isTypeFamily (nextLvl l) b'
    VU -> return True
    _ -> return False

isCtorTy :: (Eval m) => Lvl -> DataGlobal -> VTm -> m Bool
isCtorTy l d t = do
  t' <- force t
  case t' of
    (VPi _ _ _ b) -> do
      b' <- evalInOwnCtx b
      isCtorTy (nextLvl l) d b'
    (VNeu (VApp (VGlobal (DataGlob d')) _)) -> return $ d == d'
    _ -> return False

unelabMeta :: (HasMetas m) => [Name] -> MetaVar -> Bounds -> m (PTm, [Arg PTm])
unelabMeta _ m [] = do
  n <- lookupMetaVarName m
  case n of
    Just n' -> return (PHole n', [])
    Nothing -> return (PHole (Name $ "m" ++ show m.unMetaVar), [])
unelabMeta (n : ns) m (Bound : bs) = do
  (t, ts) <- unelabMeta ns m bs
  return (t, Arg Explicit (PName n) : ts)
unelabMeta (_ : ns) m (Defined : bs) = unelabMeta ns m bs
unelabMeta _ _ _ = error "impossible"

unelabPat :: (HasMetas m) => [Name] -> SPat -> m PTm
unelabPat ns pat = do
  (n, _) <- runStateT (unelabPat' pat.asTm) (pat.binds ++ ns)
  return n
  where
    unelabPat' :: (HasMetas m) => STm -> StateT [Name] m PTm
    unelabPat' pat' = case pat' of
      (SGlobal (CtorGlob (CtorGlobal c))) -> do
        return $ PName c
      (SApp m a b) -> do
        a' <- unelabPat' a
        b' <- unelabPat' b
        return $ pApp a' [Arg m b']
      (SVar (Idx 0)) ->
        state
          ( \case
              (v : vs) -> (PName v, vs)
              [] -> error "impossible"
          )
      _ -> error "impossible"

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
            <$> unelabPat ns c.pat
            <*> traverse (unelab (c.pat.binds ++ ns)) c.branch
      )
      cs
unelab _ SU = return PU
unelab _ (SGlobal g) = return $ PName (globName g)
unelab ns (SLit l) = PLit <$> traverse (unelab ns) l
unelab ns (SRepr m t) = PRepr m <$> unelab ns t

instance (Eval m, Has m [Name]) => Pretty m VTm where
  pretty v = do
    n <- view
    traceM $ show (v, n)
    q <- quote (Lvl (length n)) v
    traceM $ show q
    return q >>= unelab n >>= pretty

instance (Eval m, Has m [Name]) => Pretty m STm where
  pretty t = do
    n <- view
    unelab n t >>= pretty

instance (Eval m, Has m [Name]) => Pretty m Closure where
  pretty cl = do
    cl' <- evalInOwnCtx cl
    pretty cl'

instance (Eval m, Has m [Name]) => Pretty m VPatB where
  pretty (VPatB pat names) = enter (\n -> names ++ n) $ pretty pat

instance (Eval m, Has m [Name]) => Pretty m Sub where
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
