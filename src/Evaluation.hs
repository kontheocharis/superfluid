{-# LANGUAGE FlexibleContexts #-}

module Evaluation
  ( Eval (..),
    quote,
    nf,
    force,
    eval,
    ($$),
    vApp,
    vRepr,
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
    Idx (..),
    Lvl (..),
    Name,
    PiMode (..),
    Spine,
    Times (..),
    inv,
    lvlToIdx,
    mapSpineM,
    nextLvl,
    nextLvls,
    pattern Impossible,
    pattern Possible, HasNameSupply (..), MetaVar,
  )
import Control.Monad (foldM)
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.List.Extra (firstJust)
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), (><))
import qualified Data.Sequence as S
import Globals (HasSig (accessSig), getCaseRepr, getGlobalRepr)
import Meta (HasMetas (..))
import Syntax (STm (..), numBinds, sAppSpine, Bounds, BoundState (..))
import Value
  ( Closure (..),
    Env,
    VHead (..),
    VNeu (..),
    VPat,
    VPatB (..),
    VTm (..),
    pattern VMeta,
    pattern VVar,
  )

class (HasMetas m, HasSig m, HasNameSupply m) => Eval m where
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
vApp (VLam _ _ c) (Arg _ u :<| us) = do
  c' <- c $$ [u]
  vApp c' us
vApp (VGlobal g us) u = return $ VGlobal g (us >< u)
vApp (VNeu n) u = return $ vAppNeu n u
vApp _ _ = error "impossible"

vMatch :: VPat -> VTm -> Maybe (Env VTm)
vMatch (VNeu (VVar _)) u = Just [u]
vMatch (VGlobal (CtorGlob (CtorGlobal c)) ps) (VGlobal (CtorGlob (CtorGlobal c')) xs)
  | c == c' && length ps == length xs =
      foldM
        ( \acc (Arg _ p, Arg _ x) -> do
            env <- vMatch p x
            return $ env ++ acc
        )
        []
        (S.zip ps xs)
vMatch _ _ = Nothing

vCase :: (Eval m) => DataGlobal -> VNeu -> [Clause VPatB Closure] -> m VTm
vCase dat v cs =
  fromMaybe
    (return $ VNeu (VCaseApp dat v cs Empty))
    ( firstJust
        ( \clause -> do
            case clause of
              Possible p t -> case vMatch p.vPat (VNeu v) of
                Just env -> Just $ t $$ env
                Nothing -> Nothing
              Impossible _ -> Nothing
        )
        cs
    )

evalToNeu :: (Eval m) => Env VTm -> STm -> m VNeu
evalToNeu env t = do
  t' <- eval env t
  case t' of
    VNeu n -> return n
    _ -> error "impossible"

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
caseToSpine v cs = do
  return undefined -- @@Todo

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
vRepr l m (VGlobal g sp) = do
  g' <- accessSig (getGlobalRepr g)
  sp' <- mapSpineM (vRepr l m) sp
  vApp g' sp'
vRepr l m (VNeu (VCaseApp dat v cs sp)) = do
  f <- accessSig (getCaseRepr dat)
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

extendEnvByNVars :: Int -> Env VTm -> Env VTm
extendEnvByNVars n env = map (VNeu . VVar . Lvl . (+ length env)) [0 .. n - 1] ++ env

evalInOwnCtx :: (Eval m) => Closure -> m VTm
evalInOwnCtx cl = do
  let vars = extendEnvByNVars cl.numVars []
  cl $$ vars

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
  t' <- evalToNeu env t
  cs' <-
    mapM
      ( \p -> do
          let pat = p.pat
          let n = numBinds pat
          pat' <- eval (extendEnvByNVars n env) pat
          bitraverse (const $ return (VPatB pat' n)) (close n env) p
      )
      cs
  vCase dat t' cs'
eval _ SU = return VU
eval l (SLit i) = VLit <$> traverse (eval l) i
eval env (SMeta m bds) = do
  m' <- vMeta m
  vAppBinds env m' bds
eval _ (SGlobal g) = return $ VGlobal g Empty
eval env (SVar (Idx i)) = return $ env !! i
eval env (SRepr m t) = do
  t' <- eval env t
  vRepr (envQuoteLvl env) m t'

vAppBinds :: (Eval m) => Env VTm -> VTm -> Bounds -> m VTm
vAppBinds env v binds = case (env, binds) of
  ([], []) -> return v
  (x : env', Bound : binds') -> do
    v' <- vApp v (S.singleton (Arg Explicit x))
    vAppBinds env' v' binds'
  (_, Defined : binds') -> vAppBinds env v binds'
  _ -> error "impossible"

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

quote :: (Eval m) => Lvl -> VTm -> m STm
quote l vt = do
  vt' <- force vt
  case vt' of
    VLam m x t -> do
      a <- t $$ [VNeu (VVar l)]
      t' <- quote (nextLvl l) a
      return $ SLam m x t'
    VPi m x ty t -> do
      ty' <- quote l ty
      a <- t $$ [VNeu (VVar l)]
      t' <- quote (nextLvl l) a
      return $ SPi m x ty' t'
    VU -> return SU
    VLit lit -> SLit <$> traverse (quote l) lit
    VGlobal g sp -> quoteSpine l (SGlobal g) sp
    VNeu (VApp h sp) -> quoteSpine l (quoteHead l h) sp
    VNeu (VReprApp m v sp) -> quoteSpine l (SRepr m (quoteHead l v)) sp
    VNeu (VCaseApp dat v cs sp) -> do
      v' <- quote l (VNeu v)
      cs' <-
        mapM
          ( \pt -> do
              let n = pt.pat.numBinds
              bitraverse
                (\p -> quote (nextLvls l n) p.vPat)
                ( \t -> do
                    a <- t $$ extendEnvByNVars n []
                    quote (nextLvls l n) a
                )
                pt
          )
          cs
      quoteSpine l (SCase dat v' cs') sp

nf :: (Eval m) => Env VTm -> STm -> m STm
nf env t = do
  t' <- eval env t
  quote (envQuoteLvl env) t'

envQuoteLvl :: Env VTm -> Lvl
envQuoteLvl env = Lvl (length env)
