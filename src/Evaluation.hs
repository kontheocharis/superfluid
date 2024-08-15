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
    pattern Possible,
  )
import Control.Monad (foldM)
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.List.Extra (firstJust)
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), (><))
import qualified Data.Sequence as S
import Meta (HasSolvedMetas (..))
import Syntax (STm (..), numBinds, sAppSpine)
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
import Globals (CtorGlobal(..), Glob (..))

class (HasSolvedMetas m) => Eval m where
  reduceUnderBinders :: m Bool
  setReduceUnderBinders :: Bool -> m ()

  reduceUnfoldDefs :: m Bool
  setReduceUnfoldDefs :: Bool -> m ()

  uniqueName :: m Name

infixl 8 $$

($$) :: (Eval m) => Closure -> [VTm] -> m VTm
Closure _ env t $$ us = eval (us ++ env) t

vAppNeu :: (Eval m) => Lvl -> VNeu -> Spine VTm -> m VTm
vAppNeu _ (VApp h us) u = return $ VNeu (VApp h (us >< u))
vAppNeu _ (VReprApp m h us) u = return $ VNeu (VReprApp m h (us >< u))
vAppNeu l (VCase c cls) u =
  VNeu . VCase c
    <$> mapM
      ( \cl -> do
          u' <- traverse (traverse (quote (nextLvls l cl.pat.numBinds))) u
          bitraverse return (postCompose (`sAppSpine` u')) cl
      )
      cls

vApp :: (Eval m) => Lvl -> VTm -> Spine VTm -> m VTm
vApp l (VLam _ _ c) (Arg _ u :<| us) = do
  c' <- c $$ [u]
  vApp l c' us
vApp _ (VGlobal g us) u = return $ VGlobal g (us >< u)
vApp l (VNeu n) u = vAppNeu l n u
vApp _ _ _ = error "impossible"

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

vCase :: (Eval m) => VNeu -> [Clause VPatB Closure] -> m VTm
vCase v cs =
  fromMaybe
    (return $ VNeu (VCase v cs))
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

vRepr :: (Eval m) => Times -> VTm -> m VTm
vRepr (Finite 0) t = return t
vRepr m (VPi e v ty t) = do
  ty' <- vRepr m ty
  t' <- reprClosure m t
  return $ VPi e v ty' t'
vRepr m (VLam e v t) = do
  t' <- reprClosure m t
  return $ VLam e v t'
vRepr _ VU = return VU
vRepr _ (VLit l) = return $ VLit l
vRepr m (VGlobal g sp) = return undefined -- @@TODO
vRepr m (VNeu (VCase (VCase v cs) sp)) = return undefined -- @@TODO
vRepr m (VNeu (VApp h sp)) = do
  sp' <- mapSpineM (vRepr m) sp
  return $ VNeu (VReprApp m h sp')
vRepr m (VNeu (VReprApp m' v sp)) = do
  sp' <- mapSpineM (vRepr m) sp
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
  vApp (envQuoteLvl env) t1' (S.singleton (Arg m t2'))
eval env (SCase t cs) = do
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
  vCase t' cs'
eval _ SU = return VU
eval _ (SLit l) = return $ VLit l
eval _ (SMeta m) = return $ VNeu (VMeta m)
eval _ (SGlobal g) = return $ VGlobal g Empty
eval env (SVar (Idx i)) = return $ env !! i
eval env (SRepr m t) = do
  t' <- eval env t
  vRepr m t'

force :: (Eval m) => Lvl -> VTm -> m VTm
force l v@(VNeu (VApp (VFlex m) sp)) = do
  mt <- lookupMeta m
  case mt of
    Just t -> do
      t' <- vApp l t sp
      force l t'
    Nothing -> return v
force _ v = return v

quoteSpine :: (Eval m) => Lvl -> STm -> Spine VTm -> m STm
quoteSpine l t Empty = return t
quoteSpine l t (sp :|> Arg m u) = do
  t' <- quoteSpine l t sp
  u' <- quote l u
  return $ SApp m t' u'

quoteHead :: Lvl -> VHead -> STm
quoteHead _ (VFlex m) = SMeta m
quoteHead l (VRigid l') = SVar (lvlToIdx l l')

quote :: (Eval m) => Lvl -> VTm -> m STm
quote l vt = do
  vt' <- force l vt
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
    VLit lit -> return $ SLit lit
    VGlobal g sp -> quoteSpine l (SGlobal g) sp
    VNeu (VApp h sp) -> quoteSpine l (quoteHead l h) sp
    VNeu (VReprApp m v sp) -> quoteSpine l (SRepr m (quoteHead l v)) sp
    VNeu (VCase v cs) -> do
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
      return $ (SCase v' cs')

nf :: (Eval m) => Env VTm -> STm -> m STm
nf env t = do
  t' <- eval env t
  quote (envQuoteLvl env) t'

envQuoteLvl :: Env VTm -> Lvl
envQuoteLvl env = Lvl (length env)
