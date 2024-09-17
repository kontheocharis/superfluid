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
    unelab,
    ($$),
    vApp,
    vRepr,
    vAppNeu,
    evalPat,
    unfoldDefs,
    quoteSpine,
    unelabSig,
    ensureIsCtor,
    vLams,
    vReprTel,
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
    Lvl (..),
    MetaVar,
    Name (..),
    Param (..),
    PiMode (..),
    Spine,
    Tag,
    Tel,
    Times (..),
    globName,
    inv,
    lvlToIdx,
    mapSpine,
    mapSpineM,
    nextLvl,
    nextLvls,
    unMetaVar,
    pattern Impossible,
    pattern Possible,
  )
import Control.Exception (assert)
import Control.Monad (foldM)
import Control.Monad.Extra (concatMapM)
import Control.Monad.State (StateT (..))
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.Trans (MonadTrans (..))
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Foldable (toList)
import qualified Data.IntMap as IM
import Data.List.Extra (firstJust, intercalate, (!?))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), fromList, (><))
import qualified Data.Sequence as S
import Data.Set (Set)
import Debug.Trace (traceM)
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    PrimGlobalInfo (..),
    Sig (..),
    getCaseRepr,
    getCtorGlobal,
    getGlobal,
    getGlobalRepr,
    getGlobalTags,
    unfoldDef,
  )
import Literals (unfoldLit)
import Meta (HasMetas, SolvedMetas, lookupMetaVar, lookupMetaVarName)
import Presyntax (PCtor (MkPCtor), PData (MkPData), PDef (MkPDef), PItem (..), PPrim (..), PProgram (..), PTm (..), pApp)
import Printing (Pretty (..))
import Syntax (BoundState (..), Bounds, SPat (..), STm (..), sAppSpine, sLams, STy, sPis)
import Value
  ( Closure (..),
    Env,
    Sub (..),
    VHead (..),
    VNeu (..),
    VPat,
    VPatB (..),
    VTm (..),
    VTy,
    pattern VGl,
    pattern VGlob,
    pattern VHead,
    pattern VMeta,
    pattern VRepr,
    pattern VVar,
  )

class (Has m SolvedMetas, Has m Sig, HasNameSupply m) => Eval m where
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
vAppNeu (VCaseApp dat c r cls us) u = VNeu (VCaseApp dat c r cls (us >< u))

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

vCase :: (Eval m) => DataGlobal -> VTm -> VTm -> [Clause VPatB Closure] -> m VTm
vCase dat v r cs = do
  v' <- unfoldDefs v
  case v' of
    VLit l -> vCase dat (unfoldLit l) r cs
    VNeu n ->
      fromMaybe (return $ VNeu (VCaseApp dat n r cs Empty)) $
        firstJust
          ( \clause -> do
              case clause of
                Possible p t -> case vMatch p.vPat v' of
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
vRepr l m (VNeu n@(VApp (VGlobal g pp) sp)) = do
  r <- access (getGlobalRepr g)
  case r of
    Just r' -> do
      r'' <- r' $$ pp
      res <- vApp r'' sp
      vRepr l m res
    Nothing -> return $ VNeu (VRepr m n)
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

-- vRepr _ m (VNeu n) = do
--   return $ VNeu (VRepr m n)

close :: (Eval m) => Int -> Env VTm -> STm -> m Closure
close n env t = return $ Closure n env t

closureArgs :: Int -> Int -> [VTm]
closureArgs n envLen = map (VNeu . VVar . Lvl . (+ envLen)) (reverse [0 .. n - 1])

extendEnvByNVars :: Int -> Env VTm -> Env VTm
extendEnvByNVars numVars env = closureArgs numVars (length env) ++ env

evalInOwnCtx :: (Eval m) => Lvl -> Closure -> m VTm
evalInOwnCtx l cl = cl $$ closureArgs cl.numVars l.unLvl

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
eval env (SCase dat t r cs) = do
  t' <- eval env t
  cs' <- mapM (\p -> do bitraverse (evalPat (extendEnvByNVars (length p.pat.binds) env)) (close (length p.pat.binds) env) p) cs
  r' <- eval env r
  vCase dat t' r' cs'
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
  (VCaseApp dat v r cs sp) -> do
    v' <- quote l (VNeu v)
    cs' <- mapM (bitraverse (quotePat l) (quoteClosure l)) cs
    r' <- quote l r
    quoteSpine l (SCase dat v' r' cs') sp

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

unelabMeta :: (Eval m) => [Name] -> MetaVar -> Bounds -> m (PTm, [Arg PTm])
unelabMeta ns m bs = case (drop (length ns - length bs) ns, bs) of
  (_, []) -> do
    mt <- lookupMetaVar m
    case mt of
      Just t -> do
        t' <- quote (Lvl (length ns)) t >>= unelab ns
        return (t', [])
      Nothing -> do
        n <- lookupMetaVarName m
        case n of
          Just n' -> return (PHole n', [])
          Nothing -> return (PHole (Name $ "m" ++ show m.unMetaVar), [])
  (n : ns', Bound : bs') -> do
    (t, ts) <- unelabMeta ns' m bs'
    return (t, Arg Explicit (PName n) : ts)
  (_ : ns', Defined : bs') -> unelabMeta ns' m bs'
  _ -> error "impossible"

unelabPat :: (Eval m) => [Name] -> SPat -> m PTm
unelabPat ns pat = do
  (n, _) <- runStateT (unelabPat' pat.asTm) pat.binds
  return n
  where
    unelabPat' :: (Eval m) => STm -> StateT [Name] m PTm
    unelabPat' pat' = case pat' of
      (SGlobal (CtorGlob (CtorGlobal c)) pp) -> do
        pp' <- lift $ mapM (unelab ns) pp
        return $ PParams (PName c) pp'
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

unelabValue :: (Eval m) => [Name] -> VTm -> m PTm
unelabValue ns t = quote (Lvl (length ns)) t >>= unelab ns

unelab :: (Eval m) => [Name] -> STm -> m PTm
unelab ns = \case
  (SPi m x a b) -> PPi m x <$> unelab ns a <*> unelab (x : ns) b
  (SLam m x t) -> PLam m x <$> unelab (x : ns) t
  (SLet x ty t u) -> PLet x <$> unelab ns ty <*> unelab ns t <*> unelab (x : ns) u
  (SMeta m bs) -> do
    (t, ts) <- unelabMeta ns m bs
    return $ pApp t ts
  (SVar v) -> do
    let i = ns !? v.unIdx
    case i of
      Just i' -> return $ PName i'
      Nothing -> return $ PName (Name $ "?" ++ show v.unIdx)
  (SApp m t u) -> PApp m <$> unelab ns t <*> unelab ns u
  (SCase _ t r cs) ->
    PCase
      <$> unelab ns t
      <*> (Just <$> unelab ns r)
      <*> mapM
        ( \c ->
            Clause
              <$> unelabPat ns c.pat
              <*> traverse (unelab (reverse c.pat.binds ++ ns)) c.branch
        )
        cs
  SU -> return PU
  (SGlobal g pp) -> do
    pp' <- mapM (unelab ns) pp
    return $ PParams (PName (globName g)) pp'
  (SLit l) -> PLit <$> traverse (unelab ns) l
  (SRepr m t) -> PRepr m <$> unelab ns t

unelabTel :: (Eval m) => [Name] -> Tel STm -> m (Tel PTm)
unelabTel _ Empty = return Empty
unelabTel ns (Param m n a :<| tel) = do
  a' <- unelab ns a
  tel' <- unelabTel (n : ns) tel
  return $ Param m n a' :<| tel'

telNames :: Tel a -> [Name]
telNames = reverse . toList . fmap (\p -> p.name)

unelabSig :: (Eval m) => m PProgram
unelabSig = do
  s <- view
  unelabSig' s
  where
    unelabData :: (Eval m) => Name -> DataGlobalInfo -> Set Tag -> m PData
    unelabData n d ts = do
      sig <- view
      te' <- unelabTel [] d.params
      ty' <- unelab (telNames d.params) d.ty.body
      ctors' <-
        mapM
          ( \n' ->
              unelabCtor
                n'.globalName
                (getCtorGlobal n' sig)
                (telNames d.params)
                (getGlobalTags n'.globalName sig)
          )
          d.ctors
      return $ MkPData n te' ty' ctors' ts

    unelabCtor :: (Eval m) => Name -> CtorGlobalInfo -> [Name] -> Set Tag -> m PCtor
    unelabCtor n c dataParams ts = do
      ty' <- unelab dataParams c.ty.body
      return $ MkPCtor n ty' ts

    unelabDef :: (Eval m) => Name -> DefGlobalInfo -> Set Tag -> m PDef
    unelabDef n d ts = do
      ty' <- unelabValue [] d.ty
      body' <- traverse (unelab []) d.tm
      return $ MkPDef n ty' (fromMaybe PWild body') ts

    unelabPrim :: (Eval m) => Name -> PrimGlobalInfo -> Set Tag -> m PPrim
    unelabPrim n p ts = do
      ty' <- unelabValue [] p.ty
      return $ MkPPrim n ty' ts

    unelabSig' :: (Eval m) => Sig -> m PProgram
    unelabSig' s =
      PProgram
        <$> concatMapM
          ( \n -> do
              case (getGlobal n s, getGlobalTags n s) of
                (DataInfo d, ts) -> (: []) . PData <$> unelabData n d ts
                (DefInfo d, ts) -> (: []) . PDef <$> unelabDef n d ts
                (CtorInfo _, _) -> return []
                (PrimInfo p, ts) -> (: []) . PPrim <$> unelabPrim n p ts
          )
          s.nameOrder

instance (Eval m, Has m [Name]) => Pretty m VTm where
  pretty v = do
    n <- view
    q <- quote (Lvl (length n)) v
    unelab n q >>= pretty

instance (Eval m, Has m [Name]) => Pretty m STm where
  pretty t = do
    n <- view
    unelab n t >>= pretty

instance (Eval m, Has m [Name]) => Pretty m Closure where
  pretty cl = do
    n <- view
    cl' <- evalInOwnCtx (Lvl (length (n :: [Name]))) cl
    pretty cl'

instance (Eval m, Has m [Name]) => Pretty m VPatB where
  pretty (VPatB pat names) = enter (names ++) $ pretty pat

instance (Eval m, Has m [Name]) => Pretty m Sub where
  pretty sub = do
    vars <-
      concatMapM
        ( \(x, v) -> do
            l' <- pretty (VNeu (VVar (Lvl x)))
            v' <- mapM pretty (NE.toList v)
            return $ map (\v'' -> l' <> " = " <> v'') v'
        )
        (IM.toList sub.vars)
    return $ intercalate ", " vars

instance (Eval m, Has m [Name]) => Pretty m (Tel STm) where
  pretty tel = do
    n <- view
    unelabTel n tel >>= pretty
