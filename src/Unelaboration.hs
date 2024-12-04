{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Unelaboration
  ( Unelab,
    unelab,
    unelabSig,
  )
where

import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (..),
    Has (..),
    Idx (..),
    Lvl (..),
    MetaVar,
    Name (..),
    Param (..),
    PiMode (..),
    PrimGlobal (..),
    Tag,
    Tel,
    mapSpineM,
    unMetaVar,
  )
import Control.Monad.Extra (concatMapM)
import Control.Monad.State (StateT (..))
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.Trans (MonadTrans (..))
import Data.Foldable (toList)
import qualified Data.IntMap as IM
import Data.List.Extra (intercalate, (!?))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import Data.Set (Set)
import Evaluation (Eval, evalInOwnCtx, quote)
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    PrimGlobalInfo (..),
    Sig (..),
    getCtorGlobal,
    getGlobal,
    getGlobalTags,
  )
import Meta (lookupMetaVar, lookupMetaVarName, lookupMetaVarQty)
import Presyntax (PCtor (MkPCtor), PData (MkPData), PDef (MkPDef), PItem (..), PPrim (..), PProgram (..), PTm (..), pApp, MaybeQty (..), singleTermClause)
import Printing (Pretty (..))
import Syntax
  ( BoundState (..),
    Bounds,
    Case (..),
    Closure (..),
    SPat (..),
    STm (..),
    VPatB (..),
    VTm (..),
    pattern VVar,
  )
import qualified Data.Sequence as S
import Substitution (Sub)

class (Eval m) => Unelab m

unelabMeta :: (Unelab m) => [Name] -> MetaVar -> Bounds -> m (PTm, [Arg PTm])
unelabMeta ns m bs = case (drop (length ns - length bs) ns, bs) of
  (_, []) -> do
    mt <- lookupMetaVar m
    mq <- lookupMetaVarQty m
    case mt of
      Just t -> do
        t' <- quote (Lvl (length ns)) t >>= unelab ns
        return (t', [])
      Nothing -> do
        n <- lookupMetaVarName m
        case n of
          Just n' -> return (PHole n', [])
          Nothing -> return (PHole (Name $ "m" ++ show m.unMetaVar ++ show mq), [])
  (n : ns', Bound q : bs') -> do
    (t, ts) <- unelabMeta ns' m bs'
    return (t, Arg Explicit q (PName n) : ts)
  (_ : ns', Defined : bs') -> unelabMeta ns' m bs'
  _ -> error "impossible"

unelabPat :: (Unelab m) => [Name] -> SPat -> m PTm
unelabPat ns pat = do
  (n, _) <- runStateT (unelabPat' pat.asTm) (map snd pat.binds)
  return n
  where
    unelabPat' :: (Unelab m) => STm -> StateT [Name] m PTm
    unelabPat' pat' = case pat' of
      (SCtor (c, pp)) -> do
        pp' <- lift $ mapSpineM (unelab ns) pp
        return $ PParams (PName c.globalName) (map (\a -> a.arg) $ toList pp')
      (SApp m q a b) -> do
        a' <- unelabPat' a
        b' <- unelabPat' b
        return $ pApp a' (S.singleton $ Arg m q b')
      (SVar (Idx _)) ->
        state
          ( \case
              (v : vs) -> (PName v, vs)
              [] -> error "impossible"
          )
      _ -> error $ "impossible, got pat " ++ show pat'

unelabValue :: (Unelab m) => [Name] -> VTm -> m PTm
unelabValue ns t = quote (Lvl (length ns)) t >>= unelab ns

unelab :: (Unelab m) => [Name] -> STm -> m PTm
unelab ns = \case
  (SPi m q x a b) -> PPi m (MaybeQty (Just q)) x <$> unelab ns a <*> unelab (x : ns) b
  (SLam m _ x t) -> PLam m (PName x) <$> unelab (x : ns) t
  (SLet q x ty t u) -> PLet (MaybeQty (Just q)) (PName x) <$> unelab ns ty <*> unelab ns t <*> unelab (x : ns) u
  (SMeta m bs) -> do
    (t, ts) <- unelabMeta ns m bs
    return $ pApp t (S.fromList ts)
  (SVar v) -> do
    let i = ns !? v.unIdx
    case i of
      Just i' -> return $ PName i'
      Nothing -> return $ PName (Name $ "?" ++ show v.unIdx)
  (SApp m _ t u) -> PApp m <$> unelab ns t <*> unelab ns u
  (SCase (Case _ _ t _ r cs)) ->
    PCase
      <$> unelab ns t
      <*> (Just <$> unelab ns r)
      <*> mapM
        ( \c ->
            Clause
              <$> unelabPat ns c.pat
              <*> traverse (unelab (reverse (map snd c.pat.binds) ++ ns)) c.branch
        )
        cs
  SU -> return PU
  SCtor (g, pp) -> do
    pp' <- mapSpineM (unelab ns) pp
    return $ PParams (PName g.globalName) (map (\a -> a.arg) $ toList pp')
  SDef g -> return $ PName g.globalName
  SData g -> return $ PName g.globalName
  SPrim g -> return $ PName g.globalName
  SLit l -> PLit <$> traverse (traverse (unelab ns) . Just) l
  SRepr t -> PRepr <$> unelab ns t
  SUnrepr t -> PUnrepr <$> unelab ns t

unelabTel :: (Unelab m) => [Name] -> Tel STm -> m (Tel PTm)
unelabTel _ Empty = return Empty
unelabTel ns (Param m q n a :<| tel) = do
  a' <- unelab ns a
  tel' <- unelabTel (n : ns) tel
  return $ Param m q n a' :<| tel'

telNames :: Tel a -> [Name]
telNames = reverse . toList . fmap (\p -> p.name)

unelabSig :: (Unelab m) => m PProgram
unelabSig = do
  s <- view
  unelabSig' s
  where
    unelabData :: (Unelab m) => Name -> DataGlobalInfo -> Set Tag -> m PData
    unelabData n d ts = do
      sig <- view
      te' <- unelabTel [] d.params
      ty' <- unelab (telNames d.params) d.familyTy
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

    unelabCtor :: (Unelab m) => Name -> CtorGlobalInfo -> [Name] -> Set Tag -> m PCtor
    unelabCtor n c dataParams ts = do
      ty' <- unelab dataParams c.ty
      return $ MkPCtor n (MaybeQty (Just c.qty)) ty' ts

    unelabDef :: (Unelab m) => Name -> DefGlobalInfo -> Set Tag -> m PDef
    unelabDef n d ts = do
      ty' <- unelabValue [] d.ty
      body' <- traverse (unelab []) d.tm
      return $ MkPDef n (MaybeQty (Just d.qty)) ty' [singleTermClause (fromMaybe PWild body')] ts

    unelabPrim :: (Unelab m) => Name -> PrimGlobalInfo -> Set Tag -> m PPrim
    unelabPrim n p ts = do
      ty' <- unelabValue [] p.ty
      return $ MkPPrim n (MaybeQty (Just p.qty)) ty' ts

    unelabSig' :: (Unelab m) => Sig -> m PProgram
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

instance (Unelab m, Has m [Name]) => Pretty m VTm where
  pretty v = do
    n <- view
    q <- quote (Lvl (length n)) v
    unelab n q >>= pretty

instance (Unelab m, Has m [Name]) => Pretty m STm where
  pretty t = do
    n <- view
    unelab n t >>= pretty

instance (Unelab m, Has m [Name]) => Pretty m Closure where
  pretty cl = do
    n <- view
    cl' <- evalInOwnCtx (Lvl (length (n :: [Name]))) cl
    pretty cl'

instance (Unelab m, Has m [Name]) => Pretty m VPatB where
  pretty (VPatB pat names) = enter (map snd names ++) $ pretty pat

instance (Unelab m, Has m [Name]) => Pretty m (Tel STm) where
  pretty tel = do
    n <- view
    unelabTel n tel >>= pretty
