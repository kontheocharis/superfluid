{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
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
    Glob (..),
    Has (..),
    Idx (..),
    Lvl (..),
    MetaVar,
    Name (..),
    Param (..),
    PiMode (..),
    Tag,
    Tel,
    globName,
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
import Meta (lookupMetaVar, lookupMetaVarName)
import Presyntax (PCtor (MkPCtor), PData (MkPData), PDef (MkPDef), PItem (..), PPrim (..), PProgram (..), PTm (..), pApp)
import Printing (Pretty (..))
import Syntax (BoundState (..), Bounds, SPat (..), STm (..))
import Syntax
  ( Closure (..),
    Sub (..),
    VPatB (..),
    VTm (..),
    pattern VVar,
  )

class (Eval m) => Unelab m

unelabMeta :: (Unelab m) => [Name] -> MetaVar -> Bounds -> m (PTm, [Arg PTm])
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

unelabPat :: (Unelab m) => [Name] -> SPat -> m PTm
unelabPat ns pat = do
  (n, _) <- runStateT (unelabPat' pat.asTm) pat.binds
  return n
  where
    unelabPat' :: (Unelab m) => STm -> StateT [Name] m PTm
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

unelabValue :: (Unelab m) => [Name] -> VTm -> m PTm
unelabValue ns t = quote (Lvl (length ns)) t >>= unelab ns

unelab :: (Unelab m) => [Name] -> STm -> m PTm
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

unelabTel :: (Unelab m) => [Name] -> Tel STm -> m (Tel PTm)
unelabTel _ Empty = return Empty
unelabTel ns (Param m n a :<| tel) = do
  a' <- unelab ns a
  tel' <- unelabTel (n : ns) tel
  return $ Param m n a' :<| tel'

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

    unelabCtor :: (Unelab m) => Name -> CtorGlobalInfo -> [Name] -> Set Tag -> m PCtor
    unelabCtor n c dataParams ts = do
      ty' <- unelab dataParams c.ty.body
      return $ MkPCtor n ty' ts

    unelabDef :: (Unelab m) => Name -> DefGlobalInfo -> Set Tag -> m PDef
    unelabDef n d ts = do
      ty' <- unelabValue [] d.ty
      body' <- traverse (unelab []) d.tm
      return $ MkPDef n ty' (fromMaybe PWild body') ts

    unelabPrim :: (Unelab m) => Name -> PrimGlobalInfo -> Set Tag -> m PPrim
    unelabPrim n p ts = do
      ty' <- unelabValue [] p.ty
      return $ MkPPrim n ty' ts

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
  pretty (VPatB pat names) = enter (names ++) $ pretty pat

instance (Unelab m, Has m [Name]) => Pretty m Sub where
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

instance (Unelab m, Has m [Name]) => Pretty m (Tel STm) where
  pretty tel = do
    n <- view
    unelabTel n tel >>= pretty
