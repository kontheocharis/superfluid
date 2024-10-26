{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE MonoLocalBinds #-}

module Accounting
  ( Acc (..),
    AccError (..),
    Account (runAccount),
    have,
  )
where

import Common
  ( Arg (..),
    Clause (..),
    Has (..),
    HasProjectFiles (..),
    Loc (..),
    Name,
    Param (..),
    Qty (..),
    Spine,
    Tel,
    minus, Try (try), Parent (child),
  )
import Context
  ( Ctx (..),
    CtxEntry (..),
    accessCtx,
    coindexCtx,
    enterCtx,
    need,
    evalHere,
    evalInOwnCtxHere,
    modifyCtx,
    qty,
    setCtxEntryQty,
    typelessBind,
    typelessBinds, expect,
  )
import Control.Monad (unless)
import Data.Foldable (Foldable (..), traverse_)
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..))
import Evaluation (Eval, force)
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    PrimGlobalInfo (..),
    dataIsIrrelevant,
    getCtorGlobal,
    getDefGlobal,
    getPrimGlobal,
    modifyDefItem,
    modifyPrimItem,
  )
import Meta (lookupMetaVarQty, modifyMetaVarQty)
import Printing (Pretty (..))
import Syntax
  ( Case (..),
    Closure (..),
    STm (..),
    VLazy,
    VLazyHead (..),
    VNeu,
    VNeuHead (..),
    VNorm (..),
    VPatB (..),
    VTm (..),
    headAsValue,
  )
import Unelaboration (Unelab)

-- Accounting for all resources :)

class (Eval m, Unelab m, Parent m, Has m Loc, Has m Qty, Has m Ctx) => Acc m where
  accError :: AccError -> m a
  catchAccErrorNoResume :: m a -> m (Either AccError a)

instance (Acc m) => Has m [Name] where
  view = do
    ctx <- accessCtx id
    return ctx.nameList

  modify f = do
    ctx <- accessCtx id
    modifyCtx (\c -> c {nameList = f ctx.nameList})

data AccError
  = QtyMismatch Qty Qty VTm

instance (HasProjectFiles m, Acc m) => Pretty m AccError where
  pretty e = do
    loc <- view
    loc' <- pretty (loc :: Loc)
    err' <- err
    return $ loc' <> "\n" <> err'
    where
      err = case e of
        QtyMismatch q1 q2 t -> do
          t' <- pretty t
          let showQty = \case
                Zero -> "zero"
                One -> "one"
                Many -> "many"
          return $ "Quantity mismatch: got " ++ showQty q1 ++ " of term " ++ t' ++ ", but " ++ showQty q2 ++ " are requested."

class Account a where
  runAccount :: (Acc m) => a -> m ()
  runAccount x = child (account x)

  account :: (Acc m) => a -> m ()

have :: (Acc m) => Qty -> VTm -> (Qty -> m ()) -> m ()
have q v f = do
  q' <- qty
  case minus q q' of
    Just q'' -> f q''
    Nothing -> accError $ QtyMismatch q q' v

instance (Account t) => Account (Spine t) where
  account Empty = return ()
  account (ts :|> Arg _ q t) = do
    need q $ account t
    account ts

instance Account (Closure, [(Qty, Name)]) where
  account (cl, bs) = do
    vcl <- evalInOwnCtxHere cl
    enterCtx (typelessBinds bs) $ account vcl

instance Account VNorm where
  account tm = case tm of
    VLam _ q x t -> account (t, [(q, x)])
    VPi _ q x ty t -> do
      need Zero $ do
        account ty
        account (t, [(q, x)])
    VU -> return ()
    VData (_, sp) -> do
      account sp
    VCtor ((_, pp), sp) -> do
      account pp
      account sp

instance Account (Case VTm VTm VPatB Closure) where
  account c = do
    i <- access (dataIsIrrelevant c.dat)
    if i
      then do
        need Zero $ account c.subject
      else do
        account c.subject
    need Zero $ account c.elimTy
    traverse_ (\(Clause p t) -> traverse (account . (,p.binds)) t) c.clauses

instance Account VLazy where
  account (tm, sp) = case tm of
    VDef d -> do
      di <- access (getDefGlobal d)
      have
        di.qty
        (VLazy (tm, sp))
        (\q -> modify (modifyDefItem d (\i -> i {qty = q})))
      account sp
    VLit v -> do
      traverse_ account v
      account sp
    VLazyCase c -> do
      account (c {subject = VLazy c.subject})
      account sp
    VRepr n' -> account (headAsValue n')
    VLet q x ty t u -> do
      expect Zero $ account ty
      expect q $ account t
      account (u, [(q, x)])
      account sp

instance Account VNeu where
  account (tm, sp) = case tm of
    VFlex m -> do
      q <- lookupMetaVarQty m
      have q (VNeu (tm, sp)) (modifyMetaVarQty m . const)
      account sp
    VRigid l -> do
      n <- accessCtx (`coindexCtx` l)
      have n.qty (VNeu (tm, sp)) (modifyCtx . setCtxEntryQty l)
      account sp
    VBlockedCase c -> do
      account (c {subject = VNeu c.subject})
      account sp
    VPrim p -> do
      di <- access (getPrimGlobal p)
      have
        di.qty
        (VNeu (tm, sp))
        (\_ -> return ()) -- it can be used linearly, doesn't mean it's used
      account sp
    VUnrepr n' -> do
      account (headAsValue n')
      account sp

instance Account VTm where
  account t = do
    t' <- force t
    case t' of
      VNorm n -> account n
      VLazy n -> account n
      VNeu n -> account n

instance Account STm where
  account tm' = do
    vtm <- evalHere tm'
    account vtm

instance (Account a) => Account (Tel a) where
  account Empty = return ()
  account (t :<| ts) = do
    expect Zero $ account t.ty
    enterCtx (typelessBind t.name t.qty) $ account ts

instance Account DataGlobalInfo where
  account di = do
    account di.params
    expect Zero $ account di.fullTy
    let bs = map (\p -> (p.qty, p.name)) (toList di.params)
    traverse_
      ( \c -> do
          ci <- access (getCtorGlobal c)
          expect Zero $ account (ci.ty, bs)
      )
      di.ctors

instance Account DefGlobalInfo where
  account f = do
    expect Zero $ account f.ty
    expect f.qty $ account (fromJust f.vtm)

instance Account PrimGlobalInfo where
  account p = expect Zero $ account p.ty
