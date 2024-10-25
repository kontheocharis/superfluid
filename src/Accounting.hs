{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Accounting
  ( Acc (..),
    AccError (..),
    Account (..),
    satisfyQty,
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
  )
import Context
  ( Ctx (..),
    CtxEntry (..),
    accessCtx,
    coindexCtx,
    enterCtx,
    enterQty,
    evalHere,
    evalInOwnCtxHere,
    modifyCtx,
    qty,
    typelessBind,
    typelessBinds,
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
  )
import Meta (lookupMetaVarQty)
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

class (Eval m, Unelab m, Has m Loc, Has m Qty, Has m Ctx) => Acc m where
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
                Zero -> "0 (zero)"
                Many -> "* (many)"
          return $ "Quantity mismatch: there are " ++ showQty q1 ++ " of term " ++ t' ++ ", but " ++ showQty q2 ++ " are requested."

class Account a where
  account :: (Acc m) => a -> m ()

satisfyQty :: (Acc m) => Qty -> VTm -> m ()
satisfyQty q v = do
  q' <- qty
  unless (q >= q') $ accError $ QtyMismatch q q' v

instance (Account t) => Account (Spine t) where
  account Empty = return ()
  account (ts :|> Arg _ q t) = do
    enterQty q $ account t
    account ts

instance Account (Closure, [(Qty, Name)]) where
  account (cl, bs) = do
    vcl <- evalInOwnCtxHere cl
    enterCtx (typelessBinds bs) $ account vcl

instance Account VNorm where
  account tm = case tm of
    VLam _ q x t -> account (t, [(q, x)])
    VPi _ q x ty t -> do
      enterQty Zero $ do
        account ty
        account (t, [(q, x)])
      satisfyQty Zero (VNorm tm)
    VU -> satisfyQty Zero (VNorm tm)
    VData (_, sp) -> do
      satisfyQty Zero (VNorm tm)
      account sp
    VCtor ((_, pp), sp) -> do
      account pp
      account sp

instance Account (Case VTm VTm VPatB Closure) where
  account c = do
    i <- access (dataIsIrrelevant c.dat)
    if i
      then do
        enterQty Zero $ account c.subject
      else do
        account c.subject
    enterQty Zero $ account c.elimTy
    traverse_ (\(Clause p t) -> traverse (account . (,p.binds)) t) c.clauses

instance Account VLazy where
  account (tm, sp) = case tm of
    VDef d -> do
      di <- access (getDefGlobal d)
      satisfyQty di.qty (VLazy (tm, sp))
      account sp
    VLit v -> do
      traverse_ account v
      account sp
    VLazyCase c -> do
      account (c {subject = VLazy c.subject})
      account sp
    VRepr n' -> account (headAsValue n')
    VLet q x ty t u -> do
      enterQty Zero $ account ty
      enterQty q $ account t
      account (u, [(q, x)])
      account sp

instance Account VNeu where
  account (tm, sp) = case tm of
    VFlex m -> do
      q <- lookupMetaVarQty m
      satisfyQty q (VNeu (tm, sp))
      account sp
    VRigid l -> do
      n <- accessCtx (`coindexCtx` l)
      satisfyQty n.qty (VNeu (tm, sp))
    VBlockedCase c -> do
      account (c {subject = VNeu c.subject})
      account sp
    VPrim p -> do
      di <- access (getPrimGlobal p)
      satisfyQty di.qty (VNeu (tm, sp))
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
    enterQty Zero $ account t.ty
    enterCtx (typelessBind t.name t.qty) $ account ts

instance Account DataGlobalInfo where
  account di = do
    account di.params
    enterQty Zero $ account di.fullTy
    let bs = map (\p -> (p.qty, p.name)) (toList di.params)
    traverse_
      ( \c -> do
          ci <- access (getCtorGlobal c)
          enterQty Zero $ account (ci.ty, bs)
      )
      di.ctors

instance Account DefGlobalInfo where
  account f = do
    enterQty Zero $ account f.ty
    enterQty f.qty $ account (fromJust f.vtm)

instance Account PrimGlobalInfo where
  account p = enterQty Zero $ account p.ty
