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
    Tel,
  )
import Context (Ctx (..), accessCtx, enterCtx, enterQty, enterTel, indexCtx, modifyCtx, qty, quoteHere, typelessBind, typelessBinds)
import Control.Monad (unless)
import Data.Foldable (traverse_)
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..))
import Evaluation (Eval)
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
import Printing (Pretty (..))
import Syntax (Case (..), Closure (..), SPat (..), STm (..), VTm (..))
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
  = QtyMismatch Qty Qty STm

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

satisfyQty :: (Acc m) => Qty -> STm -> m ()
satisfyQty q t = do
  q' <- qty
  unless (q >= q') $ accError $ QtyMismatch q q' t

instance Account VTm where
  account t = do
    t' <- quoteHere t
    account t'

instance Account STm where
  account tm = case tm of
    SVar idx -> do
      n <- accessCtx (`indexCtx` idx)
      satisfyQty n.qty tm
    SLam _ q x body -> enterCtx (typelessBind x q) $ account body
    SApp _ q fn arg -> do
      account fn
      enterQty q $ account arg
    SPi _ q x a b -> enterQty Zero $ do
      account a
      enterCtx (typelessBind x q) $ account b
    SLet q x ty val body -> do
      enterQty Zero $ account ty
      enterQty q $ account val
      enterCtx (typelessBind x q) $ account body
    SU -> satisfyQty Zero tm
    SData _ -> satisfyQty Zero tm
    SCtor (_, args) -> traverse_ (\(Arg _ q t) -> enterQty q $ account t) args
    SCase c -> do
      i <- access (dataIsIrrelevant c.dat)
      if i
        then do
          enterQty Zero $ account c.subject
        else do
          account c.subject
      enterQty Zero $ account c.elimTy
      traverse_ (\(Clause p t) -> enterCtx (typelessBinds p.binds) $ traverse account t) c.clauses
    SMeta _ _ -> return () -- Metas are assumed to not exist anymore
    SLit _ -> return () -- Valid in any quantity
    SDef d -> do
      di <- access (getDefGlobal d)
      satisfyQty di.qty tm
    SPrim p -> do
      di <- access (getPrimGlobal p)
      satisfyQty di.qty tm
    SRepr t -> account t
    SUnrepr t -> account t

instance (Account a) => Account (Tel a) where
  account Empty = return ()
  account (t :<| ts) = do
    enterQty Zero $ account t.ty
    enterCtx (typelessBind t.name t.qty) $ account ts

instance Account DataGlobalInfo where
  account di = do
    account di.params
    enterQty Zero $ account di.fullTy
    enterTel di.params $ do
      traverse_
        ( \c -> do
            ci <- access (getCtorGlobal c)
            enterQty Zero $ account ci.ty.body
        )
        di.ctors

instance Account DefGlobalInfo where
  account f = do
    enterQty Zero $ account f.ty
    enterQty f.qty $ account (fromJust f.tm)

instance Account PrimGlobalInfo where
  account p = enterQty Zero $ account p.ty
