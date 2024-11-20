{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# OPTIONS_GHC -Wno-orphans #-}

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
    Parent (child),
    Qty (..),
    Spine,
    Tel,
    minus,
    telToBinds,
  )
import Context
  ( Ctx (..),
    CtxEntry (..),
    accessCtx,
    coindexCtx,
    enterCtx,
    evalHere,
    evalInOwnCtxHere,
    expect,
    modifyCtx,
    need,
    qty,
    setCtxEntryQty,
    typelessBind,
    typelessBinds, modifyNames, getNames,
  )
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
                View -> "view"
          return $ "Quantity mismatch: got " ++ showQty q1 ++ " of term " ++ t' ++ ", but " ++ showQty q2 ++ " requested."

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
    VCtor ((c, pp), sp) -> do
      di <- access (getCtorGlobal c)
      have
        di.qty
        (VNorm tm)
        (\q -> return ())
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
    traverse_ (\(Clause p t) -> child $ traverse (account . (,p.binds)) t) c.clauses

instance Account VLazy where
  account (tm, sp) = case tm of
    VDef d -> do
      di <- access (getDefGlobal d)
      have
        di.qty
        (VLazy (tm, sp))
        (\q -> return ())
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
    VFlex _ -> do
      -- q <- lookupMetaVarQty m
      -- have q (VNeu (tm, sp)) (modifyMetaVarQty m . const)
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
    enterCtx (typelessBinds (telToBinds di.params)) $ do
      expect Zero $ account di.familyTy
      traverse_
        ( \c -> do
            ci <- access (getCtorGlobal c)
            account ci.ty
        )
        di.ctors

instance Account DefGlobalInfo where
  account f = do
    expect Zero $ account f.ty
    expect f.qty $ account (fromJust f.vtm)

instance Account PrimGlobalInfo where
  account p = expect Zero $ account p.ty
