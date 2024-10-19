{-# LANGUAGE FlexibleContexts #-}

import Common (Arg (..), Clause (..), Has (..), HasProjectFiles (..), Loc (..), Qty (..), Tel, CtorGlobal)
import Context (Ctx, accessCtx, enterCtx, enterQty, enterTel, indexCtx, qty, quoteHere, typelessBind, typelessBinds)
import Control.Monad (unless)
import Data.Foldable (traverse_)
import Data.Sequence (Seq (..))
import Evaluation (Eval)
import Globals
  ( DataGlobalInfo (..),
    DefGlobalInfo (..),
    PrimGlobalInfo (..),
    Sig,
    dataIsIrrelevant,
    getDefGlobal,
    getPrimGlobal, CtorGlobalInfo, getCtorGlobal,
  )
import Printing (Pretty (..))
import Syntax (Case (..), SPat (..), STm (..), VTm)

-- Accounting for all resources :)

class (Eval m, Has m Loc, Has m Qty, Has m Ctx) => Acc m where
  accError :: AccError -> m a

data AccError
  = QtyMismatch Qty Qty

instance (HasProjectFiles m, Acc m) => Pretty m AccError where
  pretty e = do
    loc <- view
    loc' <- pretty (loc :: Loc)
    err' <- err
    return $ loc' <> "\n" <> err'
    where
      err = case e of
        QtyMismatch q1 q2 -> do
          return $ "Quantity mismatch: (" <> show q1 <> " _ : _) and (" <> show q2 ++ "_ : _)"

class Account a where
  account :: (Acc m) => a -> m ()

satisfyQty :: (Acc m) => Qty -> m ()
satisfyQty q = do
  q' <- qty
  unless (q >= q') $ accError $ QtyMismatch q q'

instance Account VTm where
  account t = do
    t' <- quoteHere t
    account t'

instance Account STm where
  account tm = case tm of
    SVar idx -> do
      n <- accessCtx (`indexCtx` idx)
      satisfyQty n.qty
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
    SU -> satisfyQty Zero
    SData _ -> satisfyQty Zero
    SCtor (_, args) -> traverse_ (\(Arg _ q t) -> enterQty q $ account t) args
    SCase c -> do
      i <- access (dataIsIrrelevant c.dat)
      if i
        then do
          enterQty Zero $ account c.subject
        else do
          account c.subject
      traverse_ (\(Clause p t) -> enterCtx (typelessBinds p.binds) $ traverse account t) c.clauses
    SMeta _ _ -> return () -- Metas are assumed to not exist anymore
    SLit _ -> return () -- Valid in any quantity
    SDef d -> do
      di <- access (getDefGlobal d)
      satisfyQty di.qty
    SPrim p -> do
      di <- access (getPrimGlobal p)
      satisfyQty di.qty
    SRepr t -> account t
    SUnrepr t -> account t

instance (Account a) => Account (Tel a) where
  account Empty = return ()
  account (t :<| ts) = do
    account t.ty
    enterCtx (typelessBind t.name t.qty) $ account ts


dataItem :: (Acc m) => DataGlobalInfo -> m ()
dataItem di = do
  account di.params
  enterQty Zero $ account di.fullTy
  enterTel di.params $ do
    account di.ctors

instance Account CtorGlobal where
  account c = do
    ci <- access (getCtorGlobal c)
    enterQty ci.qty $ account ci.ty

instance Account CtorGlobalInfo where
  account ci = do
    account ci.ty
    traverse_ (\(Arg _ q t) -> enterQty q $ account t) ci.spine

-- ensureNewName n
-- te' <- tel te
-- ty' <- do
--   (ty', _) <- enterQty Zero $ ty (Check (VNorm VU))
--   vty <- evalHere ty'
--   i <- getLvl >>= (`isTypeFamily` vty)
--   unless i (tcError $ InvalidDataFamily vty)
--   return ty'
-- cty <- closeHere (length te') ty'
-- fty <- evalHere $ sPis te' ty'
-- modify (addItem n (DataInfo (DataGlobalInfo n te' fty cty [] Nothing Nothing Empty)) ts)

-- endDataItem :: (Acc m) => DataGlobal -> m ()
-- endDataItem dat = do
--   (motiveTy, elimTy, arity) <- buildElimTy dat
--   modify
--     ( modifyDataItem
--         dat
--         ( \d ->
--             d
--               { elimTy = Just elimTy,
--                 motiveTy = Just motiveTy,
--                 indexArity = arity
--               }
--         )
--     )

-- ctorItem :: (Acc m) => DataGlobal -> Name -> Set Tag -> Child m -> m ()
-- ctorItem dat n ts ty = do
--   di <- access (getDataGlobal dat)
--   idx <- access (\s -> length (getDataGlobal dat s).ctors)
--   (sp, ty', q) <- enterTel di.params $ do
--     ensureNewName n
--     (ty', _) <- enterQty Zero $ ty (Check (VNorm VU))
--     let sp = fmap (\p -> Arg p.mode p.qty ()) $ fst (sGatherPis ty')
--     vty <- evalHere ty'
--     i <- getLvl >>= (\l -> isCtorTy l dat vty)
--     case i of
--       Nothing -> tcError $ InvalidCtorType ty'
--       Just (_, q) -> return (sp, ty', q)
--   cty <- closeHere (length di.params) ty'
--   modify (addItem n (CtorInfo (CtorGlobalInfo n cty idx q dat sp)) ts)
--   modify (modifyDataItem dat (\d -> d {ctors = d.ctors ++ [CtorGlobal n]}))

-- primItem :: (Acc m) => Name -> Qty -> Set Tag -> Child m -> m ()
-- primItem n q ts ty = do
--   ensureNewName n
--   (ty', _) <- enterQty Zero $ ty (Check (VNorm VU))
--   vty <- evalHere ty'
--   modify (addItem n (PrimInfo (PrimGlobalInfo n q vty)) ts)

-- reprItem :: (Acc m) => Tel STm -> m VTy -> (Closure -> Set Tag -> Sig -> Sig) -> Set Tag -> Child m -> m STm
-- reprItem te getGlob addGlob ts r = do
--   ty <- getGlob
--   (r', _) <- enterTel te $ r (Check ty)
--   vr <- closeHere (length te) r'
--   modify (addGlob vr ts)
--   return r'

-- reprDataItem :: (Acc m) => DataGlobal -> Set Tag -> Child m -> m (Tel STm)
-- reprDataItem dat ts c = do
--   di <- access (getDataGlobal dat)
--   tm <-
--     enterQty Zero $
--       reprItem
--         Empty
--         (reprHere 1 di.fullTy)
--         (addDataRepr dat)
--         ts
--         c
--   let (ls, _) = sGatherLams tm
--   return (telWithNames di.params (toList $ fmap (\p -> p.name) ls))

-- reprCtorItem :: (Acc m) => Tel STm -> CtorGlobal -> Set Tag -> Child m -> m ()
-- reprCtorItem te ctor ts c = do
--   ci <- access (getCtorGlobal ctor)
--   _ <-
--     reprItem
--       te
--       (evalInOwnCtxHere ci.ty >>= reprHere 1)
--       (addCtorRepr ctor)
--       ts
--       c
--   return ()

-- reprDefItem :: (Acc m) => DefGlobal -> Set Tag -> Child m -> m ()
-- reprDefItem def ts c = do
--   _ <- reprItem Empty (access (getDefGlobal def) >>= \d -> return d.ty) (addDefRepr def) ts c
--   return ()

-- reprCaseItem :: (Acc m) => Tel STm -> DataGlobal -> Set Tag -> Child m -> m ()
-- reprCaseItem te dat ts c = do
--   di <- access (getDataGlobal dat)
--   _ <-
--     reprItem
--       te
--       (evalInOwnCtxHere (fromJust di.elimTy))
--       (addCaseRepr dat)
--       ts
--       c
--   return ()
