{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Elaboration
  ( Elab,
    elab,
    checkProgram,
  )
where

import Common
  ( Arg (..),
    CtorGlobal (..),
    DataGlobal (..),
    HasNameSupply (uniqueName),
    PiMode (..),
    mapSpine,
  )
import Data.Bifunctor (bimap)
import Globals (KnownGlobal (..), knownCtor, knownData)
import Presyntax
  ( PCtor (..),
    PData (..),
    PDef (..),
    PItem (..),
    PPrim (..),
    PProgram (..),
    PTm (..),
    pApp,
  )
import Syntax (STm, toPSpine)
import Typechecking
  ( Mode (..),
    Tc (..),
    app,
    caseOf,
    checkByInfer,
    ctorItem,
    dataItem,
    defItem,
    ensureAllProblemsSolved,
    insertLam,
    lam,
    letIn,
    lit,
    meta,
    name,
    piTy,
    primItem,
    repr,
    univ,
    wildPat,
  )
import Value (VTm (..), VTy)

-- Presyntax exists below here

class (Tc m) => Elab m

pKnownCtor :: KnownGlobal CtorGlobal -> [PTm] -> PTm
pKnownCtor k ts = pApp (PName (knownCtor k).globalName) (map (Arg Explicit) ts)

pKnownData :: KnownGlobal DataGlobal -> [PTm] -> PTm
pKnownData d ts = pApp (PName (knownData d).globalName) (map (Arg Explicit) ts)

elab :: (Elab m) => PTm -> Mode -> m (STm, VTy)
elab p mode = case (p, mode) of
  -- Check/both modes:
  (PLocated l t, md) -> enterLoc l (elab t md)
  (PLam m x t, md) -> lam md m x (elab t)
  -- Lambda insertion
  (t, Check (VPi Implicit x' a b)) -> insertLam x' a b (elab t)
  (PUnit, Check ty@VU) -> elab (pKnownData KnownUnit []) (Check ty)
  (PUnit, md) -> elab (pKnownCtor KnownTt []) md
  (PSigma x a b, md) -> elab (pKnownData KnownSigma [a, PLam Explicit x b]) md
  (PPair t1 t2, md) -> elab (pKnownCtor KnownPair [t1, t2]) md
  (PLet x a t u, md) -> letIn md x (elab a) (elab t) (elab u)
  (PRepr m t, md) -> repr md m (elab t)
  (PHole n, md) -> meta md (Just n)
  (PWild, md) -> ifInPat (wildPat md) (meta md Nothing)
  (PLambdaCase cs, md) -> do
    n <- uniqueName
    elab (PLam Explicit n (PCase (PName n) cs)) md
  (PCase s cs, md) -> caseOf md (elab s) (map (bimap elab elab) cs)
  (PLit l, md) -> lit md (fmap elab l)
  (te, Check ty) -> checkByInfer (elab te Infer) ty
  -- Only infer:
  (PName x, Infer) -> name x
  (PApp {}, Infer) -> do
    let (s, sp) = toPSpine p
    app (elab s) (mapSpine elab sp)
  (PU, Infer) -> univ
  (PPi m x a b, Infer) -> piTy m x (elab a) (elab b)

checkDef :: (Elab m) => PDef -> m ()
checkDef def = defItem def.name def.tags (elab def.ty) (elab def.tm)

checkCtor :: (Elab m) => DataGlobal -> PCtor -> m ()
checkCtor dat ctor = ctorItem dat ctor.name ctor.tags (elab ctor.ty)

checkData :: (Elab m) => PData -> m ()
checkData dat = do
  dataItem dat.name dat.tags (elab dat.ty)
  mapM_ (checkCtor (DataGlobal dat.name)) dat.ctors

checkPrim :: (Elab m) => PPrim -> m ()
checkPrim prim = primItem prim.name prim.tags (elab prim.ty)

checkItem :: (Elab m) => PItem -> m ()
checkItem i = do
  r <- case i of
    PDef def -> checkDef def
    PData dat -> checkData dat
    PPrim prim -> checkPrim prim
    PDataRep {} -> return () -- @@Todo
    PDefRep {} -> return () -- @@Todo
    PLocatedItem l i' -> enterLoc l $ checkItem i'
  ensureAllProblemsSolved
  return r

checkProgram :: (Elab m) => PProgram -> m ()
checkProgram (PProgram items) = mapM_ checkItem items
