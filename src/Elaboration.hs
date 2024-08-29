{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Elaboration
  ( Elab,
    infer,
    checkProgram,
    check,
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
import Evaluation (force)
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
elab p Infer = infer p
elab p (Check ty) = check p ty

check :: (Elab m) => PTm -> VTy -> m (STm, VTy)
check term typ = do
  typ' <- force typ
  case (term, typ') of
    (PLocated l t, ty) -> enterLoc l (check t ty)
    (PLam m x t, ty) -> lam (Check ty) m x (elab t)
    (t, VPi Implicit x' a b) -> insertLam x' a b (elab t)
    (PUnit, ty@VU) -> check (pKnownData KnownUnit []) ty
    (PUnit, ty) -> check (pKnownCtor KnownTt []) ty
    (PLet x a t u, ty) -> letIn (Check ty) x (elab a) (elab t) (elab u)
    (PRepr m t, ty) -> repr (Check ty) m (elab t)
    (PHole n, ty) -> meta (Check ty) (Just n)
    (PWild, ty) ->
      ifInPat
        (wildPat (Check ty))
        (meta (Check ty) Nothing)
    (PLambdaCase cs, ty) -> do
      n <- uniqueName
      check (PLam Explicit n (PCase (PName n) cs)) ty
    (PCase s cs, ty) -> caseOf (Check ty) (elab s) (map (bimap elab elab) cs)
    (te, ty) -> checkByInfer (infer te) ty

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterLoc l $ infer t
  PName x -> name x
  PSigma x a b -> infer $ pKnownData KnownSigma [a, PLam Explicit x b]
  PUnit -> infer $ pKnownData KnownUnit []
  PPair t1 t2 -> infer $ pKnownCtor KnownPair [t1, t2]
  PLam m x t -> lam Infer m x (elab t)
  PApp {} -> do
    let (s, sp) = toPSpine term
    app (elab s) (mapSpine elab sp)
  PU -> univ
  PPi m x a b -> piTy m x (elab a) (elab b)
  PLet x a t u -> letIn Infer x (elab a) (elab t) (elab u)
  PRepr m x -> repr Infer m (elab x)
  PHole n -> meta Infer (Just n)
  PWild ->
    ifInPat
      (wildPat Infer)
      (meta Infer Nothing)
  PLambdaCase cs -> do
    n <- uniqueName
    infer $ PLam Explicit n (PCase (PName n) cs)
  PCase s cs -> caseOf Infer (elab s) (map (bimap elab elab) cs)
  PLit l -> lit Infer (fmap elab l)

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
