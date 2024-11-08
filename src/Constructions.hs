{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Constructions (telWithUniqueNames, hMethodTy, hIndicesTel, hElimTy, hMotiveTy, dataConstructions) where

import Common
  ( Arg (..),
    CtorGlobal (..),
    DataGlobal (..),
    Has (..),
    HasNameSupply (uniqueName),
    Lvl (..),
    Name (..),
    Param (..),
    PiMode (..),
    Qty (..),
    Spine,
    Tel,
    mapSpine,
    spineValues,
  )
import Context
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    getCtorGlobal,
    getDataGlobal, DataConstructions, CtorConstructions,
  )
import Syntax
  ( HTel (..),
    HTm (..),
    HTy,
    hApp,
    hPis,
    hSimpleTel,
    sGatherApps,
    sGatherPis,
    unembed,
    unembedTel,
  )

-- Various constructions on datatypes using HOAS

type Constr m = (Has m Ctx)

telWithUniqueNames :: (Constr m) => Tel a -> m (Tel a)
telWithUniqueNames = do
  mapM
    ( \(Param m q n a) -> do
        case n of
          Name "_" -> do
            n' <- uniqueName
            return (Param m q n' a)
          Name _ -> return (Param m q n a)
    )

dataConstructions :: (Constr m) => DataGlobalInfo -> m DataConstructions
dataConstructions = _

ctorConstructions :: (Constr m) => CtorGlobalInfo -> m CtorConstructions
ctorConstructions = _

hMethodTy :: (Constr m) => CtorGlobal -> m (Spine HTm -> HTm -> HTm)
hMethodTy c = do
  ci <- access (getCtorGlobal c)
  di <- access (getDataGlobal ci.dataGlobal)

  -- Access the relevant info
  let (sArgs, sRet) = sGatherPis ci.ty
  sUniqueArgs <- telWithUniqueNames sArgs

  -- Convert to HOAS
  return $ \ps motive ->
    let (_, sRetSp) = sGatherApps sRet in
    let sRetIndexSp = S.drop (length di.params) sRetSp in
    let penv = reverse $ spineValues ps
     in let args = unembedTel penv sUniqueArgs
         in let retSp as = mapSpine (unembed (reverse (spineValues as) ++ penv)) sRetIndexSp
             in hPis args (\as -> hApp motive (retSp as :|> Arg Explicit Zero (hApp (HCtor (c, ps)) as)))

hIndicesTel :: (Constr m) => DataGlobal -> m (Spine HTm -> HTel)
hIndicesTel d = do
  di <- access (getDataGlobal d)

  -- TODO: Create modules for the following:
  --  1. Representation (reprInf goes here)
  --  2. Mapping (over signatures)

  -- Access the relevant info
  sTy <- evalInOwnCtxHere di.ty >>= vUnfold (Lvl (length di.params)) >>= quote (Lvl (length di.params))
  let (sIndices, _) = sGatherPis sTy
  sUniqueIndices <- telWithUniqueNames sIndices

  -- Convert to HOAS
  return $ \ps -> unembedTel (reverse $ spineValues ps) sUniqueIndices

hMotiveTy :: (Constr m) => DataGlobal -> m (Spine HTm -> HTm)
hMotiveTy d = do
  indicesTel <- hIndicesTel d
  return $ \ps -> hPis (indicesTel ps) (const HU)

hElimTy :: (Constr m) => DataGlobal -> m (Spine HTm -> HTy)
hElimTy d = do
  di <- access (getDataGlobal d)

  -- Get HOAS indices and methods
  indicesTel <- hIndicesTel d
  methodTys <- mapM hMethodTy di.ctors

  let motiveTy ps = hPis (indicesTel ps) (const HU)
  let methodsTel ps m = hSimpleTel . S.fromList $ map (\c -> Param Explicit Many (Name "_") (c ps m)) methodTys
  let subjectTy ps is = hApp (HData d) (ps <> is)

  return $ \ps ->
    HPi
      Explicit
      Zero
      (Name "P")
      (motiveTy ps)
      ( \m ->
          hPis
            (methodsTel ps m)
            ( \_ ->
                hPis
                  (indicesTel ps)
                  ( \is ->
                      HPi
                        Explicit
                        Many
                        (Name "s")
                        (subjectTy ps is)
                        (\s -> hApp m (is :|> Arg Explicit Zero s))
                  )
            )
      )
