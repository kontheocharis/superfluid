{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Constructions (telWithUniqueNames, hMethodTy, hIndicesTel, hElimTy, hMotiveTy, dataConstructions, ctorConstructions) where

import Common
  ( Arg (..),
    CtorGlobal (..),
    Has (..),
    HasNameSupply (uniqueName),
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
  ( CtorConstructions (..),
    CtorGlobalInfo (..),
    DataConstructions (..),
    DataGlobalInfo (..),
    Sig,
    dataGlobalFromInfo,
    getCtorGlobal,
    getDataGlobal,
  )
import Syntax
  ( Env,
    HTel (..),
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

type Constr m = (Has m Ctx, HasNameSupply m, Has m Sig)

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

ctorConstructions :: (Constr m) => CtorGlobalInfo -> m CtorConstructions
ctorConstructions ci = do
  ctorArgs <- hCtorArgs ci
  ctorReturnTy <- hCtorReturnTy ci
  ctorReturnIndices <- hCtorReturnIndices ci
  return $ CtorConstructions {args = ctorArgs, returnTy = ctorReturnTy, returnIndices = ctorReturnIndices}

dataConstructions :: (Constr m) => DataGlobalInfo -> m DataConstructions
dataConstructions di = do
  let paramsTel = unembedTel [] di.params
  indicesTel <- hIndicesTel di
  motiveTy <- hMotiveTy indicesTel
  methodTys <- mapM hMethodTy di.ctors
  elimTy <- hElimTy di indicesTel motiveTy methodTys
  return $
    DataConstructions
      { params = paramsTel,
        indices = indicesTel,
        motive = motiveTy,
        elim = elimTy
      }

type HCtorArgs = Spine HTm -> HTel

spineToEnv :: Spine HTm -> Env HTm
spineToEnv = reverse . spineValues

hCtorArgs :: (Constr m) => CtorGlobalInfo -> m HCtorArgs
hCtorArgs ci = do
  let (sArgs, _) = sGatherPis ci.ty
  return $ \ps -> unembedTel (spineToEnv ps) sArgs

type HCtorReturnTy = Spine HTm -> Spine HTm -> HTm

hCtorReturnTy :: (Constr m) => CtorGlobalInfo -> m HCtorReturnTy
hCtorReturnTy ci = do
  let (_, sRet) = sGatherPis ci.ty
  return $ \ps is -> unembed (spineToEnv (ps <> is) ++ spineToEnv ps) sRet

type HCtorReturnIndices = Spine HTm -> Spine HTm -> Spine HTm

hCtorReturnIndices :: (Constr m) => CtorGlobalInfo -> m HCtorReturnIndices
hCtorReturnIndices ci = do
  let (_, sRet) = sGatherPis ci.ty
  let (_, sRetSp) = sGatherApps sRet
  return $ \ps is -> mapSpine (unembed (spineToEnv (ps <> is) ++ spineToEnv ps)) sRetSp

type HMethodTy = Spine HTm -> HTm -> HTm

hMethodTy :: (Constr m) => CtorGlobal -> m HMethodTy
hMethodTy c = do
  ci <- access (getCtorGlobal c)
  di <- access (getDataGlobal ci.dataGlobal)

  -- Access the relevant info
  let (sArgs, sRet) = sGatherPis ci.ty
  sUniqueArgs <- telWithUniqueNames sArgs

  -- Convert to HOAS
  return $ \ps motive ->
    let (_, sRetSp) = sGatherApps sRet
     in let sRetIndexSp = S.drop (length di.params) sRetSp
         in let penv = spineToEnv ps
             in let args = unembedTel penv sUniqueArgs
                 in let retSp as = mapSpine (unembed (spineToEnv as ++ penv)) sRetIndexSp
                     in hPis args (\as -> hApp motive (retSp as :|> Arg Explicit Zero (hApp (HCtor (c, ps)) as)))

type HIndicesTel = Spine HTm -> HTel

hIndicesTel :: (Constr m) => DataGlobalInfo -> m HIndicesTel
hIndicesTel di = do
  -- TODO: Create modules for the following:
  --  1. Representation (reprInf goes here)
  --  2. Mapping (over signatures)

  -- Access the relevant info
  let (sIndices, _) = sGatherPis di.familyTy
  sUniqueIndices <- telWithUniqueNames sIndices

  -- Convert to HOAS
  return $ \ps -> unembedTel (spineToEnv ps) sUniqueIndices

type HMotiveTy = Spine HTm -> HTm

hMotiveTy :: (Constr m) => HIndicesTel -> m HMotiveTy
hMotiveTy te = return $ \ps -> hPis (te ps) (const HU)

hElimTy :: (Constr m) => DataGlobalInfo -> HIndicesTel -> HMotiveTy -> [HMethodTy] -> m (Spine HTm -> HTy)
hElimTy di indicesTel motiveTy methodTys = do
  -- Get HOAS indices and methods
  let methodsTel ps m = hSimpleTel . S.fromList $ map (\c -> Param Explicit Many (Name "_") (c ps m)) methodTys
  let subjectTy ps is = hApp (HData (dataGlobalFromInfo di)) (ps <> is)

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
