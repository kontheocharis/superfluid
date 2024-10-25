{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Meta
  ( SolvedMetas,
    emptySolvedMetas,
    lookupMetaVar,
    lookupMetaVarName,
    freshMetaVar,
    solveMetaVar,
    resetSolvedMetas,
    HasMetas,
    lookupMetaVarQty,
  )
where

import Common (Has (..), MetaVar (..), Name, Qty)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Maybe (fromJust)
import Syntax (VTm)

newtype SolvedMetas = SolvedMetas {values :: IntMap (Maybe VTm, Qty, Maybe Name)}

type HasMetas m = (Has m SolvedMetas)

emptySolvedMetas :: SolvedMetas
emptySolvedMetas = SolvedMetas IM.empty

lookupMetaVar :: (Has m SolvedMetas) => MetaVar -> m (Maybe VTm)
lookupMetaVar (MetaVar m) = do
  SolvedMetas ms <- view
  let (tm, _, _) = fromJust $ IM.lookup m ms
  return tm

lookupMetaVarName :: (Has m SolvedMetas) => MetaVar -> m (Maybe Name)
lookupMetaVarName (MetaVar m) = do
  SolvedMetas ms <- view
  let (_, _, name) = fromJust $ IM.lookup m ms
  return name

lookupMetaVarQty :: (Has m SolvedMetas) => MetaVar -> m Qty
lookupMetaVarQty (MetaVar m) = do
  SolvedMetas ms <- view
  let (_, qty, _) = fromJust $ IM.lookup m ms
  return qty

freshMetaVar :: (Has m SolvedMetas) => Maybe Name -> Qty -> m MetaVar
freshMetaVar n q = do
  SolvedMetas ms <- view
  let c = IM.size ms
  modify (\m -> m {values = IM.insert c (Nothing, q, n) m.values})
  return (MetaVar c)

solveMetaVar :: (Has m SolvedMetas) => MetaVar -> VTm -> m ()
solveMetaVar (MetaVar m) v' =
  modify (\sm -> sm {values = IM.update (\(_, q, n) -> Just (Just v', q, n)) m sm.values})

resetSolvedMetas :: (Has m SolvedMetas) => m ()
resetSolvedMetas = modify (const emptySolvedMetas)
