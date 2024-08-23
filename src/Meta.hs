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
  )
where

import Common (Has, MetaVar (..), Modify (..), Name, View (..))
import Control.Monad.Trans (MonadTrans (..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Maybe (fromJust)
import Value (VTm)

newtype SolvedMetas = SolvedMetas {values :: IntMap (Maybe VTm, Maybe Name)}

type HasMetas m = (Has m SolvedMetas)

emptySolvedMetas :: SolvedMetas
emptySolvedMetas = SolvedMetas IM.empty

lookupMetaVar :: (Has m SolvedMetas) => MetaVar -> m (Maybe VTm)
lookupMetaVar (MetaVar m) = do
  SolvedMetas ms <- view
  let (tm, _) = fromJust $ IM.lookup m ms
  return tm

lookupMetaVarName :: (Has m SolvedMetas) => MetaVar -> m (Maybe Name)
lookupMetaVarName (MetaVar m) = do
  SolvedMetas ms <- view
  let (_, name) = fromJust $ IM.lookup m ms
  return name

freshMetaVar :: (Has m SolvedMetas) => Maybe Name -> m MetaVar
freshMetaVar n = do
  SolvedMetas ms <- view
  let c = IM.size ms
  modify (\m -> m {values = IM.insert c (Nothing, n) m.values})
  return (MetaVar c)

solveMetaVar :: (Has m SolvedMetas) => MetaVar -> VTm -> m ()
solveMetaVar (MetaVar m) v' =
  modify (\sm -> sm {values = IM.update (\(_, n) -> Just (Just v', n)) m sm.values})

resetSolvedMetas :: (Has m SolvedMetas) => m ()
resetSolvedMetas = modify (const emptySolvedMetas)
