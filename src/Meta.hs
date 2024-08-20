module Meta
  ( SolvedMetas,
    emptySolvedMetas,
    HasMetas (..),
  )
where

import Common (MetaVar (..), Name)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Maybe (fromJust)
import Value (VTm)

newtype SolvedMetas = SolvedMetas {values :: IntMap (Maybe VTm, Maybe Name)}

emptySolvedMetas :: SolvedMetas
emptySolvedMetas = SolvedMetas IM.empty

class (Monad m) => HasMetas m where
  solvedMetas :: m SolvedMetas
  modifySolvedMetas :: (SolvedMetas -> SolvedMetas) -> m ()

  lookupMetaVar :: MetaVar -> m (Maybe VTm)
  lookupMetaVar (MetaVar m) = do
    SolvedMetas ms <- solvedMetas
    let (tm, _) = fromJust $ IM.lookup m ms
    return tm

  lookupMetaVarName :: MetaVar -> m (Maybe Name)
  lookupMetaVarName (MetaVar m) = do
    SolvedMetas ms <- solvedMetas
    let (_, name) = fromJust $ IM.lookup m ms
    return name

  freshMetaVar :: Maybe Name -> m MetaVar
  freshMetaVar n = do
    c <- (\m -> IM.size m.values) <$> solvedMetas
    modifySolvedMetas (\m -> m {values = IM.insert c (Nothing, n) m.values})
    return (MetaVar c)

  solveMetaVar :: MetaVar -> VTm -> m ()
  solveMetaVar (MetaVar m) v' =
    modifySolvedMetas (\sm -> sm {values = IM.update (\(_, n) -> Just (Just v', n)) m sm.values})

  resetSolvedMetas :: m ()
  resetSolvedMetas = modifySolvedMetas (const emptySolvedMetas)
