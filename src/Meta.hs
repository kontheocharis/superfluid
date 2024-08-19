module Meta
  ( SolvedMetas (..),
    emptySolvedMetas,
    HasMetas (..),
  )
where

import Common (MetaVar (..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Value (VTm)

newtype SolvedMetas = SolvedMetas (IntMap VTm)

emptySolvedMetas :: SolvedMetas
emptySolvedMetas = SolvedMetas IM.empty

class (Monad m) => HasMetas m where
  solvedMetas :: m SolvedMetas
  modifySolvedMetas :: (SolvedMetas -> SolvedMetas) -> m ()

  lookupMeta :: MetaVar -> m (Maybe VTm)
  lookupMeta (MetaVar m) = do
    SolvedMetas ms <- solvedMetas
    return $ IM.lookup m ms

  solveMeta :: MetaVar -> VTm -> m ()
  solveMeta (MetaVar m) tm = modifySolvedMetas (\(SolvedMetas ms) -> SolvedMetas (IM.insert m tm ms))

  resetSolvedMetas :: m ()
  resetSolvedMetas = modifySolvedMetas (const emptySolvedMetas)
