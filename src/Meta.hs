module Meta
  ( SolvedMetas (..),
    emptySolvedMetas,
    HasSolvedMetas (..),
  )
where

import Common (MetaVar (..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Value (VTm)

newtype SolvedMetas = SolvedMetas (IntMap VTm)

emptySolvedMetas :: SolvedMetas
emptySolvedMetas = SolvedMetas IM.empty

class (Monad m) => HasSolvedMetas m where
  solvedMetas :: m SolvedMetas
  modifySolvedMetas :: (SolvedMetas -> SolvedMetas) -> m ()

  lookupMeta :: MetaVar -> m (Maybe VTm)
  lookupMeta (MetaVar m) = do
    SolvedMetas ms <- solvedMetas
    return $ IM.lookup m ms

  resetSolvedMetas :: m ()
  resetSolvedMetas = modifySolvedMetas (const emptySolvedMetas)
