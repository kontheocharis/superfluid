module Traversal (mapGlobalInfoM) where

import Common
  ( Has (..),
    Lvl (..),
    Param (..),
    Tel,
    nextLvl, DataGlobal (DataGlobal),
  )
import Constructions (ctorConstructions, dataConstructions)
import Data.Foldable (traverse_)
import Data.Sequence (Seq (..))
import Evaluation (Eval (..), eval, quote)
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    PrimGlobalInfo (..),
    getCtorGlobal,
    modifyCtorItem, getDataGlobal,
  )
import Syntax
  ( STm (..),
  )

mapTelM :: (Eval m) => Lvl -> (Lvl -> STm -> m STm) -> Tel STm -> m (Tel STm)
mapTelM _ _ Empty = return Empty
mapTelM l f (Param m q x a :<| tel) = do
  a' <- f l a
  tel' <- mapTelM (nextLvl l) f tel
  return $ Param m q x a' :<| tel'

mapDataGlobalInfoM :: (Eval m) => (Lvl -> STm -> m STm) -> DataGlobalInfo -> m DataGlobalInfo
mapDataGlobalInfoM f (DataGlobalInfo n params ty ctors _) = do
  di <- access (getDataGlobal (DataGlobal n))
  params' <- mapTelM (Lvl 0) f params
  ty' <- f (Lvl (length di.params)) ty
  traverse_
    ( \c -> do
        ci <- access (getCtorGlobal c)
        c' <- mapCtorGlobalInfoM f ci
        modify $ modifyCtorItem c (const c')
    )
    ctors
  constructions' <- dataConstructions (DataGlobalInfo n params' ty' ctors Nothing)
  return $ DataGlobalInfo n params' ty' ctors (Just constructions')

mapCtorGlobalInfoM :: (Eval m) => (Lvl -> STm -> m STm) -> CtorGlobalInfo -> m CtorGlobalInfo
mapCtorGlobalInfoM f (CtorGlobalInfo n q ty idx qtySum dataGlobal _) = do
  di <- access (getDataGlobal dataGlobal)
  ty' <- f (Lvl (length di.params)) ty
  constructions' <- ctorConstructions (CtorGlobalInfo n q ty' idx qtySum dataGlobal Nothing)
  return $ CtorGlobalInfo n q ty' idx qtySum dataGlobal (Just constructions')

mapDefGlobalInfoM :: (Eval m) => (Lvl -> STm -> m STm) -> DefGlobalInfo -> m DefGlobalInfo
mapDefGlobalInfoM f (DefGlobalInfo n q ty _ tm) = do
  ty' <- quote (Lvl 0) ty >>= f (Lvl 0) >>= eval []
  tm' <- traverse (f (Lvl 0)) tm
  vtm' <- traverse (eval []) tm'
  tm'' <- traverse (quote (Lvl 0)) vtm'
  return $ DefGlobalInfo n q ty' vtm' tm''

mapPrimGlobalInfoM :: (Eval m) => (Lvl -> STm -> m STm) -> PrimGlobalInfo -> m PrimGlobalInfo
mapPrimGlobalInfoM f (PrimGlobalInfo n q ty) = do
  ty' <- quote (Lvl 0) ty >>= f (Lvl 0) >>= eval []
  return $ PrimGlobalInfo n q ty'

mapGlobalInfoM :: (Eval m) => (Lvl -> STm -> m STm) -> GlobalInfo -> m GlobalInfo
mapGlobalInfoM f i = case i of
  DataInfo d -> DataInfo <$> mapDataGlobalInfoM f d
  CtorInfo c -> CtorInfo <$> mapCtorGlobalInfoM f c
  DefInfo d -> DefInfo <$> mapDefGlobalInfoM f d
  PrimInfo p -> PrimInfo <$> mapPrimGlobalInfoM f p
