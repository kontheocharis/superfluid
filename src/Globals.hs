{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    Sig (..),
    getDataGlobal,
    getCtorGlobal,
    getDefGlobal,
    unfoldDef,
    HasSig (..),
    getDataRepr,
    getGlobalRepr,
    getCaseRepr,
    getCtorRepr,
    getDefRepr,
    KnownGlobal (..),
    knownData,
    knownCtor,
  )
where

import Common (CtorGlobal (CtorGlobal), DataGlobal (DataGlobal), DefGlobal, Name (..), globalName, Glob (..), PrimGlobal)
import Data.Map (Map)
import qualified Data.Map as M
import Value (VTm, VTy)

data CtorGlobalInfo = CtorGlobalInfo {ty :: VTm, idx :: Int, dataGlobal :: DataGlobal}

data DataGlobalInfo = DataGlobalInfo {ty :: VTm, ctors :: [CtorGlobal]}

data DefGlobalInfo = DefGlobalInfo {ty :: VTy, tm :: VTm}

data PrimGlobalInfo = PrimGlobalInfo {ty :: VTm}

data GlobalInfo = DataInfo DataGlobalInfo | CtorInfo CtorGlobalInfo | DefInfo DefGlobalInfo | PrimInfo PrimGlobalInfo

data Sig = Sig
  { contents :: Map Name GlobalInfo,
    repr :: Map Name VTm,
    reprCase :: Map Name VTm
  }

getDataGlobal :: DataGlobal -> Sig -> DataGlobalInfo
getDataGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (DataInfo info) -> info
  Just _ -> error "getDataGlobal: not a data global"
  _ -> error "getDataGlobal: not a global"

getCtorGlobal :: CtorGlobal -> Sig -> CtorGlobalInfo
getCtorGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (CtorInfo info) -> info
  Just _ -> error "getCtorGlobal: not a ctor global"
  _ -> error "getCtorGlobal: not a global"

getDefGlobal :: DefGlobal -> Sig -> DefGlobalInfo
getDefGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (DefInfo info) -> info
  Just _ -> error "getDefGlobal: not a def global"
  _ -> error "getDefGlobal: not a global"

lookupGlobal :: Name -> Sig -> Maybe GlobalInfo
lookupGlobal n sig = M.lookup n sig.contents

unfoldDef :: DefGlobal -> Sig -> VTm
unfoldDef g sig = (getDefGlobal g sig).tm



getDataRepr :: DataGlobal -> Sig -> VTm
getDataRepr g sig = case M.lookup g.globalName sig.repr of
  Just t -> t
  Nothing -> error $ "getDataRepr: no repr for data " ++ show g

getCaseRepr :: DataGlobal -> Sig -> VTm
getCaseRepr g sig = case M.lookup g.globalName sig.reprCase of
  Just t -> t
  Nothing -> error $ "getCaseRepr: no repr for data " ++ show g

getCtorRepr :: CtorGlobal -> Sig -> VTm
getCtorRepr g sig = case M.lookup g.globalName sig.repr of
  Just t -> t
  Nothing -> error $ "getCtorRepr: no repr for constructor " ++ show g

getDefRepr :: DefGlobal -> Sig -> VTm
getDefRepr g sig = case M.lookup g.globalName sig.repr of
  Just t -> t
  Nothing -> error $ "getDefRepr: no repr for def " ++ show g

getPrimRepr :: PrimGlobal -> Sig -> VTm
getPrimRepr g sig = case M.lookup g.globalName sig.repr of
  Just t -> t
  Nothing -> error $ "getPrimRepr: no repr for prim " ++ show g

getGlobalRepr :: Glob -> Sig -> VTm
getGlobalRepr (DataGlob g) = getDataRepr g
getGlobalRepr (CtorGlob g) = getCtorRepr g
getGlobalRepr (DefGlob g) = getDefRepr g
getGlobalRepr (PrimGlob g) = getPrimRepr g

class (Monad m) => HasSig m where
  getSig :: m Sig

  accessSig :: (Sig -> a) -> m a
  accessSig f = f <$> getSig

data KnownGlobal a where
  KnownSigma :: KnownGlobal DataGlobal
  KnownPair :: KnownGlobal CtorGlobal

deriving instance Show (KnownGlobal a)

deriving instance Eq (KnownGlobal a)

knownData :: KnownGlobal DataGlobal -> DataGlobal
knownData KnownSigma = DataGlobal (Name "Sigma")

knownCtor :: KnownGlobal CtorGlobal -> CtorGlobal
knownCtor KnownPair = CtorGlobal (Name "pair")
