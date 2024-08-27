{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    PrimGlobalInfo (..),
    GlobalInfo (..),
    Sig (..),
    getDataGlobal,
    getCtorGlobal,
    getDefGlobal,
    unfoldDef,
    getGlobal,
    getGlobalTags,
    modifyDefItem,
    getDataRepr,
    getGlobalRepr,
    getCaseRepr,
    getCtorRepr,
    getDefRepr,
    modifyDataItem,
    KnownGlobal (..),
    knownData,
    knownCtor,
    lookupGlobal,
    hasName,
    emptySig,
    globalInfoToTm,
    addItem,
  )
where

import Common (CtorGlobal (CtorGlobal), DataGlobal (DataGlobal), DefGlobal (DefGlobal), Glob (..), Name (..), PrimGlobal (..), Tag, globalName)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set
import Syntax (STm (..))
import Value (VTm (..), VTy)

data CtorGlobalInfo = CtorGlobalInfo {ty :: VTm, idx :: Int, dataGlobal :: DataGlobal}

data DataGlobalInfo = DataGlobalInfo {ty :: VTm, ctors :: [CtorGlobal]}

data DefGlobalInfo = DefGlobalInfo {ty :: VTy, vtm :: Maybe VTm, tm :: Maybe STm} -- might not be set yet if

newtype PrimGlobalInfo = PrimGlobalInfo {ty :: VTm}

data GlobalInfo = DataInfo DataGlobalInfo | CtorInfo CtorGlobalInfo | DefInfo DefGlobalInfo | PrimInfo PrimGlobalInfo

data Sig = Sig
  { contents :: Map Name GlobalInfo,
    nameOrder :: [Name],
    tags :: Map Name (Set Tag),
    repr :: Map Name VTm,
    reprCase :: Map Name VTm
  }

emptySig :: Sig
emptySig = Sig M.empty [] M.empty M.empty M.empty

hasName :: Name -> Sig -> Bool
hasName n s = M.member n s.contents

addItem :: Name -> GlobalInfo -> Set Tag -> Sig -> Sig
addItem n i ts s =
  s
    { contents = M.insert n i s.contents,
      nameOrder = s.nameOrder ++ [n],
      tags = M.insert n ts s.tags
    }

modifyDataItem :: DataGlobal -> (DataGlobalInfo -> DataGlobalInfo) -> Sig -> Sig
modifyDataItem dat f s = s {contents = M.insert dat.globalName (DataInfo (f (getDataGlobal dat s))) s.contents}

modifyDefItem :: DefGlobal -> (DefGlobalInfo -> DefGlobalInfo) -> Sig -> Sig
modifyDefItem def f s = s {contents = M.insert def.globalName (DefInfo (f (getDefGlobal def s))) s.contents}

getDataGlobal :: DataGlobal -> Sig -> DataGlobalInfo
getDataGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (DataInfo info) -> info
  Just _ -> error $ "getDataGlobal: not a data global" ++ show g
  _ -> error $ "getDataGlobal: not a global" ++ show g

getCtorGlobal :: CtorGlobal -> Sig -> CtorGlobalInfo
getCtorGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (CtorInfo info) -> info
  Just _ -> error $ "getCtorGlobal: not a ctor global: "  ++ show g
  _ -> error $ "getCtorGlobal: not a global" ++ show g

getDefGlobal :: DefGlobal -> Sig -> DefGlobalInfo
getDefGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (DefInfo info) -> info
  Just _ -> error $ "getDefGlobal: not a def global" ++ show g
  _ -> error $ "getDefGlobal: not a global" ++ show g

getGlobal :: Name -> Sig -> GlobalInfo
getGlobal n sig = case M.lookup n sig.contents of
  Just i -> i
  Nothing -> error $ "getGlobal: no global named " ++ show n

getGlobalTags :: Name -> Sig -> Set Tag
getGlobalTags n sig = case M.lookup n sig.tags of
  Just t -> t
  Nothing -> error $ "getGlobalTags: no tags for global " ++ show n

lookupGlobal :: Name -> Sig -> Maybe GlobalInfo
lookupGlobal n sig = M.lookup n sig.contents

globalInfoToTm :: Name -> GlobalInfo -> (STm, VTy)
globalInfoToTm n i = case i of
  DefInfo d -> (SGlobal (DefGlob (DefGlobal n)), d.ty)
  DataInfo d -> (SGlobal (DataGlob (DataGlobal n)), d.ty)
  CtorInfo c -> (SGlobal (CtorGlob (CtorGlobal n)), c.ty)
  PrimInfo p -> (SGlobal (PrimGlob (PrimGlobal n)), p.ty)

unfoldDef :: DefGlobal -> Sig -> Maybe VTm
unfoldDef g sig = (getDefGlobal g sig).vtm

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

data KnownGlobal a where
  KnownSigma :: KnownGlobal DataGlobal
  KnownPair :: KnownGlobal CtorGlobal
  KnownNat :: KnownGlobal DataGlobal
  KnownZero :: KnownGlobal CtorGlobal
  KnownSucc :: KnownGlobal CtorGlobal
  KnownFin :: KnownGlobal DataGlobal
  KnownFZero :: KnownGlobal CtorGlobal
  KnownFSucc :: KnownGlobal CtorGlobal
  KnownChar :: KnownGlobal DataGlobal
  KnownChr :: KnownGlobal CtorGlobal
  KnownList :: KnownGlobal DataGlobal
  KnownNil :: KnownGlobal CtorGlobal
  KnownCons :: KnownGlobal CtorGlobal
  KnownString :: KnownGlobal DataGlobal
  KnownStr :: KnownGlobal CtorGlobal
  KnownUnit :: KnownGlobal DataGlobal
  KnownTt :: KnownGlobal CtorGlobal

deriving instance Show (KnownGlobal a)

deriving instance Eq (KnownGlobal a)

knownData :: KnownGlobal DataGlobal -> DataGlobal
knownData KnownSigma = DataGlobal (Name "Sigma")
knownData KnownNat = DataGlobal (Name "Nat")
knownData KnownFin = DataGlobal (Name "Fin")
knownData KnownChar = DataGlobal (Name "Char")
knownData KnownList = DataGlobal (Name "List")
knownData KnownString = DataGlobal (Name "String")
knownData KnownUnit = DataGlobal (Name "Unit")

knownCtor :: KnownGlobal CtorGlobal -> CtorGlobal
knownCtor KnownPair = CtorGlobal (Name "pair")
knownCtor KnownZero = CtorGlobal (Name "z")
knownCtor KnownSucc = CtorGlobal (Name "s")
knownCtor KnownFZero = CtorGlobal (Name "fz")
knownCtor KnownFSucc = CtorGlobal (Name "fs")
knownCtor KnownChr = CtorGlobal (Name "chr")
knownCtor KnownNil = CtorGlobal (Name "nil")
knownCtor KnownCons = CtorGlobal (Name "cons")
knownCtor KnownStr = CtorGlobal (Name "str")
knownCtor KnownTt = CtorGlobal (Name "tt")
