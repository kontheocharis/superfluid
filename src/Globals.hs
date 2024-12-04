{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    PrimGlobalInfo (..),
    GlobalInfo (..),
    Sig (..),
    InstanceInfo (..),
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
    knownPrim,
    knownDef,
    mapSigContentsM,
    mapSigContentsM_,
    getDefRepr,
    modifyDataItem,
    KnownGlobal (..),
    DataConstructions (..),
    CtorConstructions (..),
    knownData,
    knownCtor,
    removeRepresentedItems,
    lookupGlobal,
    hasName,
    emptySig,
    addItem,
    addCaseRepr,
    addCtorRepr,
    addDataRepr,
    addDefRepr,
    dataIsIrrelevant,
    unfoldDefSyntax,
    getPrimGlobal,
    modifyPrimItem,
    modifyCtorItem,
    dataGlobalFromInfo,
    lookupInstance,
    instances,
    addInstanceItem,
    getCtorGlobal',
    getDataGlobal',
  )
where

import Common
  ( CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (..),
    Glob (..),
    Name (..),
    PrimGlobal (..),
    Qty (..),
    Spine,
    Tag (UnfoldTag),
    Tel,
    globalName,
  )
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as S
import Syntax (Closure, HTel, HTm, HTy, Pat, STm (..), STy, VTm (..), VTy)

data CtorGlobalInfo = CtorGlobalInfo
  { name :: Name,
    qty :: Qty,
    ty :: STy,
    index :: Int,
    qtySum :: Qty,
    dataGlobal :: DataGlobal,
    constructions :: Maybe CtorConstructions
  }

data CtorConstructions = CtorConstructions
  { args :: Spine HTm -> HTel,
    argsArity :: Tel (),
    ty :: Spine HTm -> HTy,
    returnIndices :: Spine HTm -> Spine HTm -> Spine HTm,
    returnTy :: Spine HTm -> Spine HTm -> HTm
  }

data DataGlobalInfo = DataGlobalInfo
  { name :: Name,
    params :: Tel STy,
    familyTy :: STy,
    ctors :: [CtorGlobal],
    constructions :: Maybe DataConstructions
  }

dataGlobalFromInfo :: DataGlobalInfo -> DataGlobal
dataGlobalFromInfo di = DataGlobal di.name

data DataConstructions = DataConstructions
  { params :: HTel,
    paramsArity :: Tel (),
    motive :: Spine HTm -> HTm,
    elim :: Spine HTm -> HTm,
    indices :: Spine HTm -> HTel,
    indicesArity :: Tel ()
  }

data DefGlobalInfo = DefGlobalInfo
  { name :: Name,
    qty :: Qty,
    ty :: VTy,
    vtm :: Maybe VTm,
    tm :: Maybe STm -- might not be set yet
  }

data PrimGlobalInfo = PrimGlobalInfo
  { name :: Name,
    qty :: Qty,
    ty :: VTm
  }

data GlobalInfo
  = DataInfo DataGlobalInfo
  | CtorInfo CtorGlobalInfo
  | DefInfo DefGlobalInfo
  | PrimInfo PrimGlobalInfo

data InstanceInfo = InstanceInfo
  { origin :: DefGlobal,
    ty :: VTy
  }

data Sig = Sig
  { contents :: Map Name GlobalInfo,
    nameOrder :: [Name],
    tags :: Map Name (Set Tag),
    repr :: Map Name (Closure, Set Tag),
    reprCase :: Map Name (Closure, Set Tag),
    instances :: Map VTy InstanceInfo -- Lvl 0
  }

mapSigContentsM :: (Monad m) => (GlobalInfo -> m GlobalInfo) -> Sig -> m Sig
mapSigContentsM f s = do
  contents' <-
    M.fromList
      <$> mapM
        (\n -> (n,) <$> f (getGlobal n s))
        s.nameOrder
  return $ s {contents = contents'}

mapSigContentsM_ :: (Monad m) => (GlobalInfo -> m ()) -> Sig -> m ()
mapSigContentsM_ f s = do
  mapM_
    (\n -> f (getGlobal n s))
    s.nameOrder

removeRepresentedItems :: Sig -> Sig
removeRepresentedItems s =
  let contents' =
        M.filterWithKey
          (\k _ -> not (M.member k s.repr || M.member k s.reprCase || S.member UnfoldTag (s.tags M.! k)))
          s.contents
   in s
        { contents = contents',
          repr = M.empty,
          reprCase = M.empty,
          nameOrder = filter (`M.member` contents') s.nameOrder
        }

emptySig :: Sig
emptySig = Sig M.empty [] M.empty M.empty M.empty M.empty

hasName :: Name -> Sig -> Bool
hasName n s = M.member n s.contents

addItem :: Name -> GlobalInfo -> Set Tag -> Sig -> Sig
addItem n i ts s =
  s
    { contents = M.insert n i s.contents,
      nameOrder = s.nameOrder ++ [n],
      tags = M.insert n ts s.tags
    }

addDataRepr :: DataGlobal -> Closure -> Set Tag -> Sig -> Sig
addDataRepr g t ts s = s {repr = M.insert g.globalName (t, ts) s.repr}

addCaseRepr :: DataGlobal -> Closure -> Set Tag -> Sig -> Sig
addCaseRepr g t ts s = s {reprCase = M.insert g.globalName (t, ts) s.reprCase}

addCtorRepr :: CtorGlobal -> Closure -> Set Tag -> Sig -> Sig
addCtorRepr g t ts s = s {repr = M.insert g.globalName (t, ts) s.repr}

addDefRepr :: DefGlobal -> Closure -> Set Tag -> Sig -> Sig
addDefRepr g t ts s = s {repr = M.insert g.globalName (t, ts) s.repr}

addInstanceItem :: VTy -> InstanceInfo -> Sig -> Sig
addInstanceItem ty info s = s {instances = M.insert ty info s.instances}

modifyDataItem :: DataGlobal -> (DataGlobalInfo -> DataGlobalInfo) -> Sig -> Sig
modifyDataItem dat f s = s {contents = M.insert dat.globalName (DataInfo (f (getDataGlobal dat s))) s.contents}

modifyDefItem :: DefGlobal -> (DefGlobalInfo -> DefGlobalInfo) -> Sig -> Sig
modifyDefItem def f s = s {contents = M.insert def.globalName (DefInfo (f (getDefGlobal def s))) s.contents}

modifyPrimItem :: PrimGlobal -> (PrimGlobalInfo -> PrimGlobalInfo) -> Sig -> Sig
modifyPrimItem def f s = s {contents = M.insert def.globalName (PrimInfo (f (getPrimGlobal def s))) s.contents}

modifyCtorItem :: CtorGlobal -> (CtorGlobalInfo -> CtorGlobalInfo) -> Sig -> Sig
modifyCtorItem ctor f s = s {contents = M.insert ctor.globalName (CtorInfo (f (getCtorGlobal ctor s))) s.contents}

getDataGlobal :: DataGlobal -> Sig -> DataGlobalInfo
getDataGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (DataInfo info) -> info
  Just _ -> error $ "getDataGlobal: not a data global" ++ show g
  _ -> error $ "getDataGlobal: not a global" ++ show g

getDataGlobal' :: DataGlobal -> Sig -> (DataGlobalInfo, DataConstructions)
getDataGlobal' g sig = let di = getDataGlobal g sig in (di, fromJust $ di.constructions)

getCtorGlobal :: CtorGlobal -> Sig -> CtorGlobalInfo
getCtorGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (CtorInfo info) -> info
  Just _ -> error $ "getCtorGlobal: not a ctor global: " ++ show g
  _ -> error $ "getCtorGlobal: not a global" ++ show g

getCtorGlobal' :: CtorGlobal -> Sig -> (CtorGlobalInfo, CtorConstructions)
getCtorGlobal' g sig = let ci = getCtorGlobal g sig in (ci, fromJust $ ci.constructions)

getDefGlobal :: DefGlobal -> Sig -> DefGlobalInfo
getDefGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (DefInfo info) -> info
  Just _ -> error $ "getDefGlobal: not a def global" ++ show g
  _ -> error $ "getDefGlobal: not a global" ++ show g

getPrimGlobal :: PrimGlobal -> Sig -> PrimGlobalInfo
getPrimGlobal g sig = case M.lookup g.globalName sig.contents of
  Just (PrimInfo info) -> info
  Just _ -> error $ "getPrimGlobal: not a prim global" ++ show g
  _ -> error $ "getPrimGlobal: not a global" ++ show g

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

lookupInstance :: VTy -> Sig -> Maybe InstanceInfo
lookupInstance ty sig = M.lookup ty sig.instances

instances :: Sig -> [(VTy, InstanceInfo)]
instances sig = M.toList sig.instances

unfoldDef :: DefGlobal -> Sig -> Maybe VTm
unfoldDef g sig = (getDefGlobal g sig).vtm

unfoldDefSyntax :: DefGlobal -> Sig -> Maybe STm
unfoldDefSyntax g sig = (getDefGlobal g sig).tm

getDataRepr :: DataGlobal -> Sig -> Maybe Closure
getDataRepr g sig = fst <$> M.lookup g.globalName sig.repr

getCaseRepr :: DataGlobal -> Sig -> Maybe Closure
getCaseRepr g sig = fst <$> M.lookup g.globalName sig.reprCase

getCtorRepr :: CtorGlobal -> Sig -> Maybe Closure
getCtorRepr g sig = fst <$> M.lookup g.globalName sig.repr

getDefRepr :: DefGlobal -> Sig -> Maybe Closure
getDefRepr g sig = fst <$> M.lookup g.globalName sig.repr

getPrimRepr :: PrimGlobal -> Sig -> Maybe Closure
getPrimRepr g sig = fst <$> M.lookup g.globalName sig.repr

getGlobalRepr :: Glob -> Sig -> Maybe Closure
getGlobalRepr (DataGlob g) = getDataRepr g
getGlobalRepr (CtorGlob g) = getCtorRepr g
getGlobalRepr (DefGlob g) = getDefRepr g
getGlobalRepr (PrimGlob g) = getPrimRepr g

dataIsIrrelevant :: DataGlobal -> Sig -> Bool
dataIsIrrelevant g sig =
  let di = getDataGlobal g sig
   in case di.ctors of
        [] -> True
        [c] ->
          let ci = getCtorGlobal c sig
           in ci.qtySum == Zero
        _ -> False

data KnownGlobal a where
  KnownSigma :: KnownGlobal DataGlobal
  KnownPair :: KnownGlobal CtorGlobal
  KnownNat :: KnownGlobal DataGlobal
  KnownZero :: KnownGlobal CtorGlobal
  KnownSucc :: KnownGlobal CtorGlobal
  KnownFin :: KnownGlobal DataGlobal
  KnownBool :: KnownGlobal DataGlobal
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
  KnownTrue :: KnownGlobal CtorGlobal
  KnownFalse :: KnownGlobal CtorGlobal
  KnownJsImpossible :: KnownGlobal PrimGlobal
  KnownJsIndex :: KnownGlobal PrimGlobal
  KnownAdd :: KnownGlobal DefGlobal
  KnownSub :: KnownGlobal DefGlobal
  KnownBind :: KnownGlobal DefGlobal
  KnownRefl :: KnownGlobal CtorGlobal
  KnownEqual :: KnownGlobal DataGlobal
  KnownEmpty :: KnownGlobal DataGlobal
  KnownVoid :: KnownGlobal DefGlobal
  KnownDCongSp :: KnownGlobal DefGlobal
  KnownInj :: CtorGlobal -> KnownGlobal DefGlobal
  KnownConf :: CtorGlobal -> CtorGlobal -> KnownGlobal DefGlobal
  KnownCycle :: DataGlobal -> KnownGlobal DefGlobal
  KnownHEqual :: KnownGlobal DataGlobal

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
knownData KnownBool = DataGlobal (Name "Bool")
knownData KnownEqual = DataGlobal (Name "Equal")
knownData KnownEmpty = DataGlobal (Name "Empty")
knownData KnownHEqual = DataGlobal (Name "HEqual")

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
knownCtor KnownTrue = CtorGlobal (Name "true")
knownCtor KnownFalse = CtorGlobal (Name "false")
knownCtor KnownRefl = CtorGlobal (Name "refl")

knownPrim :: KnownGlobal PrimGlobal -> PrimGlobal
knownPrim KnownJsImpossible = PrimGlobal (Name "js-impossible")
knownPrim KnownJsIndex = PrimGlobal (Name "js-index")

knownDef :: KnownGlobal DefGlobal -> DefGlobal
knownDef KnownSub = DefGlobal (Name "sub")
knownDef KnownAdd = DefGlobal (Name "add")
knownDef KnownBind = DefGlobal (Name "bind")
knownDef KnownVoid = DefGlobal (Name "void")
knownDef KnownDCongSp = DefGlobal (Name "dcong-sp") -- @@Todo: this is a hack
knownDef (KnownInj (CtorGlobal d)) = DefGlobal (Name $ "inj-" ++ d.unName)
knownDef (KnownConf (CtorGlobal d) (CtorGlobal c)) = DefGlobal (Name $ "conf-" ++ d.unName ++ "-" ++ c.unName)
knownDef (KnownCycle (DataGlobal d)) = DefGlobal (Name $ "cycle-" ++ d.unName)
