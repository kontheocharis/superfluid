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
    knownPrim,
    knownDef,
    mapSigContentsM,
    mapSigContentsM_,
    getDefRepr,
    modifyDataItem,
    KnownGlobal (..),
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
import Data.Set (Set)
import qualified Data.Set as S
import Syntax (Closure, STm (..), STy, VTm (..), VTy)

data CtorGlobalInfo = CtorGlobalInfo
  { name :: Name,
    ty :: Closure,
    idx :: Int,
    qtySum :: Qty,
    dataGlobal :: DataGlobal,
    argArity :: Spine ()
  }

data DataGlobalInfo = DataGlobalInfo
  { name :: Name,
    params :: Tel STy,
    fullTy :: VTy,
    ty :: Closure,
    ctors :: [CtorGlobal],
    motiveTy :: Maybe Closure,
    elimTy :: Maybe Closure,
    indexArity :: Spine () -- might not be set yet
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
    ty :: VTm
  }

data GlobalInfo
  = DataInfo DataGlobalInfo
  | CtorInfo CtorGlobalInfo
  | DefInfo DefGlobalInfo
  | PrimInfo PrimGlobalInfo

data Sig = Sig
  { contents :: Map Name GlobalInfo,
    nameOrder :: [Name],
    tags :: Map Name (Set Tag),
    repr :: Map Name (Closure, Set Tag),
    reprCase :: Map Name (Closure, Set Tag)
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

addDataRepr :: DataGlobal -> Closure -> Set Tag -> Sig -> Sig
addDataRepr g t ts s = s {repr = M.insert g.globalName (t, ts) s.repr}

addCaseRepr :: DataGlobal -> Closure -> Set Tag -> Sig -> Sig
addCaseRepr g t ts s = s {reprCase = M.insert g.globalName (t, ts) s.reprCase}

addCtorRepr :: CtorGlobal -> Closure -> Set Tag -> Sig -> Sig
addCtorRepr g t ts s = s {repr = M.insert g.globalName (t, ts) s.repr}

addDefRepr :: DefGlobal -> Closure -> Set Tag -> Sig -> Sig
addDefRepr g t ts s = s {repr = M.insert g.globalName (t, ts) s.repr}

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
  Just _ -> error $ "getCtorGlobal: not a ctor global: " ++ show g
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

knownPrim :: KnownGlobal PrimGlobal -> PrimGlobal
knownPrim KnownJsImpossible = PrimGlobal (Name "js-impossible")
knownPrim KnownJsIndex = PrimGlobal (Name "js-index")

knownDef :: KnownGlobal DefGlobal -> DefGlobal
knownDef KnownSub = DefGlobal (Name "sub")
knownDef KnownAdd = DefGlobal (Name "add")
