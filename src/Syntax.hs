{-# LANGUAGE PatternSynonyms #-}

module Syntax
  ( STm (..),
    STy,
    VHead (..),
    SPat (..),
    BoundState (..),
    Bounds,
    sAppSpine,
    sLams,
    sPis,
    Case (..),
    VData,
    sGatherApps,
    sGatherPis,
    sGatherLams,
    sGlobWithParams,
    uniqueSLams,
    sGatherLets,
    VPat,
    VPatB (..),
    VTy,
    Env,
    Closure (..),
    VNeu,
    VTm (..),
    VLazy,
    mapHeadM,
    vGatherApps,
    headAsValue,
    sReprTimes,
    VNeuHead (..),
    VLazyHead (..),
    VNorm (..),
    WTm (..),
    PRen (..),
    Sub (..),
    VLazyCase,
    VBlockedCase,
    SCase,
    mapClosureM,
    weakAsValue,
    subbing,
    liftPRen,
    liftPRenN,
    isEmptySub,
    vGetSpine,
    pattern VVar,
    pattern VMeta,
    pattern VV,
  )
where

import Common
  ( Arg (..),
    Clause,
    CtorGlobal,
    DataGlobal,
    DefGlobal,
    Glob (..),
    Idx,
    Lit,
    Lvl (..),
    MetaVar,
    Name,
    Param (..),
    PiMode,
    PrimGlobal,
    Spine,
    Tel,
    unLvl, Qty,
  )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Sequence (Seq (..), fromList)
import Interfaces.General (HasNameSupply (uniqueName))

data Sub = Sub {lvl :: Lvl, vars :: IntMap (NonEmpty VTm)} deriving (Show)

isEmptySub :: Sub -> Bool
isEmptySub s = IM.null s.vars

emptySub :: Sub
emptySub = Sub (Lvl 0) IM.empty

subbing :: Lvl -> Lvl -> VTm -> Sub
subbing l x v = Sub l (IM.singleton x.unLvl (NE.singleton v))

instance Semigroup Sub where
  Sub l1 v1 <> Sub l2 v2 = Sub (max l1 l2) (IM.unionWith (<>) v1 v2)

instance Monoid Sub where
  mempty = emptySub

data PRen = PRen
  { domSize :: Lvl,
    codSize :: Lvl,
    vars :: IntMap (Lvl, Qty)
  }
  deriving (Show)

liftPRen :: Qty -> PRen -> PRen
liftPRen q (PRen dom cod ren) = PRen (Lvl (dom.unLvl + 1)) (Lvl (cod.unLvl + 1)) (IM.insert cod.unLvl (dom, q) ren)

liftPRenN :: [Qty] -> PRen -> PRen
liftPRenN qs ren = foldl (flip liftPRen) ren qs

type VPat = VTm

data VPatB = VPatB {vPat :: VPat, binds :: [(Qty, Name)]} deriving (Show)

type VTy = VTm

type Env v = [v]

data Closure = Closure {numVars :: Int, env :: Env VTm, body :: STm} deriving (Show)

mapClosureM :: (Monad m) => (STm -> m STm) -> Closure -> m Closure
mapClosureM f (Closure n env t) = Closure n env <$> f t

data Case s t p c = Case
  { dat :: DataGlobal,
    datParams :: Spine t,
    subject :: s,
    subjectIndices :: Spine t,
    elimTy :: t,
    clauses :: [Clause p c]
  }
  deriving (Show)

type SCase = Case STm STm SPat STm

type VSpined t = (t, Spine VTm)

type VNeu = VSpined VNeuHead

type VLazy = VSpined VLazyHead

type VData = VSpined DataGlobal

type VCtor = VSpined (CtorGlobal, Spine VTm)

type VLazyCase = Case VLazy VTm VPatB Closure

type VBlockedCase = Case VNeu VTm VPatB Closure

data VNeuHead
  = VFlex MetaVar
  | VRigid Lvl
  | VBlockedCase VBlockedCase
  | VPrim PrimGlobal
  | VUnrepr VHead
  deriving (Show)


data VLazyHead
  = VDef DefGlobal
  | VLit (Lit VTm)
  | VLazyCase VLazyCase
  | VLet Qty Name VTy VTm Closure
  | VRepr VHead
  deriving (Show)

data VHead
  = VNeuHead VNeuHead
  | VLazyHead VLazyHead
  | VDataHead DataGlobal
  | VCtorHead (CtorGlobal, Spine VTm)
  deriving (Show)


mapHeadM :: (Monad m) => (VTm -> m VTm) -> VHead -> m VHead
mapHeadM f h = do
  h' <- f (headAsValue h)
  case vGatherApps h' of
    Just (h'', Empty) -> return h''
    _ -> error "mapHeadM: got non-head value"

vGatherApps :: VTm -> Maybe (VSpined VHead)
vGatherApps (VNorm (VCtor (c, sp))) = Just (VCtorHead c, sp)
vGatherApps (VNorm (VData (d, sp))) = Just (VDataHead d, sp)
vGatherApps (VNeu (h, sp)) = Just (VNeuHead h, sp)
vGatherApps (VLazy (h, sp)) = Just (VLazyHead h, sp)
vGatherApps _ = Nothing

headAsValue :: VHead -> VTm
headAsValue (VNeuHead h) = VNeu (h, Empty)
headAsValue (VLazyHead h) = VLazy (h, Empty)
headAsValue (VDataHead d) = VNorm (VData (d, Empty))
headAsValue (VCtorHead c) = VNorm (VCtor (c, Empty))

data VNorm
  = VPi PiMode Qty Name VTy Closure
  | VLam PiMode Qty Name Closure
  | VData VData
  | VCtor VCtor
  | VU
  deriving (Show)

data VTm
  = VNorm VNorm
  | VLazy VLazy
  | VNeu VNeu
  deriving (Show)

data WTm
  = WNorm VNorm
  | WNeu VNeu
  deriving (Show)

weakAsValue :: WTm -> VTm
weakAsValue (WNorm n) = VNorm n
weakAsValue (WNeu n) = VNeu n

vGetSpine :: VTm -> Spine VTm
vGetSpine (VNorm (VData (_, sp))) = sp
vGetSpine (VNorm (VCtor (_, sp))) = sp
vGetSpine (VNeu (_, sp)) = sp
vGetSpine (VLazy (_, sp)) = sp
vGetSpine _ = Empty

pattern VVar :: Lvl -> VNeu
pattern VVar l = (VRigid l, Empty)

pattern VV :: Lvl -> VTm
pattern VV l = VNeu (VRigid l, Empty)

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = (VFlex m, Empty)

type STy = STm

data SPat = SPat {asTm :: STm, binds :: [(Qty, Name)]} deriving (Show)

data BoundState = Bound Qty | Defined deriving (Eq, Show)

type Bounds = [BoundState]

data STm
  = SPi PiMode Qty Name STm STm
  | SLam PiMode Qty Name STm
  | SLet Qty Name STy STm STm
  | SMeta MetaVar Bounds
  | SApp PiMode Qty STm STm
  | SCase SCase
  | SU
  | SData DataGlobal
  | SCtor (CtorGlobal, Spine STm)
  | SDef DefGlobal
  | SPrim PrimGlobal
  | SVar Idx
  | SLit (Lit STm)
  | SRepr STm
  | SUnrepr STm
  deriving (Show)

sReprTimes :: Int -> STm -> STm
sReprTimes 0 t = t
sReprTimes n t | n > 0 = SRepr (sReprTimes (n - 1) t)
               | otherwise = SUnrepr (sReprTimes (n + 1) t)

-- @@Todo: case and constructor params should be (Lvl, [VTm]) instead.
-- Otherwise we are doing lots of unnecessary work.

sAppSpine :: STm -> Spine STm -> STm
sAppSpine t Empty = t
sAppSpine t (Arg m q u :<| sp) = sAppSpine (SApp m q t u) sp

uniqueSLams :: (HasNameSupply m) => [(PiMode, Qty)] -> STm -> m STm
uniqueSLams ms t = do
  sp <- fromList <$> mapM (\(m, q) -> Param m q <$> uniqueName <*> return ()) ms
  return $ sLams sp t

sLams :: Tel a -> STm -> STm
sLams Empty t = t
sLams (Param m q x _ :<| sp) t = SLam m q x (sLams sp t)

sGatherApps :: STm -> (STm, Spine STm)
sGatherApps (SApp m q t u) = let (t', sp) = sGatherApps t in (t', sp :|> Arg m q u)
sGatherApps t = (t, Empty)

sPis :: Tel STm -> STm -> STm
sPis Empty b = b
sPis (Param q m n a :<| xs) b = SPi q m n a (sPis xs b)

sGatherPis :: STm -> (Tel STm, STm)
sGatherPis = \case
  SPi m q n a b -> let (xs, b') = sGatherPis b in (Param m q n a :<| xs, b')
  t -> (Empty, t)

sGatherLams :: STm -> (Tel (), STm)
sGatherLams = \case
  SLam m q n t -> let (ns, b) = sGatherLams t in (Param m q n () :<| ns, b)
  t -> (Empty, t)

sGatherLets :: STm -> ([(Qty, Name, STy, STm)], STm)
sGatherLets = \case
  SLet q n ty t u -> let (binds, ret) = sGatherLets u in ((q, n, ty, t) : binds, ret)
  t -> ([], t)

sGlobWithParams :: Glob -> Spine STm -> STm
sGlobWithParams (DataGlob d) _ = SData d
sGlobWithParams (CtorGlob c) xs = SCtor (c, xs)
sGlobWithParams (DefGlob d) _ = SDef d
sGlobWithParams (PrimGlob p) _ = SPrim p
