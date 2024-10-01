{-# LANGUAGE PatternSynonyms #-}

module Syntax
  ( STm (..),
    STy,
    SPat (..),
    BoundState (..),
    Bounds,
    sAppSpine,
    sLams,
    sPis,
    Case (..),
    sGatherApps,
    sGatherPis,
    sGatherLams,
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
    VNeuHead (..),
    VLazyHead (..),
    VNorm (..),
    WTm (..),
    PRen (..),
    Sub (..),
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
    pattern VHead,
  )
where

import Common
  ( Arg (..),
    Clause,
    CtorGlobal,
    DataGlobal,
    DefGlobal,
    Glob,
    HasNameSupply (uniqueName),
    Idx,
    Lit,
    Lvl (..),
    MetaVar,
    Name,
    Param (..),
    PiMode,
    Spine,
    Tel,
    Times,
    unLvl, PrimGlobal,
  )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Sequence (Seq (..), fromList)

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
    vars :: IntMap Lvl
  }
  deriving (Show)

liftPRen :: PRen -> PRen
liftPRen (PRen dom cod ren) = PRen (Lvl (dom.unLvl + 1)) (Lvl (cod.unLvl + 1)) (IM.insert cod.unLvl dom ren)

liftPRenN :: Int -> PRen -> PRen
liftPRenN 0 ren = ren
liftPRenN n ren = liftPRenN (n - 1) (liftPRen ren)

type VPat = VTm

data VPatB = VPatB {vPat :: VPat, binds :: [Name]} deriving (Show)

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

type VCtor = VSpined (CtorGlobal, [VTm])

data VNeuHead
  = VFlex MetaVar
  | VRigid Lvl
  | VBlockedCase (Case VNeu VTm VPatB Closure)
  | VReprFlex MetaVar
  | VReprRigid Lvl
  | VPrim PrimGlobal
  deriving (Show)

data VLazyHead
  = VDef DefGlobal
  | VLit (Lit VTm)
  | VLazyCase (Case VLazy VTm VPatB Closure)
  | VReprLazyCase Int (Case VLazy VTm VPatB Closure)
  | VReprBlockedCase Int (Case VNeu VTm VPatB Closure)
  | VReprDef Int DefGlobal
  | VReprCtor Int (CtorGlobal, [VTm])
  | VReprData Int DataGlobal
  deriving (Show)

data VNorm
  = VPi PiMode Name VTy Closure
  | VLam PiMode Name Closure
  | VData VData
  | VCtor VCtor
  | VUnrepr Closure
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

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = (VFlex m, Empty)

pattern VHead :: t -> VSpined t
pattern VHead m = (m, Empty)

type STy = STm

data SPat = SPat {asTm :: STm, binds :: [Name]} deriving (Show)

data BoundState = Bound | Defined deriving (Eq, Show)

type Bounds = [BoundState]

data STm
  = SPi PiMode Name STm STm
  | SLam PiMode Name STm
  | SLet Name STy STm STm
  | SMeta MetaVar Bounds
  | SApp PiMode STm STm
  | SCase SCase
  | SU
  | SGlobal Glob [STm]
  | SVar Idx
  | SLit (Lit STm)
  | SRepr Times STm
  deriving (Show)

-- @@Todo: case and constructor params should be (Lvl, [VTm]) instead.
-- Otherwise we are doing lots of unnecessary work.

sAppSpine :: STm -> Spine STm -> STm
sAppSpine t Empty = t
sAppSpine t (Arg m u :<| sp) = sAppSpine (SApp m t u) sp

uniqueSLams :: (HasNameSupply m) => [PiMode] -> STm -> m STm
uniqueSLams ms t = do
  sp <- fromList <$> mapM (\m -> Arg m <$> uniqueName) ms
  return $ sLams sp t

sLams :: Spine Name -> STm -> STm
sLams Empty t = t
sLams (Arg m x :<| sp) t = SLam m x (sLams sp t)

sGatherApps :: STm -> (STm, Spine STm)
sGatherApps (SApp m t u) = let (t', sp) = sGatherApps t in (t', sp :|> Arg m u)
sGatherApps t = (t, Empty)

sPis :: Tel STm -> STm -> STm
sPis Empty b = b
sPis (Param m n a :<| xs) b = SPi m n a (sPis xs b)

sGatherPis :: STm -> (Tel STm, STm)
sGatherPis = \case
  SPi m n a b -> let (xs, b') = sGatherPis b in (Param m n a :<| xs, b')
  t -> (Empty, t)

sGatherLams :: STm -> (Spine Name, STm)
sGatherLams = \case
  SLam m n t -> let (ns, b) = sGatherLams t in (Arg m n :<| ns, b)
  t -> (Empty, t)

sGatherLets :: STm -> ([(Name, STy, STm)], STm)
sGatherLets = \case
  SLet n ty t u -> let (binds, ret) = sGatherLets u in ((n, ty, t) : binds, ret)
  t -> ([], t)
