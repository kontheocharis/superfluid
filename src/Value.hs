{-# LANGUAGE PatternSynonyms #-}

module Value
  ( VPat,
    VPatB (..),
    VTy,
    Env,
    Closure (..),
    VHead (..),
    VNeu (..),
    VTm (..),
    PRen (..),
    Sub (..),
    subbing,
    liftPRen,
    liftPRenN,
    isEmptySub,
    vGetSpine,
    pattern VVar,
    pattern VMeta,
    pattern VHead,
    pattern VRepr,
    pattern VGl,
    pattern VGlob,
    pattern VCase,
  )
where

import Common
  ( Clause,
    DataGlobal,
    Glob,
    Lit,
    Lvl (..),
    MetaVar,
    Name,
    PiMode,
    Spine,
    Times,
    unLvl,
  )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Sequence (Seq (..))
import Syntax (STm)

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

data VHead = VFlex MetaVar | VRigid Lvl | VGlobal Glob deriving (Show, Eq)

data VNeu
  = VApp VHead (Spine VTm)
  | VCaseApp DataGlobal VNeu VTm [Clause VPatB Closure] (Spine VTm)
  | VReprApp Times VNeu (Spine VTm)
  deriving (Show)

data VTm
  = VPi PiMode Name VTy Closure
  | VLam PiMode Name Closure
  | VU
  | VLit (Lit VTm)
  | VNeu VNeu
  deriving (Show)

vGetSpine :: VTm -> Spine VTm
vGetSpine (VNeu (VApp _ sp)) = sp
vGetSpine (VNeu (VCaseApp _ _ _ _ sp)) = sp
vGetSpine (VNeu (VReprApp _ _ sp)) = sp
vGetSpine _ = Empty

pattern VVar :: Lvl -> VNeu
pattern VVar l = VApp (VRigid l) Empty

pattern VCase :: DataGlobal -> VNeu -> VTm -> [Clause VPatB Closure] -> VNeu
pattern VCase dat m r cls = VCaseApp dat m r cls Empty

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = VApp (VFlex m) Empty

pattern VHead :: VHead -> VNeu
pattern VHead m = VApp m Empty

pattern VRepr :: Times -> VNeu -> VNeu
pattern VRepr m t = VReprApp m t Empty

pattern VGl :: Glob -> VTm
pattern VGl g = VNeu (VHead (VGlobal g))

pattern VGlob :: Glob -> Spine VTm -> VTm
pattern VGlob g sp = VNeu (VApp (VGlobal g) sp)
