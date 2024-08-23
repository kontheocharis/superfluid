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
    pattern VVar,
    pattern VMeta,
    pattern VHead,
    pattern VRepr,
    pattern VGl,
    pattern VGlob,
    pattern VCase,
  )
where

import Common (Arg (..), Clause, DataGlobal, Glob, HasNameSupply (..), Lit, Lvl (..), MetaVar, Name, PiMode, Spine, Times, WithNames (..), nextLvl, unLvl)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Sequence (Seq (..), fromList)
import Printing (Pretty (..))
import Syntax (STm, sLams)

data Sub = Sub {lvl :: Lvl, vars :: IntMap VTm} deriving (Show)

isEmptySub :: Sub -> Bool
isEmptySub s = IM.null s.vars

emptySub :: Sub
emptySub = Sub (Lvl 0) IM.empty

subbing :: Lvl -> Lvl -> VTm -> Sub
subbing l x v = Sub l (IM.singleton x.unLvl v)

instance Semigroup Sub where
  Sub l1 v1 <> Sub l2 v2
    | l1 > l2 = Sub l1 (IM.union v1 v2)
    | otherwise = Sub l2 (IM.union v1 v2)

instance Monoid Sub where
  mempty = emptySub

data PRen = PRen
  { domSize :: Lvl,
    codSize :: Lvl,
    vars :: IntMap Lvl
  }

liftPRen :: PRen -> PRen
liftPRen = liftPRenN 1

liftPRenN :: Int -> PRen -> PRen
liftPRenN n (PRen dom cod ren) = PRen (Lvl (dom.unLvl + n)) (Lvl (cod.unLvl + n)) (IM.map (\c -> Lvl (c.unLvl + n)) ren)

type VPat = VTm

data VPatB = VPatB {vPat :: VPat, binds :: [Name]} deriving (Show)

type VTy = VTm

type Env v = [v]

data Closure = Closure {numVars :: Int, env :: Env VTm, body :: STm} deriving (Show)

data VHead = VFlex MetaVar | VRigid Lvl | VGlobal Glob deriving (Show, Eq)

data VNeu
  = VApp VHead (Spine VTm)
  | VCaseApp DataGlobal VNeu [Clause VPatB Closure] (Spine VTm)
  | VReprApp Times VHead (Spine VTm)
  deriving (Show)

data VTm
  = VPi PiMode Name VTy Closure
  | VLam PiMode Name Closure
  | VU
  | VLit (Lit VTm)
  | VNeu VNeu
  deriving (Show)

pattern VVar :: Lvl -> VNeu
pattern VVar l = VApp (VRigid l) Empty

pattern VCase :: DataGlobal -> VNeu -> [Clause VPatB Closure] -> VNeu
pattern VCase dat m cls = VCaseApp dat m cls Empty

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = VApp (VFlex m) Empty

pattern VHead :: VHead -> VNeu
pattern VHead m = VApp m Empty

pattern VRepr :: Times -> VHead -> VNeu
pattern VRepr m t = VReprApp m t Empty

pattern VGl :: Glob -> VTm
pattern VGl g = VNeu (VHead (VGlobal g))

pattern VGlob :: Glob -> Spine VTm -> VTm
pattern VGlob g sp = VNeu (VApp (VGlobal g) sp)
