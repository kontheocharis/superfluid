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
    pattern VCase,
  )
where

import Common (Arg (..), Clause, DataGlobal, Glob, HasNameSupply (..), Lit, Lvl (..), MetaVar, Name, PiMode, Spine, Times, nextLvl, unLvl, WithNames (..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Sequence (Seq (..), fromList)
import Syntax (STm, sLams)
import Printing (Pretty (..))

newtype Sub = Sub {vars :: IntMap VTm}

isEmptySub :: Sub -> Bool
isEmptySub s = IM.null s.vars

emptySub :: Sub
emptySub = Sub IM.empty

subbing :: Lvl -> VTm -> Sub
subbing l v = Sub (IM.singleton l.unLvl v)

instance Semigroup Sub where
  Sub v1 <> Sub v2 = Sub (IM.union v1 v2)

data PRen = PRen
  { domSize :: Lvl,
    codSize :: Lvl,
    vars :: IntMap Lvl
  }

liftPRen :: PRen -> PRen
liftPRen = liftPRenN 1

liftPRenN :: Int -> PRen -> PRen
liftPRenN n (PRen dom cod ren) = PRen (Lvl (dom.unLvl + n)) (Lvl (cod.unLvl + n)) (IM.map (\c -> Lvl (c.unLvl + n)) ren)

instance Monoid Sub where
  mempty = emptySub

type VPat = VTm

data VPatB = VPatB {vPat :: VPat, binds :: [Name]}

type VTy = VTm

type Env v = [v]

data Closure = Closure {numVars :: Int, env :: Env VTm, body :: STm}

data VHead = VFlex MetaVar | VRigid Lvl deriving (Eq)

data VNeu
  = VApp VHead (Spine VTm)
  | VCaseApp DataGlobal VNeu [Clause VPatB Closure] (Spine VTm)
  | VReprApp Times VHead (Spine VTm)

data VTm
  = VPi PiMode Name VTy Closure
  | VLam PiMode Name Closure
  | VU
  | VGlobal Glob (Spine VTm)
  | VLit (Lit VTm)
  | VNeu VNeu

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
pattern VGl g = VGlobal g Empty
