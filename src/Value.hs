{-# LANGUAGE PatternSynonyms #-}

module Value
  ( Sub,
    VPat,
    VPatB (..),
    VTy,
    Env,
    Closure (..),
    VHead (..),
    VNeu (..),
    VTm (..),
    pattern VVar,
    pattern VMeta,
    pattern VHead,
    pattern VRepr,
  )
where

import Common (Clause, Glob, Lit, Lvl, MetaVar, Name, PiMode, Spine, Times)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Sequence (Seq (Empty))
import Syntax (STm)

newtype Sub = Sub {vars :: IntMap VTm}

instance Semigroup Sub where
  Sub v1 <> Sub v2 = Sub (IM.union v1 v2)

instance Monoid Sub where
  mempty = Sub IM.empty

type VPat = VTm

data VPatB = VPatB {pat :: VPat, numBinds :: Int}

type VTy = VTm

type Env v = [v]

data Closure = Closure {numVars :: Int, env :: Env VTm, body :: STm}

data VHead = VFlex MetaVar | VRigid Lvl deriving (Eq)

data VNeu
  = VApp VHead (Spine VTm)
  | VCase VNeu [Clause VPatB Closure]
  | VReprApp Times VHead (Spine VTm)

data VTm
  = VPi PiMode Name VTy Closure
  | VLam PiMode Name Closure
  | VU
  | VGlobal Glob (Spine VTm)
  | VLit (Lit ())
  | VNeu VNeu

pattern VVar :: Lvl -> VNeu
pattern VVar l = VApp (VRigid l) Empty

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = VApp (VFlex m) Empty

pattern VHead :: VHead -> VNeu
pattern VHead m = VApp m Empty

pattern VRepr :: Times -> VHead -> VNeu
pattern VRepr m t = VReprApp m t Empty
