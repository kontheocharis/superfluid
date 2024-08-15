module Syntax
  ( STm (..),
    STy,
    SPat,
    numBinds,
    toPSpine,
    sAppSpine,
  )
where

import Common
  ( Arg (..),
    Clause,
    Idx,
    Lit,
    MetaVar,
    Name,
    PiMode,
    Spine,
    Times,
  )
import Data.Sequence (Seq (..))
import Presyntax (PTm (..))
import Globals (Glob)

type STy = STm

type SPat = STm

data STm
  = SPi PiMode Name STm STm
  | SLam PiMode Name STm
  | SLet Name STy STm STm
  | SMeta MetaVar
  | SApp PiMode STm STm
  | SCase STm [Clause SPat STm]
  | SU
  | SGlobal Glob
  | SVar Idx
  | SLit (Lit ())
  | SRepr Times STm

numBinds :: SPat -> Int
numBinds (SVar _) = 1
numBinds (SGlobal _) = 0
numBinds (SLit _) = 0
numBinds (SApp _ t u) = numBinds t + numBinds u
numBinds _ = error "impossible"

toPSpine :: PTm -> (PTm, Spine PTm)
toPSpine (PApp m t u) = let (t', sp) = toPSpine t in (t', sp :|> Arg m u)
toPSpine t = (t, Empty)

sAppSpine :: STm -> Spine STm -> STm
sAppSpine t Empty = t
sAppSpine t (Arg m u :<| sp) = sAppSpine (SApp m t u) sp
