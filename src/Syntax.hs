module Syntax
  ( STm (..),
    STy,
    SPat (..),
    BoundState (..),
    Bounds,
    toPSpine,
    sAppSpine,
    sLams,
    uniqueSLams,
  )
where

import Common
  ( Arg (..),
    Clause,
    DataGlobal,
    Glob,
    HasNameSupply (uniqueName),
    Idx,
    Lit,
    MetaVar,
    Name,
    PiMode,
    Spine,
    Times,
  )
import Data.Sequence (Seq (..), fromList)
import Presyntax (PTm (..))

type STy = STm

data SPat = SPat { asTm :: STm, binds :: [Name] } deriving (Show)

data BoundState = Bound | Defined deriving (Eq, Show)

type Bounds = [BoundState]

data STm
  = SPi PiMode Name STm STm
  | SLam PiMode Name STm
  | SLet Name STy STm STm
  | SMeta MetaVar Bounds
  | SApp PiMode STm STm
  | SCase DataGlobal STm [Clause SPat STm]
  | SU
  | SGlobal Glob
  | SVar Idx
  | SLit (Lit STm)
  | SRepr Times STm
  deriving (Show)

toPSpine :: PTm -> (PTm, Spine PTm)
toPSpine (PApp m t u) = let (t', sp) = toPSpine t in (t', sp :|> Arg m u)
toPSpine t = (t, Empty)

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



