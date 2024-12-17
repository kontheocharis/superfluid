{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
module SyntaxIndexed () where

import Common (Name (..), PiMode (Explicit), Qty (One), MetaVar, DataGlobal, Spine, DefGlobal, Lit)
import Data.Sequence (Seq, Seq (..))
import Data.Kind (Type)
import Data.Singletons (Sing (..), SingI (sing))

data Con = Empty | Con :> Name


data Size :: Con -> Type where
  SZ :: Size ns
  SS :: Size ns -> Size ns

data Idx :: Con -> Type where
  IZ :: Idx (ns :> n)
  IS :: Idx c -> Idx (ns :> n)

data Lvl :: Con -> Type where
  LZ :: Lvl (ns :> n)
  LS :: Lvl ns -> Lvl (ns :> n)

type STy = STm

data SCase :: Con -> Type where

data STm :: Con -> Type where
  SPi :: PiMode -> Qty -> Sing n -> STy ns -> STy (ns :> n) -> STy ns
  SLam :: PiMode -> Qty -> Sing n -> STm (ns :> n) -> STm ns
  SLet :: Qty -> Sing n -> STy ns -> STm ns -> STm (ns :> n) -> STm ns
  SMeta :: MetaVar -> STy ns
  SApp :: STm ns -> STm ns -> STm ns
  SCase :: SCase ns -> STm ns
  SU :: STy ns -> STm ns
  SData :: DataGlobal -> Spine (STm ns) -> Spine (STm ns) -> STm ns
  SCtor :: DataGlobal -> Spine (STm ns) -> Spine (STm ns) -> STm ns
  SDef :: DefGlobal -> Spine (STm ns) -> STm ns
  SPrim :: DefGlobal -> Spine (STm ns) -> STm ns
  SVar :: Idx ns -> STm ns
  SLit :: Lit (STm ns) -> STm ns
  SRepr :: STm ns -> STm ns
  SUnrepr :: STm ns -> STm ns


identity :: STm ns
identity = SLam Explicit One (sing . Sing $ Name "foo") (SVar IZ)
