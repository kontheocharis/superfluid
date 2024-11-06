{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
module Interfaces.Tc (Tc(..)) where
import Interfaces.General (Has)
import Data.Kind (Type)
import Syntax (STm, VTy)
import Common (PiMode, Name)


-- class
--   ( Eval m,
--     Unelab m,
--     Has m Loc,
--     Try m,
--     Has m Qty,
--     Has m (Seq Problem),
--     Has m InPat,
--     Has m Ctx,
--     Has m SolveAttempts
--   ) =>
--   Tc m


data Mode = Check | Infer

-- type Child m md = (Mode -> m (STm, VTy))

data InMode :: Mode -> Type where
  InCheck :: InMode Check
  InInfer :: InMode Infer

data Typechecker m :: Mode -> Type where
  TcCheck :: (VTy -> m STm) -> Typechecker m Check
  TcInfer :: (m (STm, VTy)) -> Typechecker m Infer

class Tc where
  lam :: InMode md -> PiMode -> Name -> Typechecker m md -> Typechecker m md
  lam (InCheck) m x (TcCheck f) = undefined
  lam (InInfer) m x (TcInfer f) = undefined


