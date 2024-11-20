{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Substitution (Sub, isEmptySub, subbing, idSub, proj, compose, emptySub, liftSub) where

import Common (Lvl (..), members, nextLvl)
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Sequence (Seq (..), fromList)
import Evaluation (Eval, eval, quote)
import Printing (Pretty (..))
import Syntax (VTm (..), pattern VV)

data Sub = Sub {domLvl :: Lvl, tms :: Seq VTm} deriving (Show)

isEmptySub :: Sub -> Bool
isEmptySub s = null s.tms

-- ε : Sub Γ •
emptySub :: Lvl -> Sub
emptySub dom = Sub dom Empty

-- _,_ : (σ : Sub Γ Δ) -> Tm Γ (Α σ) -> Sub Γ (Δ, Α)
subbing :: Sub -> VTm -> Sub
subbing s v = Sub s.domLvl (s.tms :|> v)

-- id : Sub Γ Γ
idSub :: Lvl -> Sub
idSub dom = Sub dom (fromList . map VV $ members dom)

-- _◦_ : (σ : Sub Γ Δ) -> (τ : Sub Δ Θ) -> Sub Γ Θ
compose :: (Eval m) => Sub -> Sub -> m Sub
compose s1 s2 = do
  s' <- traverse (sub s1) s2.tms
  return $ Sub s1.domLvl s'

-- ^ _ : Sub Γ Δ -> Sub (Γ, Α) (Δ, Α)
liftSub :: Sub -> Sub
liftSub s = Sub (nextLvl s.domLvl) (s.tms :|> VV (Lvl (length s.tms)))

-- π : Sub Γ (Δ , A) -> Sub Γ Δ
proj :: Sub -> Sub
proj s = case s.tms of
  Empty -> error "Cannot project from empty substitution"
  s' :|> _ -> Sub s.domLvl s'

instance (Monad m, Pretty m VTm) => Pretty m Sub where
  pretty s = do
    tms' <- traverse pretty s.tms
    return $ intercalate ", " (toList tms')

-- _[_] : Sub Γ Δ -> Tm Γ A -> Tm Δ A
sub :: (Eval m) => Sub -> VTm -> m VTm
sub s v = do
  t <- quote s.domLvl v
  eval (reverse $ toList s.tms) t
