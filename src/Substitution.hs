{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Substitution
  ( Sub,
    subbing,
    idSub,
    proj,
    compose,
    emptySub,
    liftSub,
    nonEmptyDom,
    BiSub (..),
  )
where

import Common (Lvl (..), nextLvl)
import Data.Sequence (Seq (..))
import Evaluation (Eval)
import Syntax (HTm (HVar), VTm (..))

-- Substitution

data Sub = Sub {domLvl :: Lvl, mapping :: Seq HTm -> Seq HTm}

data BiSub = BiSub {forward :: Sub, backward :: Sub}

nonEmptyDom :: (Seq HTm -> HTm -> a) -> (Seq HTm -> a)
nonEmptyDom f = \case
  Empty -> error "Empty domain"
  s :|> x -> f s x

-- ε : Sub Γ •
emptySub :: Lvl -> Sub
emptySub dom = Sub dom (const Empty)

-- _,_ : (σ : Sub Γ Δ) -> Tm Γ (Α σ) -> Sub Γ (Δ, Α)
subbing :: Sub -> (Seq HTm -> HTm) -> Sub
subbing s v = Sub s.domLvl (\g -> s.mapping g :|> v g)

-- id : Sub Γ Γ
idSub :: Lvl -> Sub
idSub dom = Sub dom id

-- _◦_ : (σ : Sub Γ Δ) -> (τ : Sub Δ Θ) -> Sub Γ Θ
compose :: Sub -> Sub -> Sub
compose s1 s2 = Sub s1.domLvl $ \sp -> s2.mapping (s1.mapping sp)

-- lift : Sub Γ Δ -> Sub (Γ, Α) (Δ, Α)
liftSub :: Sub -> Sub
liftSub s = Sub (nextLvl s.domLvl) $ nonEmptyDom (\sp t -> s.mapping sp :|> t)

-- π : Sub Γ (Δ , A) -> Sub Γ Δ
proj :: Sub -> Sub
proj s = Sub s.domLvl $ \sp -> case s.mapping sp of
  Empty -> error "Cannot project from empty substitution"
  s' :|> _ -> s'

-- _[_] : Sub Γ Δ -> Tm Γ A -> Tm Δ A
sub :: (Eval m) => Sub -> VTm -> m VTm
sub s v = undefined
