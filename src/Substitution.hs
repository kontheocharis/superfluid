{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Substitution
  ( Sub,
    subbing,
    idSub,
    Subst (..),
    composeSub,
    emptySub,
    liftSub,
    nonEmptyDom,
    BiSub (..),
    liftSubN,
  )
where

import Common (Lvl (..), nextLvl, nextLvls, Spine)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation (Eval)
import Syntax (HTm (HVar), VTm (..))

-- Substitution

data Sub = Sub {domLvl :: Lvl, codLvl :: Lvl, mapping :: Seq HTm -> Seq HTm}

data BiSub = BiSub {forward :: Sub, backward :: Sub}

nonEmptyDom :: (Seq HTm -> HTm -> a) -> (Seq HTm -> a)
nonEmptyDom f = \case
  Empty -> error "Empty domain"
  s :|> x -> f s x

-- ε : Sub Γ •
emptySub :: Lvl -> Sub
emptySub dom = Sub dom (Lvl 0) (const Empty)

-- _,_ : (σ : Sub Γ Δ) -> Tm Γ (Α σ) -> Sub Γ (Δ, Α)
subbing :: Sub -> (Seq HTm -> HTm) -> Sub
subbing s v = Sub s.domLvl (nextLvl s.codLvl) (\g -> s.mapping g :|> v g)

-- id : Sub Γ Γ
idSub :: Lvl -> Sub
idSub dom = Sub dom dom id

-- _◦_ : (σ : Sub Γ Δ) -> (τ : Sub Δ Θ) -> Sub Γ Θ
composeSub :: Sub -> Sub -> Sub
composeSub s1 s2 = Sub s1.domLvl s2.codLvl $ \sp -> s2.mapping (s1.mapping sp)

-- lift : (σ : Sub Γ Δ) -> Sub (Γ, Α σ) (Δ, Α)
liftSub :: Sub -> Sub
liftSub s = Sub (nextLvl s.domLvl) (nextLvl s.codLvl) $ nonEmptyDom (\sp t -> s.mapping sp :|> t)

-- liftN : (σ : Sub Γ Δ) -> Sub (Γ ++ Α σ) (Δ ++ Α)
liftSubN :: Int -> Sub -> Sub
liftSubN n s =
  Sub
    (nextLvls s.domLvl n)
    (nextLvls s.codLvl n)
    ( \sp ->
        let beginning = s.domLvl.unLvl - n
         in s.mapping (S.take beginning sp) <> S.drop beginning sp
    )

-- π : Sub Γ (Δ , A) -> Sub Γ Δ
-- proj :: Sub -> Sub
-- proj s = Sub s.domLvl $ \sp -> case s.mapping sp of
--   Empty -> error "Cannot project from empty substitution"
--   s' :|> _ -> s'

-- _[_] : Sub Γ Δ -> Tm Γ A -> Tm Δ A

class Subst a where
  sub :: (Eval m) => Sub -> a -> m a

instance (Subst VTm) where

instance (Subst t) => (Subst (Spine t)) where
-- sub :: (Eval m) => Sub -> VTm -> m VTm
-- sub s v = undefined
