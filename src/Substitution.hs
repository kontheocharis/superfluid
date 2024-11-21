{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Substitution
  ( Sub (..),
    extendSub,
    idSub,
    Subst (..),
    composeSub,
    liftSub,
    nonEmptyDom,
    BiSub (..),
    Shapes,
    liftSubN,
    projN,
    proj,
    Shape,
    mapSub1,
    mapSubN,
    replaceSub,
    nonEmptyDomL,
    terminalSub,
  )
where

import Common (Arg (..), Clause (..), Lvl (..), Name (..), Param (..), PiMode (..), Qty (..), Spine, Tel, members, nextLvl, nextLvls, telShapes, telToBinds)
import Context (Ctx)
import Data.Foldable (toList)
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..), fromList)
import qualified Data.Sequence as S
import Evaluation (Eval)
import Syntax (Case (..), Env, HCtx, HTm (..), HTy, SPat (..), VTm (..))

-- Substitution

type Shapes = Tel ()

type Shape = Param ()

data Sub = Sub {domSh :: Shapes, codSh :: Shapes, mapping :: Spine HTm -> Spine HTm}

data BiSub = BiSub {forward :: Sub, backward :: Sub}

nonEmptyDom :: (Spine HTm -> HTm -> a) -> (Spine HTm -> a)
nonEmptyDom f = \case
  Empty -> error "Empty domain"
  s :|> Arg _ _ x -> f s x

nonEmptyDomL :: (HTm -> Spine HTm -> a) -> (Spine HTm -> a)
nonEmptyDomL f = \case
  Empty -> error "Empty domain"
  Arg _ _ x :<| s -> f x s

-- Basically allows us to split the domain of a substitution into two parts
-- if we know that the domain is greater than l
domGt :: Int -> (Spine HTm -> Spine HTm -> a) -> (Spine HTm -> a)
domGt l f x = case S.splitAt l x of
  (_, Empty) -> error "Domain too small"
  (xs, ys) -> f xs ys

mapSub1 :: Shapes -> Shapes -> (Spine HTm -> HTm -> Spine HTm) -> Sub
mapSub1 dom cod f = Sub dom cod $ nonEmptyDom f

mapSubN :: Shapes -> Shapes -> Shapes -> (Spine HTm -> Spine HTm -> Spine HTm) -> Sub
mapSubN dom cod n f = Sub dom cod $ domGt (length n) f

-- ε : Sub Γ •
terminalSub :: Shapes -> Sub
terminalSub dom = Sub dom Empty (const Empty)

-- _,_ : (σ : Sub Γ Δ) -> Tm Γ (Α σ) -> Sub Γ (Δ, Α)
extendSub :: Sub -> Shape -> (Spine HTm -> HTm) -> Sub
extendSub s sh v = Sub s.domSh (s.codSh :|> sh) (\g -> let Param m q _ () = sh in s.mapping g :|> (v g <$ Arg m q ()))

-- id : Sub Γ Γ
idSub :: Shapes -> Sub
idSub dom = Sub dom dom id

-- _◦_ : (σ : Sub Γ Δ) -> (τ : Sub Δ Θ) -> Sub Γ Θ
composeSub :: Sub -> Sub -> Sub
composeSub s1 s2 = Sub s1.domSh s2.codSh $ \sp -> s2.mapping (s1.mapping sp)

-- lift : (σ : Sub Γ Δ) -> Sub (Γ, Α σ) (Δ, Α)
liftSub :: Shape -> Sub -> Sub
liftSub sh@(Param m q _ ()) s = Sub (s.domSh :|> sh) (s.codSh :|> sh) $ nonEmptyDom (\sp t -> s.mapping sp :|> Arg m q t)

-- liftN : (σ : Sub Γ Δ) -> Sub (Γ ++ Α σ) (Δ ++ Α)
liftSubN :: Shapes -> Sub -> Sub
liftSubN n s =
  Sub
    (s.domSh <> n)
    (s.codSh <> n)
    ( \sp ->
        let beginning = S.length s.domSh - S.length n
         in s.mapping (S.take beginning sp) <> S.drop beginning sp
    )

getVar :: Lvl -> Sub -> Arg HTm
getVar x s =
  let ms = fromList . map (Arg Explicit Many . HVar) $ members (Lvl (length s.domSh))
   in (fromJust $ s.mapping ms S.!? x.unLvl)

-- Replace : (σ : Sub Γ Δ) -> (x : Var Δ A) -> (t : Tm Δ A) -> Ctx
-- replace : (σ : Sub Γ Δ) -> (x : Var Γ A) -> (t : Tm Γ A) -> Sub Γ (Replace σ x t)
replaceSub :: Sub -> Lvl -> HTm -> Sub
replaceSub s x t = Sub s.domSh s.codSh $ \sp ->
  S.zipWith
    ( \s' i ->
        if Lvl i == x then s' {arg = t} else s'
    )
    sp
    (S.fromList [0 ..])

-- π₁ : Sub Γ (Δ , A) -> Sub Γ Δ
proj :: Sub -> Sub
proj = projN 1

-- πₙ : Sub Γ (Δ ++ A) -> Sub Γ Δ
projN :: Int -> Sub -> Sub
projN n s = Sub s.domSh (S.take (length s.domSh - n) s.codSh) $ \sp -> S.take (length s.codSh - n) (s.mapping sp)

bindsToShapes :: [(Qty, Name)] -> Shapes
bindsToShapes = fromList . map (\(q, n) -> Param Explicit q n ())

class Subst a where
  -- [_]_ : (σ : Sub Γ Δ) -> P Γ (A σ) -> P Δ A
  sub :: Sub -> a -> a

instance (Subst HTm) where
  sub s (HVar x) = (getVar x s).arg
  sub s (HApp m q t u) = HApp m q (sub s t) (sub s u)
  sub s (HPi m q n a b) = HPi m q n (sub s a) (sub (liftSub (Param m q n ()) s) . b)
  sub s (HLam m q n t) = HLam m q n (sub (liftSub (Param m q n ()) s) . t)
  sub s (HLet q n ty a b) = HLet q n (sub s ty) (sub s a) (sub (liftSub (Param Explicit q n ()) s) . b)
  sub _ (HMeta m bs) = HMeta m bs
  sub s (HCase (Case d ps subj is ty cs)) =
    HCase
      ( Case
          d
          (fmap (sub s) ps)
          (sub s subj)
          (fmap (sub s) is)
          (sub s ty)
          ( fmap
              ( \(Clause p t) -> case t of
                  Nothing -> Clause p Nothing
                  Just t' -> Clause p (Just $ \p' -> let bs = p.binds in sub (liftSubN (bindsToShapes bs) s) (t' p'))
              )
              cs
          )
      )
  sub _ HU = HU
  sub _ (HData d) = HData d
  sub s (HCtor (c, sp)) = HCtor (c, fmap (sub s) sp)
  sub _ (HDef d) = HDef d
  sub _ (HPrim p) = HPrim p
  sub s (HLit l) = HLit (fmap (sub s) l)
  sub s (HRepr t) = HRepr (sub s t)
  sub s (HUnrepr t) = HUnrepr (sub s t)

instance (Subst t) => (Subst (Tel t)) where
  sub _ Empty = Empty
  sub s (x :<| t) = sub s x :<| sub (liftSub (Param x.mode x.qty x.name ()) s) t

instance (Subst t) => (Subst (Spine t)) where
  sub _ Empty = Empty
  sub s (x :<| t) = sub s x :<| sub (liftSub (Param x.mode x.qty (Name "_") ()) s) t

instance (Subst t) => Subst (Arg t) where
  sub s (Arg m q x) = Arg m q (sub s x)

instance (Subst t) => Subst (Param t) where
  sub s (Param m q n x) = Param m q n (sub s x)
