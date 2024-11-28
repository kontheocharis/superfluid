{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
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
    nonEmptyDomL,
    terminalSub,
    unembedClosure1,
    extendSubSp,
    hoistBinders,
    hoistBinders',
  )
where

import Common (Arg (..), Clause (..), Lvl (..), Name (..), Param (..), PiMode (..), Qty (..), Spine, Tel, members, membersIn, nextLvl, nextLvls)
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..), fromList)
import qualified Data.Sequence as S
import Evaluation (Eval, quoteClosure)
import Syntax
  ( Case (..),
    Closure (..),
    HTel (..),
    HTm (..),
    patBinds,
    unembed,
  )

-- Substitution

type Shapes = Tel ()

type Shape = Param ()

data Sub = Sub {domSh :: Shapes, codSh :: Shapes, mapping :: Spine HTm -> Spine HTm}

data BiSub = BiSub {forward :: Sub, backward :: Sub}

-- Create dummy shapes
defaultShapes :: Lvl -> Shapes
defaultShapes l = fromList $ replicate l.unLvl (Param Explicit Many (Name "_") ())

-- @@Performance: can be made more efficient
hoistBinders :: Shapes -> Shapes -> HTm -> (Spine HTm -> HTm)
hoistBinders c (sh :<| shs) t sp = hoistBinder c sh t (hoistBinders c shs t sp)
hoistBinders _ Empty t _ = t

hoistBinder :: Shapes -> Shape -> HTm -> (HTm -> HTm)
hoistBinder c sh t x = sub (extendSub (idSub c) sh (const x)) t -- @@Check: is const x right?

unembedClosure1 :: (Eval m) => Lvl -> Closure -> m (HTm -> HTm)
unembedClosure1 l c = do
  c' <- unembed (map HVar (members (nextLvl l))) <$> quoteClosure l c
  return $ hoistBinder (defaultShapes (Lvl $ length c.env)) (Param Explicit Many (Name "_") ()) c'

hoistBinders' :: Shapes -> Shapes -> HTm -> ([HTm] -> HTm)
hoistBinders' sh t sp = hoistBinders sh t sp . fromList . map (Arg Explicit Many)

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

-- _,_ : (σ : Sub Γ Δ) -> Tm Γ (Α σ) -> Sub Γ (Δ , Α)
extendSub :: Sub -> Shape -> (Spine HTm -> HTm) -> Sub
extendSub s sh v = Sub s.domSh (s.codSh :|> sh) (\g -> let Param m q _ () = sh in s.mapping g :|> (v g <$ Arg m q ()))

extendSubSp :: Sub -> Shape -> Shape -> (Spine HTm -> Spine HTm) -> Sub
extendSubSp s sh sh' v = Sub s.domSh (s.codSh :|> sh') (\g -> s.mapping g <> v g)

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

-- π₁ : Sub Γ (Δ , A) -> Sub Γ Δ
proj :: Sub -> Sub
proj = projN 1

-- πₙ : Sub Γ (Δ ++ A) -> Sub Γ Δ
projN :: Int -> Sub -> Sub
projN n s = Sub s.domSh (S.take (length s.domSh - n) s.codSh) $ \sp -> S.take (length s.codSh - n) (s.mapping sp)

bindsToShapes :: [(Qty, Name)] -> Shapes
bindsToShapes = fromList . map (\(q, n) -> Param Explicit q n ())

class Subst a where
  -- [_]_ : (σ : Sub Γ Δ) -> P Δ (A σ) -> P Γ A
  sub :: Sub -> a -> a

  -- Occurs check
  occurs :: Lvl -> (Lvl -> Bool) -> a -> Bool

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
                  Just t' -> Clause p (Just $ \u -> let bs = patBinds p in sub (liftSubN (bindsToShapes bs) s) (t' u))
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

  occurs _ x (HVar y) = x y
  occurs l x (HApp _ _ t u) = occurs l x t || occurs l x u
  occurs l x (HPi _ _ _ a b) = occurs l x a || occurs (nextLvl l) x (b (HVar l))
  occurs l x (HLam _ _ _ t) = occurs (nextLvl l) x (t (HVar l))
  occurs l x (HLet _ _ _ a b) = occurs l x a || occurs (nextLvl l) x (b (HVar l))
  occurs _ _ (HMeta _ _) = False
  occurs _ _ HU = False
  occurs _ _ (HData _) = False
  occurs l x (HCtor (_, sp)) = any (occurs l x) sp
  occurs _ _ (HDef _) = False
  occurs _ _ (HPrim _) = False
  occurs l x (HLit l') = foldr (\t acc -> acc || occurs l x t) False l'
  occurs l x (HRepr t) = occurs l x t
  occurs l x (HUnrepr t) = occurs l x t
  occurs l x (HCase (Case _ ps subj is ty cs)) =
    any (occurs l x) ps
      || occurs l x subj
      || any (occurs l x) is
      || occurs l x ty
      || any
        ( \(Clause p t) -> case t of
            Nothing -> False
            Just t' ->
              let l' = length $ patBinds p
               in occurs
                    (nextLvls l l')
                    x
                    (t' (map HVar $ membersIn l (Lvl l')))
        )
        cs

instance (Subst t) => (Subst (Tel t)) where
  sub _ Empty = Empty
  sub s (x :<| t) = sub s x :<| sub (liftSub (Param x.mode x.qty x.name ()) s) t

  occurs _ _ Empty = False
  occurs l x (a :<| t) = occurs l x a || occurs (nextLvl l) x t

instance (Subst t) => (Subst (Spine t)) where
  sub _ Empty = Empty
  sub s (x :<| t) = sub s x :<| sub (liftSub (Param x.mode x.qty (Name "_") ()) s) t

  occurs _ _ Empty = False
  occurs l x (a :<| t) = occurs l x a || occurs (nextLvl l) x t

instance (Subst t) => Subst (Arg t) where
  sub s (Arg m q x) = Arg m q (sub s x)

  occurs l x (Arg _ _ t) = occurs l x t

instance (Subst t) => Subst (Param t) where
  sub s (Param m q n x) = Param m q n (sub s x)

  occurs l x (Param _ _ _ t) = occurs l x t

instance Subst HTel where
  sub _ HEmpty = HEmpty
  sub s (HWithParam m q n t tel) =
    HWithParam
      m
      q
      n
      (sub s t)
      (sub (liftSub (Param m q n ()) s) . tel)

  occurs _ _ HEmpty = False
  occurs l x (HWithParam m q _ t tel) = occurs l x t || occurs (nextLvl l) x (tel (HVar l))
