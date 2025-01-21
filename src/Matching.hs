{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Matching
  ( Matching (..),
    caseTree,
    clausesWithEmptyConstraints,
    MatchingState (..),
    MatchingError,
    clauses,
  )
where

import Algebra.Lattice (Lattice (..), (/\))
import Common
  ( Arg (..),
    Clause (..),
    Clauses,
    CtorGlobal (..),
    DataGlobal (..),
    DefGlobal,
    Has (..),
    HasNameSupply (uniqueName),
    Loc,
    Logger (..),
    Lvl (..),
    Name (..),
    Param (..),
    Parent (child),
    PiMode (..),
    Qty (..),
    Spine,
    Try (..),
    mapSpine,
    nextLvl,
    ofShapes,
    plainShape,
    spineShapes,
    telShapes,
  )
import Context
import Context (unembedClosure1Here)
import Control.Applicative (asum)
import Control.Monad (forM)
import Control.Monad.Extra (firstJustM)
import Data.Foldable (Foldable (..), toList)
import Data.List (intercalate)
import Data.Maybe (catMaybes)
import Data.Semiring (Semiring (times))
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Data.Traversable (for)
import Debug.Trace (trace, traceM)
import Evaluation
  ( Eval (..),
    embedEval,
    ifIsData,
    quoteUnembed,
  )
import Globals
  ( CtorConstructions (..),
    CtorGlobalInfo (..),
    DataConstructions (..),
    DataGlobalInfo (..),
    KnownGlobal (KnownConf, KnownCycle, KnownDCongSp, KnownEmpty, KnownEqual, KnownHEqual, KnownInj, KnownRefl, KnownVoid),
    getCtorGlobal,
    getCtorGlobal',
    getDataGlobal,
    getDataGlobal',
    knownCtor,
    knownData,
    knownDef,
    splitParamsAndIndices,
  )
import Printing (Pretty (..))
import Substitution
  ( BiSub (..),
    Shape,
    Shapes,
    Sub (..),
    Subst (..),
    composeSub,
    extendSub,
    hCtxToTel,
    hoistBinders,
    hoistBinders',
    idSub,
    liftSub,
    liftSubN,
    mapSub1,
    mapSubN,
    proj,
    replaceVar,
  )
import Syntax
  ( Case (..),
    HCtx,
    HTel (HEmpty, HWithParam),
    HTm (..),
    HTy,
    Pat (..),
    STm (..),
    VTm (..),
    VTy,
    ctxSize,
    embed,
    extendCtxWithTel,
    extendTel,
    hApp,
    hGatherApps,
    hLams,
    joinTels,
    lastVar,
  )
import Typechecking (Child, InPat (InPat), ModeG (..), Tc (..), ifForcePiType)
import Unelaboration (Unelab)
import Unification (CanUnify (..), canUnifyHere)
import Prelude hiding (cycle, pi)

data MatchingError = MatchingError | IncompleteClauses

instance (Monad m) => Pretty m MatchingError where
  pretty MatchingError = return "Matching error"
  pretty IncompleteClauses = return "Incomplete clauses"

class (Eval m, Has m Loc, Tc m) => Matching m where
  matchingError :: MatchingError -> m a

runTc :: (Matching m) => Qty -> Ctx -> m a -> m a
runTc q c x = enter (const q) $ enterCtx (const c) x

runTc' :: (Matching m) => Qty -> HCtx -> m a -> m a
runTc' q c x = do
  c' <- embedCtx c
  runTc q c' x

embedCtx :: (Matching m) => HCtx -> m Ctx
embedCtx = embedCtx' emptyCtx
  where
    embedCtx' :: (Matching m) => Ctx -> HCtx -> m Ctx
    embedCtx' c Empty = return c
    embedCtx' c (Param m q x a :<| ps) = do
      a' <- embedEval c.lvl a
      let c' = bind m x q a' c
      embedCtx' c' ps

unembedCtx :: (Matching m) => Ctx -> m HCtx
unembedCtx ctx = do
  let entries = ctxEntries ctx
  enter (const emptyCtx) $ unembedCtx' entries
  where
    unembedCtx' :: (Matching m) => [CtxEntry] -> m HCtx
    unembedCtx' [] = return Empty
    unembedCtx' (e : es) = do
      e' <- Param e.mode e.qty e.name <$> quoteUnembedHere (assertIsNeeded e.ty)
      es' <- enter (addCtxEntry e) $ unembedCtx' es
      return $ e' :<| es'

-- Unification

-- The unify outcome is a "decorated" bit that tells us whether the unification
-- was successful or not.
data UnifyOutcome = Can | Cannot [MatchingError]

-- A unification between terms a, b : Tm Γ A is a telescope Γ' and an
-- invertible (with coherence proofs computing to refl)
-- substitution σ : Sub Γ' (Γ, (a = b)).
--
-- Unification will not always succeed.
--
-- We also "remember" if Γ' is the bottom context (x : Empty) or not.
-- The `Shapes` is the shape of the added equalities in the context.
type Unification = (HCtx, Shapes, UnifyOutcome, BiSub)

instance Lattice UnifyOutcome where
  Can \/ _ = Can
  _ \/ Can = Can
  Cannot xs \/ Cannot ys = Cannot (xs ++ ys)

  Can /\ Can = Can
  Cannot xs /\ Cannot ys = Cannot (xs ++ ys)
  _ /\ _ = Cannot []

--- Simple equality
--
-- internally:
-- Equal : [A : Type] -> A -> A -> Type
equality :: HTm -> HTm -> HTm -> HTm
equality ty a b =
  hApp
    (HData (knownData KnownEqual))
    (S.fromList [Arg Implicit Zero ty, Arg Explicit Zero a, Arg Explicit Zero b])

-- Simple reflexivity
--
-- internally:
-- refl : [A : Type] -> (0 x : A) -> Equal [A] x x
refl :: HTm -> HTm -> HTm
refl ty = HApp Implicit Zero (HCtor (knownCtor KnownRefl, S.singleton (Arg Implicit Zero ty)))

-- Higher equality (written as `=P,e=`)
--
--          m : HEqual s t e x y
-- x : P s ---- y : P t
--   |            |
--   |            |
--   s ---------- t
--          e : Equal s t
--
-- internally:
-- HEqual : [A : Type] (s t : A) (e : Equal s t) (P : A -> Type) -> P s -> P t -> Type
-- HEqual [A] s t e P u v = Equal [P t] (subst P e u) v
hequality :: HTm -> HTm -> HTm -> HTm -> HTm -> HTm -> HTm
hequality s t e p u v =
  hApp
    (HData (knownData KnownHEqual))
    ( S.fromList
        [ Arg Implicit Zero s,
          Arg Explicit Zero t,
          Arg Explicit Zero e,
          Arg Explicit Zero p,
          Arg Explicit Zero u,
          Arg Explicit Zero v
        ]
    )

-- Equality for spines (Written δ =Δ= γ for a telescope Δ and spines δ γ : Tms Δ)
--
-- (() =()= ()) := ()
-- ((x,xs) =(x : A),Δ= (y,ys)) := (e : x =A= y, xs =Δ,e= ys)
--
-- @@Check: hacky, no way this is right
equalitySp :: HTel -> Spine HTm -> Spine HTm -> HTel
equalitySp HEmpty Empty Empty = HEmpty
equalitySp (HWithParam m _ nt tt delta) (Arg _ _ x :<| xs) (Arg _ _ y :<| ys) =
  HWithParam m Zero (Name (nt.unName ++ "-eq")) (equality tt x y) (\e -> equalitySp' (x, y, e, delta y) delta xs ys)
  where
    equalitySp' :: (HTm, HTm, HTm, HTel) -> (HTm -> HTel) -> Spine HTm -> Spine HTm -> HTel
    equalitySp' (s, t, e, p) (($ t) -> HEmpty) Empty Empty = HEmpty
    equalitySp' (s, t, e, p) (($ t) -> (HWithParam m _ nt tt delta)) (Arg _ _ x :<| xs) (Arg _ _ y :<| ys) =
      HWithParam
        m
        Zero
        (Name (nt.unName ++ "-heq"))
        (hequality s t e tt x y)
        (\e' -> equalitySp' (x, y, e', p) delta xs ys)
    equalitySp' _ _ _ _ = error "Mismatching spines should never occur in well-typed terms"
equalitySp _ _ _ = error "Mismatching spines should never occur in well-typed terms"

-- Reflexivity for spines
reflSp :: HTel -> Spine HTm -> Spine HTm
reflSp HEmpty Empty = Empty
reflSp (HWithParam m _ _ tt delta) (Arg _ _ x :<| xs) = Arg m Zero (refl tt x) :<| reflSp (delta x) xs
reflSp _ _ = error "Mismatching spines should never occur in well-typed terms"

-- dcong : (f : Tm Γ (Π A Τ)) -> {x y : Tm Γ A} -> Tms Γ (x = y) -> Tms Γ (f x = f y)
-- dcong :: HTy -> (HTm -> HTy) -> (HTm -> HTm) -> HTm -> HTm
-- dcong a t = undefined

-- dcongSp : (f : Tm Γ (Πs Δ Τ)) -> {xs ys : Tms Γ Δ} -> Tms Γ (xs ..= ys) -> Tm Γ (f xs = f ys)
dcongSp :: HTel -> (Spine HTm -> HTy) -> (Spine HTm -> HTm) -> Spine HTm -> HTm
dcongSp delta _ f ps = hApp (HDef (knownDef KnownDCongSp)) (Arg Explicit Many (hLams delta f) :<| ps) -- @@Hack

-- inj : (c : Ctor D Δ Π ξ) -> {δ : Δ} {xs ys : Tms Γ (Π [δ])} -> Tm Γ (c xs = c ys) -> Tms Γ (xs ..= ys)
inj :: CtorGlobal -> Spine HTm -> Spine HTm -> Spine HTm -> HTm -> Spine HTm
inj c _ ys _ _ = fmap (\p -> p {arg = hApp (HDef (knownDef (KnownInj c))) (S.singleton p)}) ys

-- conf : (c1 : Ctor D Δ Π₁, c2 : Ctor D Δ Π₂ ξ₂) -> {δ : Δ} {xs : Tms Γ Π₁[δ]} {ys : Tms Γ Π₂[δ]}
--            -> Tm Γ (c1 xs = c2 ys)
--            -> Tm Γ Empty
conf :: CtorGlobal -> CtorGlobal -> Spine HTm -> Spine HTm -> Spine HTm -> HTm -> HTm
conf c1 c2 _ _ _ = hApp (HDef (knownDef (KnownConf c1 c2))) . S.singleton . Arg Explicit Many

-- @@Todo: properly encode the < relation, and deal with indices!
-- cyc : {δ : Δ} (x t : D δ ψ) -> {{auto _ : x < t}} -> Tm Γ (x = t) -> Tm Γ Empty
cyc :: DataGlobal -> Spine HTm -> HTm -> HTm -> HTm -> HTm
cyc d _ _ _ = hApp (HDef (knownDef (KnownCycle d))) . S.singleton . Arg Explicit Many

-- Never
--
-- This is the internal Empty type's eliminator.
--
-- Important: 'internal Empty' means void in the metatheory, because the Unit
-- type behaves like the empty context instead.
--
-- never : [A : Ty Γ] -> Tm Γ Empty -> Tm Γ A
void :: HTy -> HTm -> HTm
void ty = HApp Explicit Zero (HApp Implicit Zero (HDef (knownDef KnownVoid)) ty)

voidSh :: Shapes
voidSh = Param Explicit Many (Name "_") () :<| Empty

voidCtx :: HCtx
voidCtx = S.singleton (Param Explicit Many (Name "_") (HData (knownData KnownEmpty)))

initialSub :: Shapes -> HCtx -> Sub
initialSub vSh sh = mapSub1 vSh (telShapes sh) (\_ x -> fmap (\p -> Arg p.mode p.qty (void p.ty x)) sh)

-- Definitional equality checker. Uses TC's unification.
canConvert :: (Matching m) => HCtx -> HTm -> HTm -> m Bool
canConvert ctx a b = do
  q <- qty -- @@Check: this shouldn't matter right?
  runTc' q ctx $ do
    -- Embed both terms, check with `canUnifyHere` and return the result.
    a' <- embedEvalHere a
    b' <- embedEvalHere b
    res <- canUnifyHere a' b'
    case res of
      Yes -> return True
      _ -> return False

traceProblem :: (Matching m) => HCtx -> HTel -> Spine HTm -> Spine HTm -> m ()
traceProblem ctx t a b = do
  c' <- embedCtx ctx
  enter (const c') $ do
    traceM "Problem:"
    traceM "Context:"
    traceM =<< pretty c'
    traceM "Tel:"
    traceM =<< pretty t
    traceM "Spine 1:"
    traceM =<< pretty a
    traceM "Spine 2:"
    traceM =<< pretty b
    return ()

-- Unification:
unifyPLSpines :: (Matching m) => HCtx -> HTel -> Spine HTm -> Spine HTm -> m Unification
unifyPLSpines ctx HEmpty Empty Empty = do
  -- Solving unify Γ ⊢ () = () : ()
  --
  -- Empty spines lead to identity substitutions
  --
  -- Γ () ≃ Γ
  -- So solve with Γ' = Γ and σ = id
  return
    ( ctx,
      Empty,
      Can,
      BiSub
        { forward = idSub (telShapes ctx),
          backward = idSub (telShapes ctx)
        }
    )
unifyPLSpines ctx (HWithParam _ _ _ ty ts) (Arg _ _ x :<| xs) (Arg _ _ y :<| ys) = do
  -- Solving unify Γ ⊢ (x, ..xs) = (y, ..ys) : (_ : A)Δ

  -- (Γ', σ : Sub Γ' Γ(χ = y)) <- unify Γ A x y
  (ctx', sh', o, s) <- unifyPL ctx ty x y

  -- (Γ'', σ' : Sub Γ'' Γ'(χs σ = ys σ)) <- unifySp Γ' ((Δ [x]) σ) (xs σ) (ys σ)
  (ctx'', sh'', o', s') <- unifyPLSpines ctx' (sub s.forward (ts x)) (sub s.forward xs) (sub s.forward ys)

  -- return (Γ'', (
  --     1 = lift (xs ..= ys) σ ∘ σ',
  --    -1 = σ'⁻¹ ∘ lift (xs σ⁻¹ ..= ys σ⁻¹) σ⁻¹
  -- ))
  return
    ( ctx'',
      sh' <> sh'',
      o /\ o',
      BiSub
        { forward = composeSub (liftSubN (spineShapes xs) s.forward) s'.forward,
          backward = composeSub s'.backward (liftSubN (spineShapes xs) s.backward)
        }
    )
unifyPLSpines _ _ _ _ = error "Mismatching spines should never occur in well-typed terms"

unifyPL :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m Unification
unifyPL ctx ty t1 t2 = do
  let tactics = [solution, injectivity, conflict, cycle, deletion]
  res <- firstJustM (\t -> t ctx ty t1 t2) tactics
  case res of
    Just x -> return x
    Nothing -> matchingError MatchingError

-- Unification tactics

solution :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m (Maybe Unification)
solution ctx ty a b = case (a, b) of
  (HVar x', HVar x)
    | x' < x' -> solution ctx ty (HVar x) (HVar x')
    | otherwise -> solution ctx ty (HVar x') (HVar x)
  (HVar x, _) -> do
    let l = Lvl (length ctx)

    -- Ensure that b is well scoped at the place of x.
    if occurs l (>= x) b
      then return Nothing
      else do
        let sh = telShapes ctx

        -- Make a new name and shape for the new context
        p <- uniqueName
        let csh = Param Explicit Many p ()

        -- Substitute b for l in the (rest of) the context, while removing l from
        -- the context

        -- Γx (context)
        let ctxx = S.take x.unLvl ctx

        -- (x : A)
        let xSh = S.index sh x.unLvl

        -- xΓ (telescope)
        let xctxx = S.drop (nextLvl x).unLvl ctx

        -- xΓ [x ↦ b]
        --
        -- We want Sub Γx Γx(x : A) which can be constructed as:
        -- [x ↦ a] = (id, b)
        let vs = extendSub (idSub sh) xSh (const b) -- @@Check: will const b work with the HOAS?
        let xctxx' = sub vs xctxx

        -- (Γx, xΓ (id, a)) (context)
        let ctx' = ctxx <> xctxx'

        -- Returning shape
        let rsh = telShapes ctx'

        -- We need to construct an invertible substitution:
        --
        -- (Γx, x : A, xΓ) ≃ Γ
        -- a : Tm Γx A
        -- ----------
        -- σ : Sub Γ(x = b) (Γx, xΓ (id, b))
        -- where
        --    σ = (\(γx, b', xγ) p => (γx, substSp b'  xγ (id, x)))
        --    σ⁻¹ = (\γ γ' => (γ, b, γ', refl b))
        let s =
              BiSub
                { forward = mapSub1 (sh :|> csh) rsh (\sp _ -> S.take x.unLvl sp <> sub vs (S.drop (nextLvl x).unLvl sp)),
                  backward =
                    mapSubN
                      rsh
                      (sh :|> csh)
                      (telShapes ctxx)
                      ( \sp sp' ->
                          sp
                            <> ofShapes (S.singleton xSh) [b]
                            <> sp'
                            <> ofShapes (S.singleton csh) [refl ty b]
                      )
                }
        traceM "SOL"
        pretty s.forward >>= traceM
        pretty s.backward >>= traceM
        traceM "ENDSOL"
        return $ Just (ctx', S.singleton csh, Can, s)
  (_, HVar x) -> solution ctx ty (HVar x) a
  _ -> return Nothing

injectivity :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m (Maybe Unification)
injectivity ctx ty a b = case (hGatherApps a, hGatherApps b) of
  ((HCtor (c1, pp), xs), (HCtor (c2, _), ys)) | c1 == c2 -> do
    -- Γ ⊢ (c xs : D δ ξ[xs]) =? (c ys : D δ ξ[ys]) -- @@Todo: this should turn into equality of spines!
    --
    -- Assume : length xs = length ys = n
    -- Assume:  Data params are equal
    -- Reason : Terms are well-typed *and* fully eta-expanded. @@Todo: Actually do the latter!
    let sh = telShapes ctx
    let c = c1
    (ci, cc) <- access (getCtorGlobal' c)
    let n = cc.argsArity

    -- (Γ', σ : BiSub Γ' Γ(xs ..= ys)) <- unify Γ xs ys
    (ctx', _, o, s) <- unifyPLSpines ctx (cc.args pp) xs ys

    -- Make a new name and shape for the new context
    x <- uniqueName
    let csh = Param Explicit Many x ()

    -- Now we need to construct an invertible substitution:
    --
    -- σ : BiSub Γ(xs ..= ys) Γ(c xs = c ys)
    -- where
    --    σ' = (πₙ id, dcongSp c (lastN n))
    --    σ'⁻¹ = (π₁ id, noConf c here)
    let s' =
          BiSub
            { forward =
                mapSubN
                  (sh <> n)
                  (sh :|> csh)
                  sh
                  ( \sp ps ->
                      sp
                        :|> Arg
                          Explicit
                          Many
                          ( dcongSp
                              (cc.args pp)
                              (hApp (HData ci.dataGlobal) . cc.returnIndices pp)
                              (hApp (HCtor (c, pp)))
                              ps
                          )
                  ),
              backward =
                mapSub1
                  (sh :|> csh)
                  (sh <> n)
                  (\sp p -> sp <> inj c pp xs ys p)
            }

    -- return (Γ', (
    --     1 = σ' ∘ σ,
    --     -1 = σ⁻¹ ∘ σ'⁻¹
    -- ))
    return . Just $
      ( ctx',
        S.singleton csh,
        o,
        BiSub
          { forward = composeSub s'.forward s.forward,
            backward = composeSub s.backward s'.backward
          }
      )
  _ -> return Nothing

conflict :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m (Maybe Unification)
conflict ctx ty a b = case (hGatherApps a, hGatherApps b) of
  ((HCtor (c1, pp), xs), (HCtor (c2, _), ys)) | c1 /= c2 -> do
    -- Γ ⊢ c1 xs =? c2 ys : D δ ξ
    --
    -- This is a conflict, so we need to return a disunifier.
    -- Make a new name and shape for the new context
    let sh = telShapes ctx
    x <- uniqueName
    let csh = Param Explicit Many x ()

    -- We return an invertible substitution:
    --
    -- σ : BiSub ⊥ Γ(c1 xs = c2 ys)
    -- where
    --     σ = init Γ(c1 xs = c2 ys),     -- init X is the initial morphism from the void context to X
    --     σ⁻¹ = (ɛ Γ, conf c1 c2 here)    -- ɛ X is the terminal morphism from X to the empty context
    return . Just $
      ( voidCtx,
        S.singleton csh,
        Cannot [],
        BiSub
          { forward = initialSub voidSh (ctx :|> csh {ty = equality ty a b}),
            backward = mapSub1 (sh :|> csh) voidSh (\_ p -> ofShapes voidSh [conf c1 c2 pp xs ys p])
          }
      )
  _ -> return Nothing

cycle :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m (Maybe Unification)
cycle ctx ty a b = case (a, b) of
  (_, HVar x) -> cycle ctx ty (HVar x) a
  (a'@(HVar x), b'@(hGatherApps -> (HCtor (c, pp), xs))) -> do
    -- Check if x occurs in xs, if so, then we have a cycle.
    let l = Lvl (length ctx)
    ci <- access (getCtorGlobal c)
    if occurs l (== x) xs
      then do
        let sh = telShapes ctx
        -- Make a new name and shape for the new context
        y <- uniqueName
        let csh = Param Explicit Many y ()

        -- We return an invertible substitution:
        --
        -- σ : BiSub ⊥ Γ(x = c xs)
        -- where
        --     σ = init Γ(x = c xs),
        --     σ⁻¹ = (ɛ Γ, cyc c x)
        return . Just $
          ( ctx,
            S.singleton csh,
            Cannot [],
            BiSub
              { forward = initialSub voidSh (ctx :|> csh {ty = equality ty a' b'}),
                backward = mapSub1 (sh :|> csh) voidSh (\_ p -> ofShapes voidSh [cyc ci.dataGlobal pp (hApp (HCtor (c, pp)) xs) (HVar x) p])
              }
          )
      else
        return Nothing
  _ -> return Nothing

deletion :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m (Maybe Unification)
deletion ctx ty a b = do
  let sh = telShapes ctx
  -- If we can unify a and b we can delete the equation since it will evaluate to refl.
  c <- canConvert ctx a b

  -- Make a new name and shape for the new context
  x <- uniqueName
  let csh = Param Explicit Many x ()

  -- More precisely, we return an invertible substitution:
  --
  -- σ : BiSub Γ Γ(a = a)
  -- where
  --     σ = (id, refl a)
  --     σ⁻¹ = π₁ id
  --
  -- ##Important: rinv/linv proofs of this isomorphism require propositional K!
  if c
    then
      return . Just $
        ( ctx,
          S.singleton csh,
          Can,
          BiSub {forward = extendSub (idSub sh) csh (\_ -> refl ty a), backward = proj (idSub (sh :|> csh))}
        )
    else
      return Nothing

-- Clauses

type ConstrainedClauses pat tm = [ConstrainedClause (Spine pat) tm]

type ConstrainedClause pats tm = Clause (SimpleConstraintSet, HCtx, pats) tm

-- Constraints

data Constraint = Constraint
  { lvl :: Lvl,
    lhs :: HTm,
    rhs :: Pat,
    param :: Param HTy
  }

instance (Unelab m, Has m Ctx) => Pretty m SimpleConstraint where
  pretty (SimpleConstraint l x p pr) = pretty (Constraint l (HVar x) p pr)

instance (Unelab m, Has m Ctx) => Pretty m Constraint where
  pretty (Constraint l x p _) = do
    x' <- pretty (embed l x)
    p' <- pretty p
    return $ x' ++ " = " ++ p'

data SimpleConstraint = SimpleConstraint
  { lvl :: Lvl,
    lhs :: Lvl,
    rhs :: Pat,
    param :: Param HTy
  }

data HList i t = HNil | HCons t (i -> HList i t)

instance Functor (HList i) where
  fmap f HNil = HNil
  fmap f (HCons x xs) = HCons (f x) (fmap f . xs)

instance Semigroup (HList i t) where
  HNil <> xs = xs
  HCons x xs <> ys = HCons x (\i -> xs i <> ys)

instance Monoid (HList i t) where
  mempty = HNil

type Constraints = HList HTm Constraint

type SimpleConstraints = HList HTm SimpleConstraint

type SimpleConstraintSet = [SimpleConstraint]

type ConstraintSet = [Constraint]

instance Subst Constraint where
  sub s (Constraint l x p q) = Constraint l (sub s x) p (sub s q)
  occurs l f (Constraint _ x p _) = occurs l f x || occurs l f p

instance Subst Constraints where
  sub _ HNil = HNil
  sub s (HCons x xs) = HCons (sub s x) (sub (liftSub plainShape s) . xs)
  occurs l f HNil = False -- @@OhNo!

subSimpleConstraint :: Sub -> SimpleConstraint -> Constraint
subSimpleConstraint s (SimpleConstraint l x p q) = sub s (Constraint l (HVar x) p q)

subSimpleConstraints :: Sub -> SimpleConstraintSet -> ConstraintSet
subSimpleConstraints s = map (subSimpleConstraint s)

simplifyConstraints :: (Matching m) => Constraints -> m (Maybe (SimpleConstraintSet, HCtx))
simplifyConstraints (HCons c cs) = do
  cs' <- simplifyConstraint c
  case cs' of
    Just (cs'', is) -> do
      rest <- simplifyConstraints (cs c.lhs)
      case rest of
        Just (restCs, restIs) -> return . Just $ (cs'' <> restCs, is <> restIs)
        Nothing -> return Nothing
    Nothing -> return Nothing
simplifyConstraints HNil = return (Just ([], Empty))

zipToConstraints :: Lvl -> Spine HTm -> Spine Pat -> HTel -> Constraints
zipToConstraints l (Arg _ _ x :<| xs) (Arg _ _ p :<| ps) (HWithParam m q n ty tel) =
  HCons (Constraint l x p (Param m q n ty)) (zipToConstraints (nextLvl l) xs ps . tel)
zipToConstraints _ Empty Empty HEmpty = HNil
zipToConstraints _ _ _ _ = error "Mismatching spines should never occur in well-typed terms"

simplifyConstraint :: (Matching m) => Constraint -> m (Maybe (SimpleConstraintSet, HCtx))
simplifyConstraint co = do
  case co of
    Constraint l (HVar x) p q -> return . Just $ ([SimpleConstraint l x p q], Empty)
    Constraint l (hGatherApps -> (HCtor (c, _), sp)) (CtorP (c', _) sp') (Param {ty = (hGatherApps -> (HData d, dsp))})
      | c == c' -> do
          (_, dc) <- access (getDataGlobal' d)
          (_, cc) <- access (getCtorGlobal' c)
          let (dpp, _) = splitParamsAndIndices dc dsp
          let ctorArgs = cc.args dpp
          simplifyConstraints (zipToConstraints l sp sp' ctorArgs)
      | otherwise -> return Nothing
    Constraint _ _ (LvlP _ n _) p -> do
      return . Just $ ([], Empty :|> p {name = n})
    _ -> do
      co' <- pretty co
      error $ "invalid constraint: " ++ co'

refineClause :: (Matching m) => Sub -> ConstrainedClause p t -> m (Maybe (ConstrainedClause p t))
refineClause s cl' = case cl' of
  Clause (cs, ctx, ps) t -> do
    ps' <- mapM pretty cs
    pctx <- embedCtx ctx
    enterCtx (const pctx) . traceM $ "Refining constraints : " ++ show ps'
    traceM $ "Substitution is : "
    pretty s >>= traceM
    let csn = subSimpleConstraints s cs
    cs' <- simplifyConstraints csn
    traceM $ "Substitution done"
    case cs' of
      Just (cs'', is) -> do
        let ctx' = sub s (ctx <> is)
        return . Just $ Clause (cs'', ctx', ps) t
      Nothing -> return Nothing

-- Matching

type HMode = ModeG HTy

type HChildTm m = Qty -> HCtx -> HMode -> m (HTm, HTy)

type HChildPat m = Qty -> HCtx -> HMode -> m (Pat, HTy, HCtx)

data MatchingState m = MatchingState
  { ctx :: HCtx,
    qty :: Qty,
    ty :: HTy,
    cls :: ConstrainedClauses (HChildPat m) (HChildTm m)
  }

forceData :: (Matching m) => HCtx -> HTy -> m (DataGlobal, Spine HTm, Spine HTm)
forceData ctx ty = do
  let size = ctxSize ctx
  ty' <- embedEval size ty
  ifIsData
    (ctxSize ctx)
    ty'
    ( \d sp -> do
        di <- access (getDataGlobal d)
        sp' <- traverse (traverse $ quoteUnembed size) sp
        let paramSp = S.take (length di.params) sp'
        let indexSp = S.drop (length di.params) sp'
        return (d, paramSp, indexSp)
    )
    (matchingError MatchingError) -- @@Todo: errors

tmAsPat :: (Matching m) => Qty -> HTm -> m Pat
tmAsPat q t = case hGatherApps t of
  (HVar x, Empty) -> do
    entry <- access (`coindexCtx` x)
    return (LvlP q entry.name x)
  (HCtor (c, pp), sp) ->
    CtorP (c, pp)
      <$> traverse (\a -> traverse (tmAsPat a.qty) a) sp
  _ -> matchingError MatchingError -- @@Todo: errors

ifForcePi :: (Matching m) => Qty -> HCtx -> PiMode -> HTy -> (Param HTy -> (HTm -> HTy) -> m a) -> m a -> m a
ifForcePi q ctx m ty the els = runTc' q ctx $ do
  pt <- pretty ty
  traceM $ "Forcing pi type HOAS: " ++ pt
  ty' <- embedEvalHere ty
  tyy'' <- pretty ty'
  traceM $ "Forcing pi type: " ++ tyy''

  c <- getCtx >>= pretty
  traceM $ "Tc CTX: " ++ c

  ifForcePiType
    m
    ty'
    ( \m' q' x a b -> do
        pb <- pretty b
        traceM $ "Now in " ++ pb
        a' <- quoteUnembedHere a
        b' <- unembedClosure1Here b
        the (Param m' q' x a') b'
    )
    (\_ _ _ _ _ -> els) -- @@Todo: errors

-- Check if the context is void, and return the level of the void member.
ctxIsVoid :: (Matching m) => HCtx -> m (Maybe Lvl)
ctxIsVoid (ps :|> p) = do
  ty' <- unfoldHoas Empty p.ty
  case hGatherApps ty' of
    (HData d, _) | d == knownData KnownEmpty -> return . Just $ ctxSize ps
    _ -> return Nothing
ctxIsVoid Empty = return Nothing

unfoldHoas :: (Matching m) => HCtx -> HTm -> m HTm
unfoldHoas ctx x = do
  ctx' <- embedCtx ctx
  enterCtx (const ctx') $ do
    x' <- embedEvalHere x >>= unfoldHere
    quoteUnembed (ctxSize ctx) x'

-- Check if clauses C are of the form (csᵢ (pᵢ psᵢ) -> tᵢ)ᵢ
hasNextPat :: (Matching m) => ConstrainedClauses ps ts -> m (Maybe (Arg ()))
hasNextPat cls = do
  case cls of
    Clause (_, _, Empty) _ : _ -> return Nothing
    Clause (_, _, a :<| _) _ : _ -> return . Just $ a {arg = ()}
    [] -> return Nothing

-- In context Γ (ctx), and return type T (ty) we have a list of unelaborated
-- clauses C with constraints. We want to produce a term Γ ⊢ e : T that "emulates"
-- the clauses using lower-level machinery, while typechecking the clauses.
--
-- Γ ⊢ C ~> e : T
-- - Clauses C in context Γ are elaborated to a term e of type T.
--
-- This is done by the tactics below:
caseTree :: (Matching m) => MatchingState m -> m HTm
caseTree c = do
  ctx' <- embedCtx c.ctx
  c' <- pretty ctx'
  cs' <- mapM (mapM pretty) (map (\(Clause (cs, _, _) _) -> cs) c.cls)
  traceM $ "In context " ++ c'
  traceM $ "and constraints " ++ show cs'
  traceM $ "and clause count " ++ show (length c.cls)

  -- First we add all the variables to the context
  -- Then once we can't anymore, we split on the first-added constraint
  -- Once all the constraints are solved, we can typecheck the right-hand
  -- side of the first clause that matches.
  let tactics = [intro c, split c, absurd c, done c]
  result <- asum <$> sequence tactics
  case result of
    Just r -> return r
    Nothing -> error "no case tree tactic matched"

-- There are no clauses left.
--
-- If we are in a `void` context (Γ = Γ₁(p : ⊥)Γ₂) then we can emit the
-- void eliminator to get the goal.
--
-- Otherwise, pattern matching is incomplete.
absurd :: (Matching m) => MatchingState m -> m (Maybe HTm)
absurd (MatchingState ctx _ ty cls) = do
  case cls of
    [] -> do
      -- @@Todo: handle impossible
      voidLvl <- ctxIsVoid ctx
      case voidLvl of
        Just l -> return . Just $ void ty (HVar l)
        Nothing -> matchingError IncompleteClauses
    _ -> return Nothing

-- There is no next pattern and the constraints have been solved:
--
-- Γ ⊢ C ~> e : B and C = ([] ϵ -> tᵢ)ᵢ
--
-- We simply take the first clause and typecheck its term.
done :: (Matching m) => MatchingState m -> m (Maybe HTm)
done (MatchingState _ q ty cls) = do
  case cls of
    Clause ([], ctx, Empty) (Just tm) : _ -> do
      -- @@Todo: qty
      ctx' <- embedCtx ctx
      pretty ctx' >>= traceM
      (tm', _) <- tm q ctx (Check ty)
      return (Just tm')
    _ -> return Nothing

hSnoc :: (Monoid (a i), Monad a) => HList i t -> (a i -> t) -> HList i t
hSnoc HNil f = HCons (f mempty) (const HNil)
hSnoc (HCons x xs) f = HCons x (\i -> hSnoc (xs i) (\is -> f (is <> return i)))

-- Given a 'constraint scheme' (p . [x = p]), i.e. a constraint parametrized by
-- a pattern, and an argument type `ty`,  apply this constraint to the first
-- pattern of each clause in C.
addNextConstraint ::
  (Matching m) =>
  MatchingState m ->
  Param HTy ->
  (Pat -> HCtx -> SimpleConstraint) ->
  ConstrainedClauses (HChildPat m) (HChildTm m) ->
  m (ConstrainedClauses (HChildPat m) (HChildTm m))
addNextConstraint st param f cls = forM cls $ \case
  (Clause (cs, ctx, p :<| ps) t) -> do
    -- @@Todo: deal with implicits
    (p', _, ctx') <- p.arg (st.qty `times` param.qty) ctx (Check param.ty)
    return $ Clause (cs ++ [f ctx' p'], ctx', ps) t
  (Clause (_, _, Empty) _) -> error "No next pattern to add constraint to"

-- Given a list of clauses C, remove the first constraint from each clause.
removeFirstConstraint :: ConstrainedClauses (HChildPat m) (HChildTm m) -> ConstrainedClauses (HChildPat m) (HChildTm m)
removeFirstConstraint = map $ \case
  (Clause (co : cs, ctx, ps) t) -> Clause (cs, ctx :|> co.param, ps) t
  (Clause ([], _, _) _) -> error "No constraints to remove"

-- The goal computes to a Π-type, and there is a next pattern:
--
-- Γ ⊢ C ~> e : (x : A) -> B  and C = ([csᵢ] (pᵢ psᵢ) -> tᵢ)ᵢ
--
-- We add (x : A) to the context to get Γ(x : A) and equate each clause's next pattern
-- to the variable x, to get C(x : A). (Note: C is not a context or telescope, but a list of clauses!)
--
-- Finally we can construct the goal as
--
--    Γ(x : A) ⊢ C(x : A) ~> e : B[x]
--   -----------------------------------------
--    Γ ⊢ C ~> (λ x . e[x]) : (x : A) -> B
intro :: (Matching m) => MatchingState m -> m (Maybe HTm)
intro st@(MatchingState ctx q' ty cls) = do
  ps <- hasNextPat cls
  case ps of
    Nothing -> return Nothing
    -- @@Todo: if the args don't match in PiMode, insert!
    Just (Arg m' _ ()) -> do
      debug $ "Intro with mode " ++ show m'
      ifForcePi
        q'
        ctx
        m'
        ty
        ( \p@(Param m q x a) b -> do
            a' <- pretty a
            traceM $ " Type of a : " ++ a'
            let ctxShapes = telShapes ctx
            let s t = extendSub (idSub ctxShapes) (Param m q x ()) (hoistBinders Empty ctxShapes t)
            let ctx' = ctx :|> Param m q x a
            let b' = b (HVar (lastVar ctx'))
            cls' <- addNextConstraint st p (\pt ctx'' -> SimpleConstraint (ctxSize ctx'') (lastVar ctx') pt p) cls -- implicit weakening everywhere!
            rest <- caseTree (MatchingState ctx' q' b' cls')
            return . Just $ HLam m q x (\t -> sub (s t) rest)
        )
        (return Nothing)

-- There is a next constraint to split on.
--
-- Γ ⊢ C ~> e : B and  C = ([xᵢ = pᵢ, csᵢ] (psᵢ) -> tᵢ)ᵢ
--
-- This is the most complex case since we need to split on the constraint xᵢ = pᵢ:
-- - If pᵢ is a variable (@@Check for all i?), we can use the solution rule.
-- - Otherwise we need to generate an eliminator that matches the outer layer of
--   all the pᵢs and recurses on the inner layers.
split :: (Matching m) => MatchingState m -> m (Maybe HTm)
split (MatchingState ctx q ty cls) = do
  case cls of
    Clause (co : _, _, _) _ : _ -> case co of
      -- 1. This constraint is of the form Γ ⊢ [x = x'], where x and x' are variables.
      -- @@Check:  is it appropriate to just look at the first clause?
      SimpleConstraint _ _ (LvlP _ n _) p -> do
        -- All we need to do is remove the constraint from the clauses. @@Check: is this right?
        -- @@Todo: same quantity check?
        traceM $ " Got constraint name " ++ show n
        Just <$> caseTree (MatchingState ctx q ty (removeFirstConstraint cls))
      -- 2. This constraint is of the form Γx (x : D δ ψ) xΓ ⊢ [(x : D δ ψ) = (ck πk : D δ (ξk[δ,πk]))]
      SimpleConstraint _ x (CtorP _ _) p -> do
        pco <- pretty co
        debug $ "Splitting on constraint: " ++ pco

        -- Get the current subject type, i.e. D δ ψ
        (d, delta, psi) <- forceData ctx p.ty
        (di, dc) <- access (getDataGlobal' d)

        -- Create the spine (ψ, x)
        let psix = psi :|> Arg p.mode p.qty (HVar x)

        -- For each constructor ci (π : Πi [δ]) : D δ (ξi [δ,π]):
        elims <- forM di.ctors $ \c -> do
          -- Let Γ' = Γχ (x : D δ ψ) xΓ (π : Πi)
          (_, cc) <- access (getCtorGlobal' c)
          let (ctx', pi) = extendCtxWithTel ctx (\_ -> cc.args delta)
          cpat <- tmAsPat p.qty (hApp (HCtor (c, delta)) pi) -- Should never fail

          -- Create the spine (ξi[δ,π], ci π)
          let psix' = cc.returnIndices delta pi :|> Arg p.mode p.qty (hApp (HCtor (c, delta)) pi)

          -- Create the telescope (ρ : Ψ)(x : D δ ρ)
          let psiTel = extendTel (dc.indices delta) (Param p.mode p.qty p.name . hApp (HData d))

          traceM $ "Prev context is "
          pretty (hCtxToTel ctx) >>= traceM

          traceM $ "Current context is "
          pretty (hCtxToTel ctx') >>= traceM

          traceProblem ctx' psiTel psix psix'

          -- Unify:
          -- Γχ (x : D δ ψ) xΓ (π : Πi) ⊢ (ψ, x) =(ρ : Ψ)(D δ ρ)= (ξi[δ,π], ci π)
          --
          -- Gives back a bi-substitution σ to a new context Γ''
          (ctx'', eqSh, _, s) <- unifyPLSpines ctx' psiTel psix psix'

          -- @@Todo: if unification is negative, emit eliminator!

          -- For each clause with pattern πj, equate πj to π:
          cp <- pretty (hCtxToTel ctx)
          traceM $ "Context is " ++ cp
          cpa <- pretty (hCtxToTel ctx')
          traceM $ "Context with args is " ++ cpa
          cpu <- pretty (hCtxToTel ctx'')
          traceM $ "Context with unification is " ++ cpu
          traceM "This is by bi-substitution: "
          pretty s.forward >>= traceM . ("Forward: " ++)
          pretty s.backward >>= traceM . ("Backward: " ++)
          cls' <- fmap catMaybes $ mapM (refineClause s.forward) cls

          -- Build the rest of the clause in Γ'', which will first give:
          --    Γ'' |- e : T σ .
          e <- caseTree (MatchingState (sub s.forward ctx'') q (sub s.forward ty) cls')
          -- Through the substitution we can recover
          --    Γχ (x : D δ ψ) xΓ (π : Πi) ((ψ, x) = (ξi[δ,π], ci π)) |- e' = e σ⁻¹ : T ,
          -- bringing us back to the original context.
          let e' = sub s.backward e

          -- Now we build e'' which is:
          --    Γχ (x : D δ ψ) xΓ (π : Πi) |- e'' = (λ us . e' [us]) : Π ((ψ, x) = (ξi[δ,π], ci π)) T
          -- The equalities are explicitly given by the motive we will set up next.
          let eq = equalitySp psiTel psix psix'
          let e'' = hoistBinders' (telShapes ctx) cc.argsArity $ hLams eq (hoistBinders (telShapes ctx') eqSh e')

          -- The method is for constructor ci π
          return (Clause cpat (Just e''))

        -- Now we build the motive for the case.
        -- First, we have the required data indices and subject:
        --    (ψ' : Ψ[δ]) (x' : D δ ψ')
        let psixTe' = extendTel (dc.indices delta) (\psi' -> p {ty = hApp (HData d) (delta <> psi')})
        -- We also add the equalities between the subject and the data indices
        -- in the motive and the ones in the context.
        --    (ψ' : Ψ[δ]) (x' : D δ ψ') ((ψ, x) = (ψ', x'))
        let eq = equalitySp psixTe' psix
        let indTel = joinTels psixTe' eq

        -- We also need the reflexivity proofs to apply to the motive.
        --    refl [ψj] : Equal [Ψj] ψj ψj
        -- Where ψj = ψ1, ..., ψn, x
        let psixRefl = reflSp psixTe' psix

        let caseBase =
              Case
                { dat = d,
                  datParams = delta,
                  subject = HVar x,
                  subjectIndices = psi,
                  -- The final motive is:
                  --    Γχ (x : D δ ψ) xΓ  |-  (λ ψ' x'. (Π ((ψ, x) = (ψ', x')) T)) : Π (ψ' : Ψ[δ], x' : D δ ψ') U
                  elimTy = hLams indTel (const ty),
                  clauses = []
                }
        return . Just $ hApp (HCase (caseBase {clauses = elims})) psixRefl
    _ -> return Nothing

-- Typechecking (uses the `Typechecking` module)

-- Typecheck a pattern
tcPat :: (Matching m) => Child m -> HMode -> m (Pat, HTy, HCtx)
tcPat c mode = do
  mode' <- traverse embedEvalHere mode
  enterPat $ do
    (tm, ty) <- c mode'
    ctx' <- getCtx >>= unembedCtx
    q <- qty
    tm' <- unembedHere tm
    pat <- tmAsPat q tm'
    ty' <- quoteUnembedHere ty
    return (pat, ty', ctx')

-- Typecheck a term
tcTm :: (Matching m) => Child m -> HMode -> m (HTm, HTy)
tcTm c mode = do
  mode' <- traverse embedEvalHere mode
  (tm, ty) <- c mode'
  tm' <- unembedHere tm
  ty' <- quoteUnembedHere ty
  return (tm', ty')

-- Create a list of constrained HOAS clauses with empty constraints, from a
-- simple list of syntax clauses.
clausesWithEmptyConstraints ::
  (Matching m) =>
  Clauses (Child m) (Child m) ->
  ConstrainedClauses (HChildPat m) (HChildTm m)
clausesWithEmptyConstraints cls = flip map cls $ \(Clause ps r) ->
  let ps' = fmap (fmap (\p q ctx m -> runTc' q ctx (tcPat p m))) ps
   in let t' = fmap (\t q ctx m -> runTc' q ctx (tcTm t m)) r in Clause ([], Empty, ps') t'

-- Typecheck a list of syntax clauses, producing a
-- corresponding case tree using primitive eliminators.
clauses :: (Matching m) => DefGlobal -> Clauses (Child m) (Child m) -> VTy -> m (STm, VTy)
clauses _ cls ty = enterCtx id $ do
  hty <- quoteUnembedHere ty
  q <- view
  ct <- caseTree (MatchingState Empty q hty (clausesWithEmptyConstraints cls))
  ct' <- embedHere ct
  return (ct', ty)
