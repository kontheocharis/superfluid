{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
    DataGlobal (..),
    DefGlobal,
    Has (..),
    HasNameSupply (uniqueName),
    Loc,
    Lvl (..),
    Name (..),
    Param (..),
    PiMode (..),
    Qty (..),
    Spine,
    nextLvl,
    spineShapes,
    telShapes,
  )
import Context
import Context (unembedClosure1Here)
import Control.Applicative (asum)
import Control.Monad (forM)
import Control.Monad.Extra (firstJustM)
import Data.Foldable (Foldable (..), toList)
import Data.Maybe (catMaybes)
import Data.Semiring (Semiring (times))
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Data.Traversable (for)
import Evaluation
  ( Eval (..),
    embedEval,
    ifIsData,
    quoteUnembed,
  )
import Globals
  ( CtorConstructions (..),
    DataConstructions (..),
    DataGlobalInfo (..),
    KnownGlobal (KnownEqual, KnownRefl),
    getCtorGlobal',
    getDataGlobal,
    getDataGlobal',
    knownCtor,
    knownData,
  )
import Substitution
  ( BiSub (..),
    Shape,
    Shapes,
    Sub (..),
    Subst (..),
    composeSub,
    extendSub,
    hoistBinders,
    hoistBinders',
    idSub,
    liftSubN,
    mapSub1,
    mapSubN,
    proj,
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
    extendCtxWithTel,
    extendTel,
    hApp,
    hGatherApps,
    hLams,
    joinTels,
    lastVar,
  )
import Typechecking (Child, InPat (InPat), ModeG (..), Tc (..), ifForcePiType)
import Prelude hiding (cycle, pi)

data MatchingError = MatchingError

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
refl ty = HApp Explicit Zero (HCtor (knownCtor KnownRefl, S.singleton (Arg Implicit Zero ty)))

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
hequality = undefined

-- Equality for spines (Written δ =Δ= γ for a telescope Δ and spines δ γ : Tms Δ)
--
-- (() =()= ()) := ()
-- ((x,xs) =(x : A),Δ= (y,ys)) := (e : x =A= y, xs =Δ,e= ys)
--
equalitySp :: HTel -> Spine HTm -> Spine HTm -> HTel
equalitySp = undefined

-- Reflexivity for spines
reflSp :: HTel -> Spine HTm -> Spine HTm
reflSp = undefined

-- equalitySp HEmpty Empty Empty = HEmpty
-- equalitySp (HWithParam m _ nt tt delta) (Arg _ _ x :<| xs) (Arg _ _ y :<| ys) =
--   HWithParam m Zero (Name (nt.unName ++ "-eq")) (equality tt x y) (\e -> equalitySp' (x, y, e) delta xs ys)
-- equalitySp _ _ _ = error "Mismatching spines should never occur in well-typed terms"

-- equalitySp' :: (HTm, HTm, HTm, HTm) -> (HTm -> HTel) -> Spine HTm -> Spine HTm -> HTel
-- equalitySp' (s, t, e, p) (($ p) -> HEmpty) Empty Empty = HEmpty
-- equalitySp' (s, t, e, p) (($ t) -> (HWithParam m _ nt tt delta)) (Arg _ _ x :<| xs) (Arg _ _ y :<| ys) =
--   HWithParam
--     m
--     Zero
--     (Name (nt.unName ++ "-heq"))
--     (hequality s t e p x y)
--     (\e' -> equalitySp' (x, y, e', delta y) delta xs ys)
-- equalitySp' _ _ _ _ = error "Mismatching spines should never occur in well-typed terms"

-- dcong : (f : Tm Γ (Π A Τ)) -> {x y : Tm Γ A} -> Tms Γ (x = y) -> Tms Γ (f x = f y)
dcong :: (HTm -> HTm) -> HTm -> HTm
dcong = undefined

-- dcongSp : (f : Tm Γ (Πs Δ Τ)) -> {xs ys : Tms Γ Δ} -> Tms Γ (xs ..= ys) -> Tm Γ (f xs = f ys)
dcongSp :: (Spine HTm -> HTm) -> Spine HTm -> HTm
dcongSp = undefined

-- inj : (c : Ctor D Δ Π ξ) -> {δ : Δ} {xs ys : Tms Γ (Π [δ])} -> Tm Γ (c xs = c ys) -> Tms Γ (xs ..= ys)
inj :: HTm -> HTm -> Spine HTm
inj = undefined

-- conf : (c1 : Ctor D Δ Π₁, c2 : Ctor D Δ Π₂ ξ₂) -> {xs : Tms  ys : Tms Γ Π}
--            -> Tm Γ (c1 xs = c2 ys)
--            -> Tm Γ Empty
conf :: HTm -> HTm -> HTm -> HTm
conf = undefined

-- @@Todo: properly encode the < relation
-- cyc : (x t : D δ ψ) -> {{auto _ : x < t}} -> Tm Γ (x = t) -> Tm Γ Empty
cyc :: HTm -> HTm -> HTm -> HTm
cyc = undefined

-- Never
--
-- This is the internal Empty type's eliminator.
--
-- Important: 'internal Empty' means void in the metatheory, because the Unit
-- type behaves like the empty context instead.
--
-- never : [A : Ty Γ] -> Tm Γ Empty -> Tm Γ A
void :: HTm -> HTm
void = undefined

voidSh :: Shapes
voidSh = Param Explicit Many (Name "_") () :<| Empty

voidCtx :: HCtx
voidCtx = undefined

initialSub :: Shapes -> Shapes -> Sub
initialSub vSh sh = mapSub1 vSh sh (\_ x -> fmap (\p -> Arg p.mode p.qty (void x)) sh)

ofSh :: Shapes -> [a] -> Spine a
ofSh sh xs = foldr (\(Param m q _ (), t) sp -> Arg m q t :<| sp) Empty (zip (toList sh) xs)

-- Definitional equality checker. This should somehow hook into the other
-- unification thing. (And the latter should be renamed to convert?)
canConvert :: (Matching m) => HCtx -> HTm -> HTm -> m Bool
canConvert = undefined

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
unifyPLSpines ctx (HWithParam _ _ _ ty ts) (Arg _ q x :<| xs) (Arg _ q' y :<| ys) | q == q' = do
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
          backward = composeSub s.backward (liftSubN (spineShapes xs) s'.backward)
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
                            <> ofSh (S.singleton xSh) [b]
                            <> sp'
                            <> ofSh (S.singleton csh) [refl ty b]
                      )
                }
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
    (_, cc) <- access (getCtorGlobal' c)
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
                  (\sp ps -> sp :|> Arg Explicit Many (dcongSp (hApp (HCtor (c, pp))) ps)),
              backward =
                mapSub1
                  (sh :|> csh)
                  (sh <> n)
                  (\sp p -> sp <> inj (HCtor (c, pp)) p)
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
  ((HCtor (c1, pp), _), (HCtor (c2, _), _)) | c1 /= c2 -> do
    -- Γ ⊢ (c1 xs : D δ ξ[xs]) =? (c2 ys : D δ ξ[ys])
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
          { forward = initialSub voidSh (sh :|> csh),
            backward = mapSub1 (sh :|> csh) voidSh (\_ p -> ofSh voidSh [conf (HCtor (c1, pp)) (HCtor (c2, pp)) p])
          }
      )
  _ -> return Nothing

cycle :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m (Maybe Unification)
cycle ctx ty a b = case (a, b) of
  (_, HVar x) -> cycle ctx ty (HVar x) a
  (HVar x, hGatherApps -> (HCtor (c, pp), xs)) -> do
    -- Check if x occurs in xs, if so, then we have a cycle.
    let l = Lvl (length ctx)
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
              { forward = initialSub voidSh (sh :|> csh),
                backward = mapSub1 (sh :|> csh) voidSh (\_ p -> ofSh voidSh [cyc (hApp (HCtor (c, pp)) xs) (HVar x) p])
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

type ConstrainedClause pats tm = Clause (SimpleConstraints, pats) tm

-- Constraints

data Constraint = Constraint
  { lvl :: Lvl,
    lhs :: HTm,
    rhs :: Pat,
    param :: Param HTy
  }

data SimpleConstraint = SimpleConstraint
  { lvl :: Lvl,
    lhs :: Lvl,
    rhs :: Pat,
    param :: Param HTy
  }

type Constraints = [Constraint]

type SimpleConstraints = [SimpleConstraint]

instance Subst Constraint where
  sub s (Constraint l x p q) = Constraint l (sub s x) p q -- @@Todo: subst in pat or remove data params from pat!
  occurs l f (Constraint _ y _ _) = occurs l f y -- @@Todo: occurs in pat??

subSimpleConstraint :: Sub -> SimpleConstraint -> Constraint
subSimpleConstraint s (SimpleConstraint l x p q) = sub s (Constraint l (HVar x) p q)

simplifyConstraints :: (Matching m) => Constraints -> m (Maybe SimpleConstraints)
simplifyConstraints cs = mconcat <$> mapM simplifyConstraint cs

simplifyConstraint :: (Matching m) => Constraint -> m (Maybe SimpleConstraints)
simplifyConstraint co = do
  case co of
    Constraint l (HVar x) p q -> return . Just $ [SimpleConstraint l x p q]
    Constraint l (hGatherApps -> (HCtor (c, _), sp)) (CtorP (c', _) sp') q
      | c == c' ->
          simplifyConstraints
            (zipWith (\x y -> Constraint l x.arg y.arg q) (toList sp) (toList sp'))
      | otherwise -> return Nothing
    _ -> return Nothing

refineClause :: (Matching m) => Sub -> ConstrainedClause p t -> m (Maybe (ConstrainedClause p t))
refineClause s cl' = case cl' of
  Clause (cs, ps) t -> do
    cs' <- simplifyConstraints (map (subSimpleConstraint s) cs)
    case cs' of
      Just cs'' -> return . Just $ Clause (cs'', ps) t
      Nothing -> return Nothing

-- Matching

type HMode = ModeG HTy

type HChildTm m = Qty -> HCtx -> HMode -> m (HTm, HTy)

type HChildPat m = Qty -> HCtx -> HMode -> m (Pat, HTy)

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
  ty' <- embedEvalHere ty
  ifForcePiType
    m
    ty'
    ( \m' q' x a b -> do
        a' <- quoteUnembedHere a
        b' <- unembedClosure1Here b
        the (Param m' q' x a') b'
    )
    (\_ _ _ _ _ -> els) -- @@Todo: errors

-- Check if clauses C are of the form (csᵢ (pᵢ psᵢ) -> tᵢ)ᵢ
hasNextPat :: (Matching m) => ConstrainedClauses ps ts -> m (Maybe (Arg ()))
hasNextPat cls = do
  case cls of
    Clause (_, Empty) _ : _ -> return Nothing
    Clause (_, a :<| _) _ : _ -> return . Just $ a {arg = ()}
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
  -- First we add all the variables to the context
  -- Then once we can't anymore, we split on the first-added constraint
  -- Once all the constraints are solved, we can typecheck the right-hand
  -- side of the first clause that matches.
  let tactics = [addVar c, splitConstraint c, done c]
  result <- asum <$> sequence tactics
  case result of
    Just r -> return r
    Nothing -> error "no case tree tactic matched"

-- There is no next pattern and the constraints have been solved:
--
-- Γ ⊢ C ~> e : B and C = ([] ϵ -> tᵢ)ᵢ
--
-- We simply take the first clause and typecheck its term.
done :: (Matching m) => MatchingState m -> m (Maybe HTm)
done (MatchingState ctx q ty cls) = do
  case cls of
    Clause ([], Empty) (Just tm) : _ -> do
      -- @@Todo: qty
      (tm', _) <- tm q ctx (Check ty)
      return (Just tm')
    _ -> return Nothing

-- Given a 'constraint scheme' (p . [x = p]), i.e. a constraint parametrized by
-- a pattern, and an argument type `ty`,  apply this constraint to the first
-- pattern of each clause in C.
addNextConstraint ::
  (Matching m) =>
  MatchingState m ->
  Param HTy ->
  (Pat -> SimpleConstraint) ->
  ConstrainedClauses (HChildPat m) (HChildTm m) ->
  m (ConstrainedClauses (HChildPat m) (HChildTm m))
addNextConstraint st param f cls = forM cls $ \case
  (Clause (cs, p :<| ps) t) -> do
    -- @@Todo: deal with implicits
    (p', _) <- p.arg (st.qty `times` param.qty) st.ctx (Check param.ty)
    return $ Clause (cs ++ [f p'], ps) t
  (Clause (_, Empty) _) -> error "No next pattern to add constraint to"

-- Given a list of clauses C, remove the first constraint from each clause.
removeFirstConstraint :: ConstrainedClauses (HChildPat m) (HChildTm m) -> ConstrainedClauses (HChildPat m) (HChildTm m)
removeFirstConstraint = map $ \case
  (Clause (_ : cs, ps) t) -> Clause (cs, ps) t
  (Clause ([], _) _) -> error "No constraints to remove"

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
addVar :: (Matching m) => MatchingState m -> m (Maybe HTm)
addVar st@(MatchingState ctx q' ty cls) = do
  ps <- hasNextPat cls
  case ps of
    Nothing -> return Nothing
    -- @@Todo: if the args don't match in PiMode, insert!
    Just (Arg m' _ ()) -> do
      ifForcePi
        q'
        ctx
        m'
        ty
        ( \p@(Param m q x a) b -> do
            let ctxShapes = telShapes ctx
            let s t = extendSub (idSub ctxShapes) (Param m q x ()) (hoistBinders Empty ctxShapes t)
            let ctx' = ctx :|> Param m q x a
            let b' = b (HVar (lastVar ctx'))
            cls' <- addNextConstraint st p (\pt -> SimpleConstraint (ctxSize ctx') (lastVar ctx') pt p) cls -- implicit weakening everywhere!
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
splitConstraint :: (Matching m) => MatchingState m -> m (Maybe HTm)
splitConstraint (MatchingState ctx q ty cls) = do
  case cls of
    Clause (co : _, _) _ : clss -> case co of
      -- 1. This constraint is of the form Γ ⊢ [x = x'], where x and x' are variables.
      -- @@Check:  is it appropriate to just look at the first clause?
      SimpleConstraint _ _ (LvlP _ _ _) _ -> do
        -- All we need to do is remove the constraint from the clauses. @@Check: is this right?
        -- @@Todo: same quantity check?
        Just <$> caseTree (MatchingState ctx q ty (removeFirstConstraint clss))
      -- 2. This constraint is of the form Γx (x : D δ ψ) xΓ ⊢ [(x : D δ ψ) = (ck πk : D δ (ξk[δ,πk]))]
      SimpleConstraint _ x (CtorP _ _) p -> do
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
          let psiTel = extendTel dc.params (Param p.mode p.qty p.name . hApp (HData d))

          -- Unify:
          -- Γχ (x : D δ ψ) xΓ (π : Πi) ⊢ (ψ, x) =(ρ : Ψ)(D δ ρ)= (ξi[δ,π], ci π)
          --
          -- Gives back a bi-substitution σ to a new context Γ''
          (ctx'', eqSh, _, s) <- unifyPLSpines ctx' psiTel psix psix'

          -- @@Todo: if unification is negative, emit eliminator!

          -- For each clause with pattern πj, equate πj to π:
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
tcPat :: (Matching m) => Child m -> HMode -> m (Pat, HTy)
tcPat c mode = do
  mode' <- traverse embedEvalHere mode
  (tm, ty) <- enterPat $ c mode'
  tm' <- unembedHere tm
  ty' <- quoteUnembedHere ty
  q <- qty
  pat <- tmAsPat q tm'
  return (pat, ty')

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
   in let t' = fmap (\t q ctx m -> runTc' q ctx (tcTm t m)) r in Clause ([], ps') t'

-- Typecheck a list of syntax clauses, producing a
-- corresponding case tree using primitive eliminators.
clauses :: (Matching m) => DefGlobal -> Clauses (Child m) (Child m) -> VTy -> m (STm, VTy)
clauses _ cls ty = enterCtx id $ do
  hty <- quoteUnembedHere ty
  q <- view
  ct <- caseTree (MatchingState Empty q hty (clausesWithEmptyConstraints cls))
  ct' <- embedHere ct
  return (ct', ty)
