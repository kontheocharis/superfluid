{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Matching
  ( Matching (..),
    caseTree,
    clausesWithEmptyConstraints,
    MatchingState (..),
    clause,
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
    Lvl (..),
    Name (..),
    Param (..),
    PiMode (..),
    Qty (..),
    Spine,
    Tel,
    mapSpineM,
    nextLvl,
    spineShapes,
    telShapes,
    telToBinds, pattern Possible, pattern Impossible, mapSpine,
  )
import Constructions (ctorConstructions)
import Context
import Control.Applicative (asum)
import Control.Monad (forM)
import Control.Monad.Extra (firstJustM)
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable (Foldable (..), toList)
import Data.Map (Map)
import Data.Maybe (catMaybes, fromJust)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation
  ( Eval (..),
    ($$),
  )
import Globals
  ( CtorConstructions (..),
    CtorGlobalInfo (..),
    DataConstructions (..),
    DataGlobalInfo (..),
    KnownGlobal (KnownEqual, KnownRefl),
    Sig (..),
    getCtorGlobal,
    getDataGlobal,
    knownCtor,
    knownData,
  )
import Substitution (BiSub (..), Shapes, Sub (..), Subst (..), composeSub, extendSub, hoistBinder, hoistBinders, hoistBinders', hoistBindersSp, idSub, liftSubN, mapSub1, mapSubN, proj)
import Syntax
  ( Case (..),
    HCtx,
    HTel (HEmpty, HWithParam),
    HTm (..),
    HTy,
    Pat (..),
    SPat (..),
    STm (..),
    VNorm (..),
    VTm (..),
    VTy,
    embed,
    embedCase,
    embedTel,
    extendCtxWithTel,
    extendTel,
    hApp,
    hGatherApps,
    hLams,
    hPis,
    joinTels,
    sAppSpine,
    sLams,
    pattern VV, sGatherApps, sTmToPat,
  )
import Typechecking (Tc (..), Child, Mode (..), InPat (..), spine)
import Unification
import Prelude hiding (cycle, pi)

-- Proof relevant unification
--

data MatchingError = MatchingError

class (Eval m) => Matching m where
  throwUnifyError :: MatchingError -> m a
  target :: m VTm

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
type Unification = (HCtx, UnifyOutcome, BiSub)

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
      Can,
      BiSub
        { forward = idSub (telShapes ctx),
          backward = idSub (telShapes ctx)
        }
    )
unifyPLSpines ctx (HWithParam _ _ _ ty ts) (Arg _ q x :<| xs) (Arg _ q' y :<| ys) | q == q' = do
  -- Solving unify Γ ⊢ (x, ..xs) = (y, ..ys) : (_ : A)Δ

  -- (Γ', σ : Sub Γ' Γ(χ = y)) <- unify Γ A x y
  (ctx', o, s) <- unifyPL ctx ty x y

  -- (Γ'', σ' : Sub Γ'' Γ'(χs σ = ys σ)) <- unifySp Γ' ((Δ [x]) σ) (xs σ) (ys σ)
  (ctx'', o', s') <- unifyPLSpines ctx' (sub s.forward (ts x)) (sub s.forward xs) (sub s.forward ys)

  -- return (Γ'', (
  --     1 = lift (xs ..= ys) σ ∘ σ',
  --    -1 = σ'⁻¹ ∘ lift (xs σ⁻¹ ..= ys σ⁻¹) σ⁻¹
  -- ))
  return
    ( ctx'',
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
    Nothing -> throwUnifyError MatchingError

-- Proof-relevant unification tactics

solution :: (Matching m) => HCtx -> HTy -> HTm -> HTm -> m (Maybe Unification)
solution ctx ty a b = case (a, b) of
  (_, HVar x) -> solution ctx ty (HVar x) a
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
        return $ Just (ctx', Can, s)
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
    ci <- access (getCtorGlobal c)
    let cc = fromJust ci.constructions
    let n = cc.argsArity

    -- (Γ', σ : BiSub Γ' Γ(xs ..= ys)) <- unify Γ xs ys
    (ctx', o, s) <- unifyPLSpines ctx (cc.args pp) xs ys

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
          Can,
          BiSub {forward = extendSub (idSub sh) csh (\_ -> refl ty a), backward = proj (idSub (sh :|> csh))}
        )
    else
      return Nothing

type ConstrainedClauses pat tm = [ConstrainedClause (Spine pat) tm]

type ConstrainedClause pats tm = Clause (Constraints, pats) tm

type NextPat pat tm = (Maybe [pat], ConstrainedClauses pat tm) -- nonempty

clausesWithEmptyConstraints :: Clauses SPat STm -> ConstrainedClauses Pat HTm
clausesWithEmptyConstraints = undefined

nextPat :: (Matching m) => ConstrainedClauses pat tm -> m (NextPat pat tm)
nextPat = undefined

type Matches m = Map CtorGlobal [(Sub, [m (HTm, HTy)])]

equateSpines :: (Matching m) => Spine HTm -> Spine HTm -> m Sub
equateSpines = undefined

equateTerms :: (Matching m) => HTm -> HTm -> m Sub
equateTerms = undefined

enterSub :: (Matching m) => Sub -> m a -> m a
enterSub = undefined

class ApplySub m where
  applySub :: Sub -> m -> m

instance ApplySub VTm where
  applySub = undefined

instance (ApplySub a) => ApplySub (Spine a) where
  applySub = undefined

instance (ApplySub a, ApplySub b) => ApplySub (Clause a b) where
  applySub = undefined

binder :: (Has m Ctx) => PiMode -> Qty -> Name -> VTy -> (Lvl -> m a) -> m a
binder m q x a f = do
  l <- getLvl
  enterCtx (bind m x q a) $ f l

forceData :: (Matching m) => HTm -> m (DataGlobal, Spine HTm, Spine HTm)
forceData d = undefined

-- unifyPrfRelSp : (a : Tms Γ T) -> (b : Tms Γ T) -> (Γ' : Ctx) * (Γ' ~= Γ (a = b)) * m [enter Γ'] ()
unifyPrfRelSp :: (Matching m) => Spine HTm -> Spine HTm -> m ()
unifyPrfRelSp = undefined

unifyPrfRel :: (Matching m) => HTm -> HTm -> m ()
unifyPrfRel = undefined

canUnifyPrfRel :: (Matching m) => HTm -> HTm -> m CanUnify
canUnifyPrfRel = undefined

enterHTel :: (Matching m) => HTel -> (Spine HTm -> m a) -> m a
enterHTel = undefined

getDataGlobal' :: DataGlobal -> Sig -> (DataGlobalInfo, DataConstructions)
getDataGlobal' = undefined

getCtorGlobal' :: CtorGlobal -> Sig -> (CtorGlobalInfo, CtorConstructions)
getCtorGlobal' = undefined

eqTel :: Spine HTm -> Spine HTm -> HTel
eqTel = undefined

reflSp :: HTel -> Spine HTm -> Spine HTm
reflSp = undefined

patAsTm :: Pat -> HTm
patAsTm = undefined

tmAsPat :: HTm -> Pat
tmAsPat = undefined

joinConstraints :: Constraints -> Constraints -> Constraints
joinConstraints = undefined

constraints :: HCtx -> Spine HTm -> Spine Pat -> m Constraints
constraints = undefined

simpleConstraint :: HTm -> Pat -> m Constraint
simpleConstraint = undefined

data Constraint = Constraint {lvl :: Lvl, lhs :: HTm, rhs :: Pat, param :: Param HTy}

data Constraints = Constraints {list :: [Constraint]}

emptyConstraints :: Constraints
emptyConstraints = Constraints []

addConstraint :: Constraint -> ConstrainedClause (Spine Pat) HTm -> ConstrainedClause (Spine Pat) HTm
addConstraint c (Clause (Constraints cs, sp) t) = Clause (Constraints (c : cs), sp) t

nextConstraint :: Constraints -> Maybe (Constraint, Constraints)
nextConstraint (Constraints []) = Nothing

data MatchingState = MatchingState
  { ctx :: HCtx,
    ty :: HTy,
    cls :: [Clause (Constraints, Spine Pat) HTm]
  }

caseTree :: (Matching m) => MatchingState -> m HTm
caseTree c = do
  let tactics = [addVar c, splitConstraint c]
  result <- asum <$> sequence tactics
  case result of
    Just r -> return r
    Nothing -> error "no case tree tactic matched"

ifForcePi :: (Matching m) => HTy -> m a -> (Param HTy -> (HTm -> HTy) -> m a) -> m a
ifForcePi = undefined

addVar :: (Matching m) => MatchingState -> m (Maybe HTm)
addVar (MatchingState ctx ty cls) = do
  (ps, _) <- nextPat cls
  case ps of
    Nothing -> return Nothing
    Just _ -> do
      ifForcePi ty (return Nothing) $ \(Param m q x a) b -> do
        -- We have the goal
        -- Γ ⊢ cs Q ~> e : (x : A) -> B
        --
        -- We add (x : A) to the context and then recurse:
        --    Γ (x : A) ⊢ cs Q ~> e' : B
        -- Finally we can construct the goal as
        --    Γ ⊢ cs Q ~> λ t. e' (id,t) : (x : A) -> B
        let s t = extendSub (idSub (telShapes ctx)) (Param m q x ()) (hoistBinders (length ctx) t)
        rest <- caseTree (MatchingState (ctx :|> Param m q x a) (b (HVar (Lvl $ length ctx))) cls)
        return . Just $ HLam m q x (\t -> sub (s t) rest)

splitConstraint :: (Matching m) => MatchingState -> m (Maybe HTm)
splitConstraint (MatchingState ctx ty cls) = do
  -- In context Γ (ctx), and return type T (ty) we have a list of clauses Q and constraints cs.
  -- Γ ⊢ cs Q ~> e : T
  case cls of
    Clause (Constraints (co : _), _) _ : clss -> case co of
      -- 1. We have the constraint Γ ⊢ x = t : T in the first clause.
      --
      -- 1.1. This constraint is of the form Γ ⊢ x = x' : T, where x and x' are variables.
      -- @@Check:  is it appropriate to just look at the first clause?
      Constraint _ (HVar x) (LvlP _ _ x') param -> do
        -- This will use the solution rule for the constraint x = x'
        (ctx', _, s) <- unifyPL ctx param.ty (HVar x) (HVar x')
        Just <$> caseTree (MatchingState ctx' (sub s.forward ty) clss)
      -- 1.2. This constraint is of the form Γx (x : D δ ψ) xΓ ⊢ (x : D δ ψ) = (ck πk : D δ (ξk[δ,πk]))
      Constraint _ (HVar x) (CtorP _ _) p -> do
        -- Get the current subject type, i.e. D δ ψ
        (d, delta, psi) <- forceData p.ty
        (di, dc) <- access (getDataGlobal' d)

        -- Create the spine (ψ, x)
        let psix = psi :|> Arg p.mode p.qty (HVar x)

        -- For each constructor ci (π : Πi [δ]) : D δ (ξi [δ,π]):
        elims <- forM di.ctors $ \c -> do
          -- Let Γ' = Γχ (x : D δ ψ) xΓ (π : Πi)
          (_, cc) <- access (getCtorGlobal' c)
          let (ctx', pi) = extendCtxWithTel ctx (\_ -> cc.args delta)
          let cpat = tmAsPat (hApp (HCtor (c, delta)) pi)

          -- For each clause with pattern πj, equate πj to π:
          children <- fmap catMaybes . forM cls $ \cl' -> do
            case cl' of
              Clause (Constraints [], _) _ -> return Nothing -- @@Check: is this right?
              Clause (Constraints (Constraint _ _ (LvlP _ _ y) _ : cs'), ps) t -> do
                newConstraint <- simpleConstraint (HVar y) cpat
                return . Just $ Clause (Constraints (newConstraint : cs'), ps) t
              Clause (Constraints (Constraint _ _ (CtorP (cj, _) _) _ : _), _) _ | cj /= c -> return Nothing
              Clause (Constraints (Constraint _ _ (CtorP _ pij) _ : cs'), ps) t -> do
                -- We have Γχ (x : D δ ψ) xΓ (π : Πi) ⊢ πj : D δ ξi[δ,πj] by weakening.
                -- (which we get for free since we are using deBrujin levels.)
                --
                -- We now generate the constraints π = πj and add them to the clause.
                newConstraints <- constraints ctx' pi pij
                return . Just $ Clause (joinConstraints newConstraints (Constraints cs'), ps) t

          -- Create the spine (ξi[δ,π], ci π)
          let psix' = cc.returnIndices delta pi :|> Arg p.mode p.qty (hApp (HCtor (c, delta)) pi)

          -- Create the telescope (ρ : Ψ)(x : D δ ρ)
          let psiTel = extendTel dc.params (Param p.mode p.qty p.name . hApp (HData d))

          -- Unify:
          -- Γχ (x : D δ ψ) xΓ (π : Πi) ⊢ (ψ, x) =(ρ : Ψ)(D δ ρ)= (ξi[δ,π], ci π)
          --
          -- Gives back a bi-substitution σ to a new context Γ''
          -- @@Todo: do we care about status?
          (ctx'', _, s) <- unifyPLSpines ctx' psiTel psix psix'

          -- Build the rest of the clause in Γ'', which will first give:
          --    Γ'' |- e : T σ .
          e <-
            caseTree
              ( MatchingState
                  (sub s.forward ctx'')
                  (sub s.forward ty)
                  (mapClauses (sub s.forward) children)
              )
          -- Through the substitution we can recover
          --    Γχ (x : D δ ψ) xΓ (π : Πi) ((ψ, x) = (ξi[δ,π], ci π)) |- e' = e σ⁻¹ : T ,
          -- bringing us back to the original context.
          let e' = sub s.backward e

          -- Now we build e'' which is:
          --    Γχ (x : D δ ψ) xΓ (π : Πi) |- e'' = (λ us . e' [us]) : Π ((ψ, x) = (ξi[δ,π], ci π)) T
          -- The equalities are explicitly given by the motive we will set up later.
          let eq = eqTel psix psix'
          let e'' = hoistBinders' (length pi) $ hLams eq (hoistBinders (length psix) e')

          -- The method is for constructor ci π
          return (Clause cpat (Just e''))

        -- Now we build the motive for the case.
        -- First, we have the required data indices and subject:
        --    (ψ' : Ψ[δ]) (x' : D δ ψ')
        let psixTe' = extendTel (dc.indices delta) (\psi' -> p {ty = hApp (HData d) (delta <> psi')})
        -- We also add the equalities between the subject and the data indices
        -- in the motive and the ones in the context.
        --    (ψ' : Ψ[δ]) (x' : D δ ψ') ((ψ, x) = (ψ', x'))
        let eq = eqTel psix
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
                  subjectIndices = psi, -- @@Todo: the xΓ is not getting quantified properly here (and neither is the ty)
                  -- The final motive is:
                  --    Γχ (x : D δ ψ)  |-   λ ψ' x'. Π ((ψ, x) = (ψ', x'), xΓ) T   :   Π (ψ' : Ψ[δ], x' : D δ ψ') U
                  elimTy = hLams indTel (const ty),
                  clauses = []
                }
        return . Just $ hApp (HCase (caseBase {clauses = elims})) psixRefl
      _ -> return Nothing
    _ -> return Nothing

mapClauses :: (HTm -> HTm) -> [Clause (Constraints, Spine Pat) HTm] -> [Clause (Constraints, Spine Pat) HTm]
mapClauses = undefined

clause :: (Tc m) => (STm, VTy) -> Clause (Spine (Child m)) (Child m) -> m (Clause (Spine SPat) STm)
clause (_, ty) (Possible Empty t) = do
  (t', _) <- t (Check ty)
  return $ Possible Empty t'
clause _ (Impossible Empty) = return $ Impossible Empty
clause (tm, ty) (Possible ps t) = do
  (ret, retTy) <- enterPat (InPossiblePat []) $ spine (tm, ty) ps
  (t', _) <- t (Check retTy)
  let (_, sp) = sGatherApps ret
  let spp = mapSpine sTmToPat sp
  return $ Possible spp t'
clause _ (Impossible _) = do
  return undefined -- @@Todo
  -- (ret, retTy) <- enterPat (InPossiblePat []) $ spine (tm, ty) ps

clauses :: (Tc m) => DefGlobal -> Clauses (Child m) (Child m) -> VTy -> m (STm, VTy)
clauses d cls ty = enterCtx id $ do
  -- Strategy:
  -- - First we typecheck each clause
  -- - Then we turn to case tree
  -- - Invariant: in empty ctx
  cls' <- mapM (clause (SDef d, ty)) cls
  hty <- quoteHere ty >>= unembedHere
  ct <- runMatching $ caseTree (MatchingState Empty hty (clausesWithEmptyConstraints cls'))
  ct' <- embedHere ct
  return (ct', ty)

runMatching :: (forall n. (Matching n) => n a) -> (forall m. (Tc m) => m a)
runMatching _ = undefined
