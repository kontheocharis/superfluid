{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Matching
  ( Matching (..),
    caseTree,
    clausesWithEmptyConstraints,
    MatchingState (..),
  )
where

import Algebra.Lattice (Lattice (..), (/\))
import Common
  ( Arg (..),
    Clause (..),
    Clauses,
    CtorGlobal (..),
    DataGlobal (..),
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
    telToBinds,
  )
import Constructions (ctorConstructions)
import Context
import Control.Applicative (asum)
import Control.Monad (forM)
import Control.Monad.Extra (firstJustM)
import Data.Bifunctor (Bifunctor (..))
import Data.Foldable (Foldable (..), toList)
import Data.Map (Map)
import Data.Maybe (catMaybes)
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
    knownCtor,
    knownData,
  )
import Substitution (BiSub (..), Shapes, Sub (..), Subst (..), composeSub, extendSub, idSub, liftSubN, mapSub1, mapSubN, proj)
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
    extendTel,
    hApp,
    hGatherApps,
    hLams,
    joinTels,
    sAppSpine,
    sLams,
    pattern VV,
  )
import Unification
import Prelude hiding (cycle, pi)

-- Proof relevant unification
--

data MatchingError = MatchingError

class (Eval m, Has m Ctx) => Matching m where
  throwUnifyError :: MatchingError -> m a

  target :: m VTm

-- The unify outcome is a "decorated" bit that tells us whether the unification
-- was successful or not.
data UnifyOutcome = Can | Cannot [MatchingError]

-- A unification between terms a, b : Tm Γ A is a telescope Γ' and an
-- invertible (with coherence proofs definitionally equal to refl)
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

-- Higher equality (written as `=`)
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
hequality :: HTm -> HTm -> HTm -> HTm -> HTm -> HTm
hequality = undefined

-- Higher equality for spines
--
-- (() =()= ()) := ()
-- ((x,xs) =(x : A)Δ= (y,ys)) := (e : x =A= y, xs =Δ[e]= ys)
--
equalitySp :: HTel -> Spine HTm -> Spine HTm -> HTel
equalitySp HEmpty Empty Empty = HEmpty
equalitySp (HWithParam m _ nt tt delta) (Arg _ _ x :<| xs) (Arg _ _ y :<| ys) =
  HWithParam m Zero (Name (nt.unName ++ "-eq")) (equality tt x y) (\e -> equalitySp (delta e) xs ys)
equalitySp _ _ _ = error "Mismatching spines should never occur in well-typed terms"

-- dcong : (f : Tm Γ (Π A Τ)) -> {x y : Tm Γ A} -> Tms Γ (x = y) -> Tms Γ (f x = f y)
dcong :: (HTm -> HTm) -> HTm -> HTm
dcong = undefined

-- dcongSp : (f : Tm Γ (Πs Δ Τ)) -> {xs ys : Tms Γ Δ} -> Tms Γ (xs ..= ys) -> Tm Γ (f xs = f ys)
dcongSp :: (Spine HTm -> HTm) -> Spine HTm -> HTm
dcongSp = undefined

-- noConf : (c : Ctor D Δ Π ξ) -> {xs ys : Tms Γ Π} -> Tm Γ (c xs = c ys) -> Tms Γ (xs ..= ys)
noConf :: HTm -> HTm -> Spine HTm
noConf = undefined

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

unifyPLSpines :: (Matching m) => HCtx -> Spine HTm -> Spine HTm -> m Unification
unifyPLSpines ctx Empty Empty = do
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
unifyPLSpines ctx (Arg _ q x :<| xs) (Arg _ q' y :<| ys) | q == q' = do
  -- Solving unify Γ (x, ..xs) (y, ..ys)

  -- (Γ', σ : Sub Γ' Γ(χ = y)) <- unify Γ x y
  (ctx', o, s) <- unifyPL ctx x y

  -- (Γ'', σ' : Sub Γ'' Γ'(χs σ = ys σ)) <- unifySp Γ' (xs σ) (ys σ)
  (ctx'', o', s') <- unifyPLSpines ctx' (sub s.forward xs) (sub s.forward ys)

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
unifyPLSpines _ _ _ = error "Mismatching spines should never occur in well-typed terms"

unifyPL :: (Matching m) => HCtx -> HTm -> HTm -> m Unification
unifyPL ctx t1 t2 = do
  let tactics = [solution, injectivity, conflict, cycle, deletion]
  res <- firstJustM (\t -> t ctx t1 t2) tactics
  case res of
    Just x -> return x
    Nothing -> throwUnifyError MatchingError

-- Proof-relevant unification tactics

solution :: (Matching m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
solution ctx a b = case (a, b) of
  (_, HVar x) -> solution ctx (HVar x) a
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
                            <> ofSh (S.singleton csh) [refl b]
                      )
                }
        return $ Just (ctx', Can, s)
  _ -> return Nothing

injectivity :: (Matching m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
injectivity ctx a b = case (hGatherApps a, hGatherApps b) of
  ((HCtor (c1, pp), xs), (HCtor (c2, _), ys)) | c1 == c2 -> do
    -- Assume : length xs = length ys = n
    -- Assume:  Data params are equal
    -- Reason : Terms are well-typed *and* fully eta-expanded
    let sh = telShapes ctx
    let c = c1
    cc <- access (getCtorGlobal c) >>= ctorConstructions
    let n = cc.argsArity

    -- (Γ', σ : Sub Γ' Γ(xs ..= ys)) <- unify Γ xs ys
    (ctx', o, s) <- unifyPLSpines ctx xs ys

    -- Make a new name and shape for the new context
    x <- uniqueName
    let csh = Param Explicit Many x ()

    -- Now we need to construct an invertible substitution:
    --
    -- σ : Sub Γ(xs ..= ys) Γ(c xs = c ys)
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
                  (\sp p -> sp <> noConf (HCtor (c, pp)) p)
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

conflict :: (Matching m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
conflict ctx a b = case (hGatherApps a, hGatherApps b) of
  ((HCtor (c1, pp), _), (HCtor (c2, _), _)) | c1 /= c2 -> do
    let sh = telShapes ctx
    -- Here we have (c1 : Ctor D Δ Π₁ ξ₁, c2 : Ctor D Δ Π₂ ξ₂)
    -- And we are trying to unify (c1 xs = c2 ys).
    --
    -- This is a conflict, so we need to return a disunifier.

    -- Make a new name and shape for the new context
    x <- uniqueName
    let csh = Param Explicit Many x ()

    -- We return an invertible substitution:
    --
    -- σ : Sub ⊥ Γ(c1 xs = c2 ys)
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

cycle :: (Matching m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
cycle ctx a b = case (a, b) of
  (_, HVar x) -> cycle ctx (HVar x) a
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
        -- σ : Sub ⊥ Γ(x = c xs)
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

deletion :: (Matching m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
deletion ctx a b = do
  let sh = telShapes ctx
  -- If we can unify a and b we can delete the equation since it will evaluate to refl.
  c <- canConvert ctx a b

  -- Make a new name and shape for the new context
  x <- uniqueName
  let csh = Param Explicit Many x ()

  -- More precisely, we return an invertible substitution:
  --
  -- σ : Sub Γ Γ(a = a)
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
          BiSub {forward = extendSub (idSub sh) csh (\_ -> refl a), backward = proj (idSub (sh :|> csh))}
        )
    else
      return Nothing

type ConstrainedClauses pat tm = [ConstrainedClause (Spine pat) tm]

type ConstrainedClause pats tm = Clause (Constraints, pats) tm

type NextPat pat tm = (Maybe [pat], ConstrainedClauses pat tm) -- nonempty

clausesWithEmptyConstraints :: Clauses a b -> ConstrainedClauses a b
clausesWithEmptyConstraints = map (bimap (emptyConstraints,) id)

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

forceData :: (Matching m) => VTm -> m (DataGlobal, Spine HTm, Spine HTm)
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

simpleConstraints :: Spine HTm -> Spine Pat -> m Constraints
simpleConstraints = undefined

simpleConstraint :: HTm -> Pat -> m Constraint
simpleConstraint = undefined

data Constraint = Constraint {lvl :: Lvl, lhs :: VTm, rhs :: Pat, param :: Param VTy}

data Constraints = Constraints {list :: [Constraint]}

emptyConstraints :: Constraints
emptyConstraints = Constraints []

addConstraint :: Constraint -> ConstrainedClause (Spine Pat) STm -> ConstrainedClause (Spine Pat) STm
addConstraint c (Clause (Constraints cs, sp) t) = Clause (Constraints (c : cs), sp) t

nextConstraint :: Constraints -> Maybe (Constraint, Constraints)
nextConstraint (Constraints []) = Nothing

data MatchingState = MatchingState
  { ctx :: HCtx,
    ty :: HTy,
    cls :: [Clause (Constraints, Spine Pat) STm]
  }

caseTree :: (Matching m) => MatchingState -> m STm
caseTree c = do
  let tactics = [addVar c, splitConstraint c]
  result <- asum <$> sequence tactics
  case result of
    Just r -> return r
    Nothing -> error "no case tree tactic matched"

addVar :: (Matching m) => MatchingState -> m (Maybe STm)
addVar (MatchingState ctx ty cls) = do
  (ps, cls') <- nextPat cls
  case ps of
    Nothing -> return Nothing
    Just ps' -> do
      ty' <- embedHere ty >>= evalHere >>= unfoldHere
      case ty' of
        VNorm (VPi m q x a b) -> binder m q x a $ \l' -> do
          l <- getLvl
          b' <- b $$ [VV l'] >>= quoteHere >>= unembedHere
          ha <- quoteHere a >>= unembedHere -- @@Todo: better way to do this?
          let cls'' = zipWith (\pt -> addConstraint $ Constraint l (VV l') pt (Param m q x a)) ps' cls'
          rest <- caseTree (MatchingState (ctx :|> Param m q x ha) b' cls'')
          return . Just $ SLam m q x rest
        _ -> return Nothing

splitConstraint :: (Matching m) => MatchingState -> m (Maybe STm)
splitConstraint (MatchingState ctx ty cls) = do
  -- Current context is:  Γχ (x : A)
  -- Rest of the goal is: Π xΓ T
  case cls of
    Clause (Constraints (co : _), _) _ : clss -> case co of
      Constraint _ (VV x) (LvlP _ _ x') _ -> do
        -- We have that x = x'
        -- This will use the solution rule for the constraint x = x'
        (ctx', _, s) <- unifyPL ctx (HVar x) (HVar x')
        Just <$> caseTree (MatchingState ctx' (sub s.forward ty) clss)
      Constraint _ (VV x) (CtorP _ _) param -> do
        -- We have that A = D δ ψ and x = ci πg

        -- Get the current subject type, i.e. D δ ψ
        (d, delta, psi) <- forceData param.ty
        (di, dc) <- access (getDataGlobal' d)

        -- Create the spine (ψ, x)
        let psix = psi :|> Arg param.mode param.qty (HVar x)

        -- For each constructor ci (π : Πi [δ]) : D δ (ξi [δ,π]):
        elims <- forM di.ctors $ \c -> do
          (_, cc) <- access (getCtorGlobal' c)

          -- Enter the context of the constructor.
          enterHTel (cc.args delta) $ \pi -> do
            -- @@Todo: turn to explicit context
            -- For each clause with pattern pj
            children <- fmap catMaybes . forM cls $ \cl' -> do
              case cl' of
                Clause (Constraints [], _) _ -> return Nothing
                Clause (Constraints (Constraint _ _ (LvlP _ _ p) _ : cs'), ps) t -> do
                  let cpat = tmAsPat (hApp (HCtor (c, delta)) pi)
                  newConstraint <- simpleConstraint (HVar p) cpat
                  return . Just $ Clause (Constraints (newConstraint : cs'), ps) t
                Clause (Constraints (Constraint _ _ (CtorP (cj, _) _) _ : _), _) _ | cj /= c -> return Nothing
                Clause (Constraints (Constraint _ _ (CtorP _ sp) _ : cs'), ps) t -> do
                  -- Current context is: Γχ (x : D δ ψ) xΓ (π : Πi)
                  -- equate pi to pj, gives back simple constraints.
                  -- give those constraints to make the child case clause j.
                  -- add this to matched clauses for i.
                  --
                  -- this constitutes a match for the constructor ci.
                  -- now to build the method for ci, call casetree recursively
                  -- with the configuration amended by the new constraints
                  newConstraints <- simpleConstraints pi sp
                  return . Just $ Clause (joinConstraints newConstraints (Constraints cs'), ps) t
            -- Create the spine (ξi[δ,π], ci π)
            let psix' = cc.returnIndices delta pi :|> Arg param.mode param.qty (hApp (HCtor (c, delta)) pi)

            -- Unify (ψ, x) with (ξi[δ,π], ci π), which will give back a new context Γ'
            -- that is isomorphic to
            --    Γχ (x : D δ ψ) xΓ (π : Πi) ((ψ, x) = (ξi[δ,π], ci π))
            -- through the substitution σ.
            (ctx', _, s) <- unifyPLSpines ctx psix psix'
            -- @@Todo: do we care about status?

            -- Build the rest of the clause, which will first give:
            --    Γ' |- e' : T σ
            -- This is refined by specialisation by unification to:
            --    Γχ (x : D δ ψ) xΓ (π : Πi) ((ψ, x) = (ξi[δ,π], ci π)) |- e : T
            -- @@Todo: We need to apply sub to children too, and perhaps move xΓ to the context?
            e <- caseTree (MatchingState ctx' (sub s.backward ty) children)

            -- @@Todo: We need to substitute over propositional K somewhere around here..
            --
            -- Now we build e'' which is:
            --    Γχ (x : D δ ψ) xΓ (π : Πi) |- e'' : Π ((ψ, x) = (ξi[δ,π], ci π)) T
            -- The equalities are explicitly given by the motive we will set up later.
            eq <- here (`embedTel` eqTel psix psix')
            let e'' = sLams eq e

            -- The method is for constructor ci π
            pt <- here (`embed` hApp (HCtor (c, delta)) pi)
            let spt = SPat pt (telToBinds cc.argsArity)
            return (Clause spt (Just e''))

        -- Now we build the motive for the case.
        -- First, we have the required data indices and subject:
        --    (ψ' : Ψ[δ]) (x' : D δ ψ')
        let psixTe' = extendTel (dc.indices delta) (\psi' -> param {ty = hApp (HData d) (delta <> psi')})
        -- We also add the equalities between the subject and the data indices
        -- in the motive and the ones in the context.
        --    (ψ' : Ψ[δ]) (x' : D δ ψ') ((ψ, x) = (ψ', x'))
        let eq = eqTel psix
        let indTel = joinTels psixTe' eq

        -- We also need the reflexivity proofs to apply to the motive.
        --    refl [ψj] : Equal [Ψj] ψj ψj
        -- Where ψj = ψ1, ..., ψn, x
        psixRefl <- mapSpineM embedHere $ reflSp psixTe' psix

        caseBase <- here $ \lv ->
          embedCase lv $
            Case
              { dat = d,
                datParams = delta,
                subject = HVar x,
                subjectIndices = psi,
                -- The final motive is:
                --    Γχ (x : D δ ψ)  |-   λ ψ' x'. Π ((ψ, x) = (ψ', x'), xΓ) T   :   Π (ψ' : Ψ[δ], x' : D δ ψ') U
                elimTy = hLams indTel (const ty),
                clauses = []
              }
        return . Just $ sAppSpine (SCase (caseBase {clauses = elims})) psixRefl
      _ -> return Nothing
    _ -> return Nothing
