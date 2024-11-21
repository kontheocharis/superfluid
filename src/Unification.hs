{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Unification
  ( UnifyError (..),
    SolveError (..),
    unify,
    CanUnify (..),
    MetaProblem (..),
    Unify (..),
    canUnifyHere,
    unifyPL,
    unifyPLSpines,
  )
where

import Algebra.Lattice (Lattice (..), (/\))
import Common
  ( Arg (..),
    Clause (..),
    Has (..),
    HasNameSupply (uniqueName),
    Lit (..),
    Lvl (..),
    MetaVar,
    Name (..),
    Param (..),
    PiMode (..),
    Qty (..),
    Spine,
    Tel,
    composeZ,
    lvlToIdx,
    mapSpineM,
    nameSpineToTel,
    nextLvl,
    nextLvls,
    spineShapes,
    telShapes,
    pattern Impossible,
    pattern Possible,
  )
import Constructions (ctorConstructions)
import Context
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Extra (findM, firstJustM)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Foldable (Foldable (..), toList)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List (intercalate)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation
  ( Eval (..),
    embedEval,
    eval,
    evalInOwnCtx,
    force,
    quotePat,
    vApp,
  )
import Globals (CtorConstructions (..), DataConstructions (..), getCtorGlobal)
import Meta (solveMetaVar)
import Printing (Pretty (..))
import Substitution (BiSub (..), Shape, Shapes, Sub (..), Subst (..), composeSub, extendSub, idSub, liftSubN, mapSub1, mapSubN, proj, projN, replaceSub)
import Syntax
  ( Case (..),
    Closure (body, numVars),
    HCtx,
    HTm (..),
    SPat (..),
    STm (..),
    VLazy,
    VLazyHead (..),
    VNeu,
    VNeuHead (..),
    VNorm (..),
    VPatB (..),
    VTm (..),
    VTy,
    embed,
    hApp,
    hGatherApps,
    headAsValue,
    removing,
    uniqueSLams,
    pattern VV,
    pattern VVar,
  )
import Prelude hiding (cycle, pi)

data MetaProblem = MetaProblem {m :: MetaVar, sp :: Spine VTm, rhs :: VTm}

class (Eval m, Has m Ctx) => Unify m where
  onMetaFailed :: MetaProblem -> SolveError -> m ()
  onMetaSolved :: MetaProblem -> m ()

data UnifyError
  = DifferentSpineLengths (Spine VTm) (Spine VTm)
  | DifferentClauses [Clause VPatB Closure] [Clause VPatB Closure]
  | Mismatching VTm VTm
  | SolveError SolveError
  deriving (Show)

data SolveError
  = InvertError (Spine VTm)
  | OccursError MetaVar
  | EscapingVariable
  | Blocking
  | Synthesis
  deriving (Show)

data CanUnify = Yes | No [UnifyError] | Maybe deriving (Show)

instance (Eval m) => Lattice (m CanUnify) where
  a \/ b = do
    a' <- a
    case a' of
      Yes -> return a'
      No _ -> b
      Maybe -> do
        b' <- b
        case b' of
          Yes -> return Yes
          No _ -> return a'
          Maybe -> return Maybe

  a /\ b = do
    a' <- a
    case a' of
      Yes -> b
      No xs -> do
        b' <- b
        case b' of
          Yes -> return a'
          No ys -> return $ No (xs ++ ys)
          Maybe -> return $ No xs
      Maybe -> do
        b' <- b
        case b' of
          Yes -> return Maybe
          No ys -> return $ No ys
          Maybe -> return Maybe

type SolveT = ExceptT SolveError

invertSpine :: (Unify m) => Spine VTm -> SolveT m PRen
invertSpine Empty = do
  l <- lift getLvl
  return $ PRen (Lvl 0) l mempty
invertSpine s@(sp' :|> Arg _ q t) = do
  (PRen dom cod ren) <- invertSpine sp'
  f <- lift $ force t
  case f of
    VNeu (VVar (Lvl l')) | IM.notMember l' ren -> return $ PRen (nextLvl dom) cod (IM.insert l' (dom, q) ren)
    _ -> throwError $ InvertError s

unifySpines :: (Unify m) => Spine VTm -> Spine VTm -> m CanUnify
unifySpines Empty Empty = return Yes
unifySpines (sp :|> Arg _ q u) (sp' :|> Arg _ q' u') | q == q' = unifySpines sp sp' /\ unify u u'
unifySpines sp sp' = return $ No [DifferentSpineLengths sp sp']

unifyClauses :: (Unify m) => [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses [] [] = return Yes
unifyClauses (c : cs) (c' : cs') = unifyClause c c' /\ unifyClauses cs cs'
unifyClauses a b = return $ No [DifferentClauses a b]

unifyClause :: (Unify m) => Clause VPatB Closure -> Clause VPatB Closure -> m CanUnify
unifyClause (Possible p t) (Possible p' t') = unifyClosure (map fst p.binds) t (map fst p'.binds) t'
unifyClause (Impossible _) (Impossible _) = return Yes
unifyClause a b = return $ No [DifferentClauses [a] [b]]

runSolveT :: (Unify m) => MetaVar -> Spine VTm -> VTm -> SolveT m () -> m CanUnify
runSolveT m sp t f = do
  f' <- runExceptT f
  case f' of
    Left err -> do
      onMetaFailed (MetaProblem m sp t) err
      return Yes
    Right () -> onMetaSolved (MetaProblem m sp t) >> return Yes

canUnifyHere :: (Unify m) => VTm -> VTm -> m CanUnify
canUnifyHere t1 t2 = do
  -- l <- accessCtx (\c -> c.lvl)
  t1' <- resolveHere t1
  t2' <- resolveHere t2
  unify t1' t2'

unifyFlex :: (Unify m) => MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyFlex m sp t = runSolveT m sp t $ do
  pren <- invertSpine sp
  rhs <- rename m pren t
  solution <- lift $ uniqueSLams (reverse $ map (\a -> (a.mode, a.qty)) (toList sp)) rhs >>= eval []
  lift $ solveMetaVar m solution

unifyClosure :: (Unify m) => [Qty] -> Closure -> [Qty] -> Closure -> m CanUnify
unifyClosure qs1 cl1 _ cl2 = do
  l <- getLvl
  t1 <- evalInOwnCtx l cl1
  t2 <- evalInOwnCtx l cl2
  if cl1.numVars == cl2.numVars
    then enterTypelessClosure qs1 cl1 $ unify t1 t2
    else error "unifyClosure: different number of variables"

iDontKnow :: (Unify m) => m CanUnify
iDontKnow = return Maybe

unify :: (Unify m) => VTm -> VTm -> m CanUnify
unify t1 t2 = do
  t1' <- force t1
  t2' <- force t2
  unifyForced t1' t2'

etaConvert :: (Unify m) => VTm -> PiMode -> Qty -> Closure -> m CanUnify
etaConvert t m q c = do
  l <- getLvl
  x <- evalInOwnCtx l c
  x' <- vApp t (S.singleton (Arg m q (VNeu (VVar l))))
  enterTypelessClosure [q] c $ unify x x'

unifyForced :: (Unify m) => VTm -> VTm -> m CanUnify
unifyForced t1 t2 = case (t1, t2) of
  (VNorm (VLam m q _ c), VNorm (VLam m' q' _ c')) | m == m' && q == q' -> unifyClosure [q] c [q'] c'
  (t, VNorm (VLam m' q' _ c')) -> etaConvert t m' q' c'
  (VNorm (VLam m q _ c), t) -> etaConvert t m q c
  (VNorm n1, VNorm n2) -> unifyNormRest n1 n2
  (VNeu (VFlex x, sp), VNeu (VFlex x', sp')) | x == x' -> unifySpines sp sp' \/ iDontKnow
  (VNeu (VFlex x, sp), _) -> unifyFlex x sp t2
  (_, VNeu (VFlex x', sp')) -> unifyFlex x' sp' t1
  (VNeu (VUnrepr c1, sp1), VNeu (VUnrepr c2, sp2)) -> unify (headAsValue c1) (headAsValue c2) /\ unifySpines sp1 sp2
  (_, VNeu (VUnrepr _, _)) -> do
    rt1 <- reprHere 1 t1
    rt2 <- reprHere 1 t2
    unify rt1 rt2
  (VNeu (VUnrepr _, _), _) -> do
    rt1 <- reprHere 1 t1
    rt2 <- reprHere 1 t2
    unify rt1 rt2
  (VNeu n1, VNeu n2) -> unifyNeuRest n1 n2
  (VLazy l1, VLazy l2) -> unifyLazy l1 l2
  (VLazy l, t) -> unifyLazyWithTermOr l t iDontKnow
  (t, VLazy l) -> unifyLazyWithTermOr l t iDontKnow
  _ -> return $ No [Mismatching t1 t2]

unifyNormRest :: (Unify m) => VNorm -> VNorm -> m CanUnify
unifyNormRest n1 n2 = case (n1, n2) of
  (VPi m q _ t c, VPi m' q' _ t' c') | m == m' && q == q' -> unify t t' /\ unifyClosure [q] c [q'] c'
  (VU, VU) -> return Yes
  (VData (d, sp), VData (d', sp')) | d == d' -> unifySpines sp sp'
  (VCtor ((c, _), sp), VCtor ((c', _), sp'))
    | c == c' -> unifySpines sp sp'
  _ -> return $ No [Mismatching (VNorm n1) (VNorm n2)]

unifyLazy :: (Unify m) => VLazy -> VLazy -> m CanUnify
unifyLazy (n1, sp1) (n2, sp2) =
  ( ( case (n1, n2) of
        (VDef d1, VDef d2) | d1 == d2 -> return Yes
        (VLit l1, VLit l2) -> unifyLit l1 l2
        (VLazyCase c1, VLazyCase c2) -> unifyCases VLazy c1 c2
        (VLet q1 _ a1 t1 u1, VLet q2 _ a2 t2 u2) | q1 == q2 -> unify a1 a2 /\ unify t1 t2 /\ unifyClosure [q1] u1 [q2] u2
        (VRepr n1', VRepr n2') -> unify (headAsValue n1') (headAsValue n2')
        _ -> iDontKnow
    )
      /\ unifySpines sp1 sp2
  )
    \/ tryUnfold
  where
    tryUnfold = unifyLazyWithTermOr (n1, sp1) (VLazy (n2, sp2)) (unifyLazyWithTermOr (n2, sp2) (VLazy (n1, sp1)) iDontKnow)

unifyNeuRest :: (Unify m) => VNeu -> VNeu -> m CanUnify
unifyNeuRest (n1, sp1) (n2, sp2) = case (n1, n2) of
  (VRigid x, VRigid x') | x == x' -> do
    unifySpines sp1 sp2 \/ iDontKnow
  (VBlockedCase c1, VBlockedCase c2) -> unifyCases VNeu c1 c2 /\ unifySpines sp1 sp2
  (VPrim p1, VPrim p2) | p1 == p2 -> unifySpines sp1 sp2
  _ -> return $ No [Mismatching (VNeu (n1, sp1)) (VNeu (n2, sp2))]

unifyLazyWithTermOr :: (Unify m) => VLazy -> VTm -> m CanUnify -> m CanUnify
unifyLazyWithTermOr l t els = do
  l' <- unfoldLazyHere l
  case l' of
    Just l'' -> unify l'' t
    Nothing -> els

unifyCases :: (Unify m) => (s -> VTm) -> Case s VTm VPatB Closure -> Case s VTm VPatB Closure -> m CanUnify
unifyCases f c1 c2 = unify (f c1.subject) (f c2.subject) /\ unifyClauses c1.clauses c2.clauses

unifyLit :: (Unify m) => Lit VTm -> Lit VTm -> m CanUnify
unifyLit l1 l2 = case (l1, l2) of
  (StringLit x, StringLit y) | x == y -> return Yes
  (CharLit x, CharLit y) | x == y -> return Yes
  (NatLit x, NatLit y) | x == y -> return Yes
  (FinLit d n, FinLit d' n') | d == d' -> unify n n'
  _ -> return $ No [Mismatching (VLazy (VLit l1, Empty)) (VLazy (VLit l2, Empty))]

instance (Monad m, Pretty m VTm, Pretty m STm, Pretty m VPatB, Pretty m Closure) => Pretty m CanUnify where
  pretty Yes = return "can unify"
  pretty (No xs) = do
    xs' <- intercalate ", " <$> mapM pretty xs
    return $ "cannot unify: " ++ xs'
  pretty Maybe = do
    return "unclear"

instance (Monad m, Pretty m VTm, Pretty m STm) => Pretty m SolveError where
  pretty (InvertError s) = do
    s' <- pretty s
    return $ "the arguments " ++ s' ++ " contain non-variables"
  pretty (OccursError m) = do
    m' <- pretty (SMeta m [])
    return $ "the meta-variable " ++ m' ++ " occurs in a term it is being unified against"
  pretty EscapingVariable = do
    return "a variable in a term escapes the context of the meta it is being unified against"
  pretty Blocking = return "reduction is blocked"
  pretty Synthesis = return "synthesis failed"

-- pretty (WithProblem p@(Problem {kind = Unify lhs rhs}) e) = do
--   p' <- enterProblem p $ do
--     lhs' <- pretty lhs
--     rhs' <- pretty rhs
--     return $ lhs' ++ " =? " ++ rhs'
--   e' <- pretty e
--   return $ p' ++ "\n" ++ e'
-- pretty (WithProblem p@(Problem {kind = Synthesize _ ty}) e) = do
--   p' <- enterProblem p $ do
--     ty' <- pretty ty
--     return $ "synthesize " ++ ty'
--   e' <- pretty e
--   return $ p' ++ "\n" ++ e'

instance (Monad m, Pretty m VTm, Pretty m STm, Pretty m VPatB, Pretty m Closure) => Pretty m UnifyError where
  pretty (SolveError e) = pretty e
  pretty (DifferentSpineLengths s s') = do
    s'' <- pretty s
    s''' <- pretty s'
    return $ "the arguments " ++ s'' ++ " and " ++ s''' ++ " have different lengths"
  pretty (DifferentClauses cs cs') = do
    cs'' <- pretty cs
    cs''' <- pretty cs'
    return $ "the clauses " ++ cs'' ++ " and " ++ cs''' ++ " are different"
  pretty (Mismatching t t') = do
    t'' <- pretty t
    t''' <- pretty t'
    return $ "the terms " ++ t'' ++ " and " ++ t''' ++ " do not match"

-- Partial renaming:

data PRen = PRen
  { domSize :: Lvl,
    codSize :: Lvl,
    vars :: IntMap (Lvl, Qty)
  }
  deriving (Show)

liftPRen :: Qty -> PRen -> PRen
liftPRen q (PRen dom cod ren) = PRen (Lvl (dom.unLvl + 1)) (Lvl (cod.unLvl + 1)) (IM.insert cod.unLvl (dom, q) ren)

liftPRenN :: [Qty] -> PRen -> PRen
liftPRenN qs ren = foldl (flip liftPRen) ren qs

renameSp :: (Unify m) => MetaVar -> PRen -> STm -> Spine VTm -> SolveT m STm
renameSp _ _ t Empty = return t
renameSp m pren t (sp :|> Arg i q u) = do
  xs <- renameSp m pren t sp
  ys <- rename m pren u
  return $ SApp i q xs ys

renameClosure :: (Unify m) => MetaVar -> PRen -> [Qty] -> Closure -> SolveT m STm
renameClosure m pren qs cl = do
  vt <- lift $ evalInOwnCtx pren.codSize cl
  rename m (liftPRenN qs pren) vt

renamePat :: (Unify m) => MetaVar -> PRen -> VPatB -> SolveT m SPat
renamePat _ pren p = do
  lift $ quotePat pren.codSize p

renameCaseSpine ::
  (Unify m) =>
  (MetaVar -> PRen -> s -> SolveT m STm) ->
  MetaVar ->
  PRen ->
  Case s VTm VPatB Closure ->
  Spine VTm ->
  SolveT m STm
renameCaseSpine renameSubject m pren (Case dat pp v i r cs) sp = do
  v' <- renameSubject m pren v
  cs' <-
    mapM
      ( \(Clause p t) -> do
          p' <- renamePat m pren p
          t' <- traverse (renameClosure m pren (map fst p.binds)) t
          return $ Clause p' t'
      )
      cs
  r' <- rename m pren r
  pp' <- mapSpineM (rename m pren) pp
  i' <- mapSpineM (rename m pren) i
  renameSp m pren (SCase (Case dat pp' v' i' r' cs')) sp

renameReprSpine :: (Unify m) => MetaVar -> PRen -> Int -> VTm -> Spine VTm -> SolveT m STm
renameReprSpine m pren t n sp = do
  m' <- rename m pren n
  let hd = composeZ t SRepr SUnrepr m'
  renameSp m pren hd sp

renameLazy :: (Unify m) => MetaVar -> PRen -> VLazy -> SolveT m STm
renameLazy m pren (n, sp) = case n of
  VDef d -> renameSp m pren (SDef d) sp
  VLit t -> do
    t' <- traverse (rename m pren) t
    renameSp m pren (SLit t') sp
  VLazyCase c -> renameCaseSpine renameLazy m pren c sp
  VRepr n' -> renameReprSpine m pren 1 (headAsValue n') sp
  VLet q x a t u -> do
    a' <- rename m pren a
    t' <- rename m pren t
    u' <- renameClosure m pren [q] u
    return $ SLet q x a' t' u'

renameNeu :: (Unify m) => MetaVar -> PRen -> VNeu -> SolveT m STm
renameNeu m pren (n, sp) = case n of
  VFlex m'
    | m == m' -> throwError $ OccursError m
    | otherwise -> renameSp m pren (SMeta m' []) sp
  VRigid (Lvl l) -> case IM.lookup l pren.vars of
    Nothing -> throwError EscapingVariable
    Just (x', _) -> renameSp m pren (SVar (lvlToIdx pren.domSize x')) sp
  VBlockedCase c -> renameCaseSpine renameNeu m pren c sp
  VPrim p -> renameSp m pren (SPrim p) sp
  VUnrepr n' -> renameReprSpine m pren (-1) (headAsValue n') sp

renameNorm :: (Unify m) => MetaVar -> PRen -> VNorm -> SolveT m STm
renameNorm m pren n = case n of
  VLam i q x t -> do
    t' <- renameClosure m pren [q] t
    return $ SLam i q x t'
  VPi i q x ty t -> do
    ty' <- rename m pren ty
    t' <- renameClosure m pren [q] t
    return $ SPi i q x ty' t'
  VU -> return SU
  VData (d, sp) -> renameSp m pren (SData d) sp
  VCtor ((c, pp), sp) -> do
    pp' <- mapSpineM (rename m pren) pp
    renameSp m pren (SCtor (c, pp')) sp

rename :: (Unify m) => MetaVar -> PRen -> VTm -> SolveT m STm
rename m pren tm = case tm of
  VNorm n -> renameNorm m pren n
  VLazy n -> renameLazy m pren n
  VNeu n -> renameNeu m pren n

-- Proof relevant unification
--

data UnifyPLError = UnifyPLError

class (Eval m, Has m Ctx) => UnifyPL m where
  throwUnifyError :: UnifyPLError -> m a

  target :: m VTm

-- The unify outcome is a "decorated" bit that tells us whether the unification
-- was successful or not.
data UnifyOutcome = Can | Cannot [UnifyPLError]

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
equality :: HTm -> HTm -> HTm
equality = undefined

-- Fibered equality (shorthand = with types left as an exercise)
--
-- internally:
-- HEqual : [A : Type] (s t : A) (e : Equal s t) (P : A -> Type) -> P s -> P t -> Type
-- HEqual [A] s t e P u v = Equal [P t] (subst P e u) v
hequality :: HTm -> HTm -> HTm -> HTm -> HTm -> HTm
hequality = undefined

hequalitySp :: Spine HTm -> Spine HTm -> Tel STm
hequalitySp = undefined

-- dcong : (f : Tm Γ (Π A Τ)) -> {x y : Tm Γ A} -> Tms Γ (x = y) -> Tms Γ (f x = f y)
dcong :: (HTm -> HTm) -> HTm -> HTm
dcong = undefined

-- dcongSp : (f : Tm Γ (Πs Δ Τ)) -> {xs ys : Tms Γ Δ} -> Tms Γ (xs ..= ys) -> Tm Γ (f xs = f ys)
dcongSp :: (Spine HTm -> HTm) -> Spine HTm -> HTm
dcongSp = undefined

-- noConf : (c : Ctor D Δ Π ξ) -> {xs ys : Tms Γ Π} -> Tm Γ (c xs = c ys) -> Tms Γ (xs ..= ys)
noConf :: HTm -> HTm -> Spine HTm
noConf = undefined

-- conflict : (c1 : Ctor D Δ Π₁, c2 : Ctor D Δ Π₂ ξ₂) -> {xs : Tms  ys : Tms Γ Π}
--            -> Tm Γ (c1 xs = c2 ys)
--            -> Tm Γ Empty
conf :: HTm -> HTm -> HTm -> HTm
conf = undefined

-- Never
--
-- This is the internal Empty type's eliminator.
--
-- Important: 'internal Empty' means void in the metatheory, because the Unit
-- type behaves like the empty context instead.
--
-- never : [A : Ty Γ] -> Tm Γ Empty -> Tm Γ A
never :: HTm -> HTm
never = undefined

voidSh :: Shapes
voidSh = Param Explicit Many (Name "_") () :<| Empty

voidCtx :: HCtx
voidCtx = undefined

initialSub :: Shapes -> Shapes -> Sub
initialSub vSh sh = mapSub1 vSh sh (\_ x -> fmap (\p -> Arg p.mode p.qty (never x)) sh)

ofSh :: Shapes -> [a] -> Spine a
ofSh sh xs = foldr (\(Param m q _ (), t) sp -> Arg m q t :<| sp) Empty (zip (toList sh) xs)

-- Unification:

unifyPLSpines :: (UnifyPL m) => HCtx -> Spine HTm -> Spine HTm -> m Unification
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

unifyPL :: (UnifyPL m) => HCtx -> HTm -> HTm -> m Unification
unifyPL ctx t1 t2 = do
  let tactics = [solution, injectivity, conflict, cycle, deletion]
  res <- firstJustM (\t -> t ctx t1 t2) tactics
  case res of
    Just x -> return x
    Nothing -> throwUnifyError UnifyPLError

-- specialise ::

solution :: (UnifyPL m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
solution ctx a b = case (a, b) of
  (_, HVar l) -> solution ctx (HVar l) a
  (HVar l, _) -> do
    let sh  = telShapes ctx

    -- Make a new name and shape for the new context
    x <- uniqueName
    let csh = Param Explicit Many x ()

    -- Substitute b for l in the (rest of) the context, while removing l from
    -- the context
    -- @@Todo: ocurrence check

    -- Γx (context)
    let ctxx = S.take l.unLvl ctx

    -- (x : A)
    let xSh = S.index sh l.unLvl

    -- xΓ (telescope)
    let xctxx = S.drop (nextLvl l).unLvl ctx

    -- xΓ [x ↦ b]
    --
    -- We want Sub Γx Γx(x : A) which can be constructed as:
    -- [x ↦ a] = (id, b)
    let vs = extendSub (idSub sh) xSh (const b) -- @@Fixme: const b might not work with the HOAS
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
    --    σ⁻¹ = (\γ γ' => (γ, a, γ', refl a))
    let s = undefined
    -- let s = BiSub
          -- { forward = mapSub1 (sh :|> csh) rsh (\sp _ -> S.take l.unLvl sp <> sub vs (S.drop (nextLvl l).unLvl sp)),
          --   backward = mapSubN rsh (sh :|> csh)  (\sp p -> sp :|> Arg Explicit Many p)
          -- }
    return $ Just (ctx', Can, s)
  _ -> return Nothing

injectivity :: (UnifyPL m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
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

conflict :: (UnifyPL m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
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

cycle :: (UnifyPL m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
cycle ctx a b = case (a, b) of
  (_, HVar l) -> cycle ctx (HVar l) a
  (HVar l, hGatherApps -> (HCtor (c1, _), xs)) ->
    -- 1. Check if l occurs in xs
    -- 2. If so, then we have a cycle so return Cannot with the appropriate sub.

    return undefined
  _ -> return Nothing

-- Definitional equality checker. This should somehow hook into the other
-- unification thing. (And the latter should be renamed to convert?)
canConvert :: (UnifyPL m) => HCtx -> HTm -> HTm -> m Bool
canConvert = undefined

-- Internal reflexivity
-- refl : [A : Type] -> A -> A
refl :: HTm -> HTm
refl = undefined

deletion :: (UnifyPL m) => HCtx -> HTm -> HTm -> m (Maybe Unification)
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
