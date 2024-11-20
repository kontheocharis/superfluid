{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Unification
  ( UnifyError (..),
    SolveError (..),
    unify,
    CanUnify (..),
    MetaProblem (..),
    Unify (..),
    canUnifyHere,
  )
where

import Algebra.Lattice (Lattice (..), (/\))
import Common
  ( Arg (..),
    Clause (..),
    Has (..),
    Lit (..),
    Lvl (..),
    MetaVar,
    PiMode (..),
    Qty (..),
    Spine,
    composeZ,
    lvlToIdx,
    mapSpineM,
    nextLvl,
    pattern Impossible,
    pattern Possible,
  )
import Context
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Foldable (Foldable (..), toList)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List (intercalate)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation
  ( Eval (..),
    eval,
    evalInOwnCtx,
    force,
    quotePat,
    vApp,
  )
import Meta (solveMetaVar)
import Printing (Pretty (..))
import Substitution (BiSub)
import Syntax
  ( Case (..),
    Closure (body, numVars),
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
    headAsValue,
    uniqueSLams,
    pattern VVar,
  )
import Prelude hiding (pi)

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

data UnifyResult = Can BiSub | Cannot BiSub [UnifyError] | Unclear


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
