{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Unification
  ( unifyErrorIsMetaRelated,
    Unify (..),
    unify,
    CanUnify (..),
    SolveError (..),
    Problem (..),
    UnifyError (..),
    getProblems,
  )
where

import Algebra.Lattice (Lattice (..))
import Common
  ( Arg (..),
    Clause (..),
    DefGlobal,
    Glob (..),
    Has (..),
    Lit (..),
    Loc,
    Lvl (..),
    MetaVar,
    Modify (modify),
    Name,
    PiMode (..),
    Spine,
    Times,
    View (..),
    lvlToIdx,
    mapSpineM,
    nextLvl,
    nextLvls,
    pattern Impossible,
    pattern Possible,
  )
import Control.Exception (assert)
import Control.Monad (zipWithM, zipWithM_)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Either (fromRight, isRight)
import Data.Foldable (Foldable (fold), toList)
import qualified Data.IntMap as IM
import Data.List (intercalate)
import Data.Sequence (Seq (..), ViewR (..))
import qualified Data.Sequence as S
import Debug.Trace (trace, traceM)
import Evaluation (Eval, eval, evalInOwnCtx, force, quote, quoteSpine, vApp, ($$))
import Globals (KnownGlobal (..), knownCtor, knownData, unfoldDef)
import Literals (unfoldLit)
import Meta (solveMetaVar)
import Numeric.Natural (Natural)
import Printing (Pretty (..))
import Syntax (SPat (..), STm (..), uniqueSLams)
import Value
  ( Closure,
    PRen (..),
    Sub (..),
    VHead (..),
    VNeu (..),
    VPatB (..),
    VTm (..),
    liftPRen,
    liftPRenN,
    numVars,
    subbing,
    pattern VGl,
    pattern VGlob,
    pattern VVar,
  )

data UnifyError
  = DifferentSpineLengths (Spine VTm) (Spine VTm)
  | DifferentClauses [Clause VPatB Closure] [Clause VPatB Closure]
  | Mismatching VTm VTm
  | SolveError SolveError
  | PrevError String
  deriving (Show)

unifyErrorIsMetaRelated :: UnifyError -> Bool
unifyErrorIsMetaRelated (SolveError _) = True
unifyErrorIsMetaRelated _ = False

data SolveError
  = InvertError (Spine VTm)
  | OccursError MetaVar VTm
  | EscapingVariable VTm
  deriving (Show)

data CanUnify = Yes | No [UnifyError] | Maybe Sub deriving (Show)

instance (Eval m, Has m [Name]) => Pretty m CanUnify where
  pretty Yes = return "can unify"
  pretty (No xs) = do
    xs' <- intercalate ", " <$> mapM pretty xs
    return $ "cannot unify: " ++ xs'
  pretty (Maybe s) = do
    s' <- pretty s
    return $ "can only unify if: " ++ s'

instance (Eval m, Has m [Name]) => Pretty m SolveError where
  pretty (InvertError s) = do
    s' <- pretty s
    return $ "the arguments " ++ s' ++ " contain non-variables"
  pretty (OccursError m t) = do
    t' <- pretty t
    m' <- pretty (SMeta m [])
    return $ "the meta-variable " ++ m' ++ " occurs in " ++ t'
  pretty (EscapingVariable t) = do
    t' <- pretty t
    return $ "a variable is missing from " ++ t'

instance (Eval m, Has m [Name]) => Pretty m UnifyError where
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
  pretty (PrevError e) = return e

instance Lattice CanUnify where
  Yes \/ _ = Yes
  _ \/ Yes = Yes
  No _ \/ a = a
  a \/ No _ = a
  Maybe _ \/ Maybe _ = Maybe mempty

  Yes /\ a = a
  a /\ Yes = a
  No xs /\ No ys = No (xs ++ ys)
  No xs /\ _ = No xs
  _ /\ No xs = No xs
  Maybe x /\ Maybe y = Maybe (x <> y)

class (Eval m, Has m (Seq Problem), Has m Loc, Has m [Name]) => Unify m

type SolveT = ExceptT SolveError

invertSpine :: (Unify m) => Lvl -> Spine VTm -> SolveT m PRen
invertSpine l Empty = return $ PRen (Lvl 0) l mempty
invertSpine l s@(sp' :|> Arg _ t) = do
  (PRen dom cod ren) <- invertSpine l sp'
  f <- lift $ force t
  case f of
    VNeu (VVar (Lvl l')) | IM.notMember l' ren -> return $ PRen (nextLvl dom) cod (IM.insert l' dom ren)
    _ -> throwError $ InvertError s

renameSp :: (Unify m) => MetaVar -> PRen -> STm -> Spine VTm -> SolveT m STm
renameSp _ _ t Empty = return t
renameSp m pren t (sp :|> Arg i u) = do
  xs <- renameSp m pren t sp
  ys <- rename m pren u
  return $ SApp i xs ys

renameClosure :: (Unify m) => MetaVar -> PRen -> Closure -> SolveT m STm
renameClosure m pren cl = do
  vt <- lift $ evalInOwnCtx pren.codSize cl
  rename m (liftPRenN cl.numVars pren) vt

renamePat :: (Unify m) => MetaVar -> PRen -> VPatB -> SolveT m SPat
renamePat m pren (VPatB p binds) = do
  let n = length binds
  p' <- rename m (liftPRenN n pren) p
  return $ SPat p' binds

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: (Unify m) => MetaVar -> PRen -> VTm -> SolveT m STm
rename m pren tm = do
  f <- lift $ force tm
  case f of
    VNeu (VApp (VFlex m') sp)
      | m == m' -> throwError $ OccursError m tm
      | otherwise -> renameSp m pren (SMeta m' []) sp
    VNeu (VApp (VRigid (Lvl x)) sp) -> case IM.lookup x pren.vars of
      Nothing -> throwError $ EscapingVariable tm
      Just x' -> renameSp m pren (SVar (lvlToIdx pren.domSize x')) sp
    VNeu (VReprApp n h sp) -> do
      t' <- rename m pren (VNeu (VApp h Empty))
      renameSp m pren (SRepr n t') sp
    VNeu (VCaseApp dat v cs sp) -> do
      v' <- rename m pren (VNeu v)
      cs' <- mapM (bitraverse (renamePat m pren) (renameClosure m pren)) cs
      renameSp m pren (SCase dat v' cs') sp
    VLam i x t -> do
      t' <- renameClosure m pren t
      return $ SLam i x t'
    VPi i x a b -> do
      a' <- rename m pren a
      b' <- renameClosure m pren b
      return $ SPi i x a' b'
    VU -> return SU
    VNeu (VApp (VGlobal g) sp) -> renameSp m pren (SGlobal g) sp
    VLit lit -> SLit <$> traverse (rename m pren) lit

unifySpines :: (Unify m) => Lvl -> Spine VTm -> Spine VTm -> m CanUnify
unifySpines _ Empty Empty = return Yes
unifySpines l (sp :|> Arg _ u) (sp' :|> Arg _ u') = do
  x <- unifySpines l sp sp'
  (x /\) <$> unify l u u'
unifySpines _ sp sp' = return $ No [DifferentSpineLengths sp sp']

unifyClauses :: (Unify m) => Lvl -> [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses l [] [] = return Yes
unifyClauses l (c : cs) (c' : cs') = do
  a <- unifyClause l c c'
  (a /\) <$> unifyClauses l cs cs'
unifyClauses _ a b = return $ No [DifferentClauses a b]

unifyPat :: (Unify m) => Lvl -> VPatB -> VPatB -> m CanUnify
unifyPat l (VPatB p binds) (VPatB p' binds') = do
  let n = length binds
  let n' = length binds'
  if n == n'
    then unify (nextLvls l n) p p'
    else return $ No []

unifyClause :: (Unify m) => Lvl -> Clause VPatB Closure -> Clause VPatB Closure -> m CanUnify
unifyClause l (Possible p t) (Possible p' t') = do
  a <- unifyPat l p p'
  b <- unifyClosure l t t'
  return $ a /\ b
unifyClause l (Impossible p) (Impossible p') = unifyPat l p p'
unifyClause _ a b = return $ No [DifferentClauses [a] [b]]

data Problem = Problem
  { lvl :: Lvl,
    names :: [Name],
    lhs :: VTm,
    rhs :: VTm,
    loc :: Loc,
    prevErrorString :: String
  }

addProblem :: (Unify m) => Problem -> m Int
addProblem p = do
  v <- getProblems
  modify (S.|> p)
  return $ S.length v

modifyProblem :: (Unify m) => Int -> (Problem -> Problem) -> m ()
modifyProblem i f = modify (\(p :: Seq Problem) -> S.adjust' f i p)

removeProblem :: (Unify m) => Int -> m ()
removeProblem i = modify (\(p :: Seq Problem) -> S.deleteAt i p)

indexProblem :: Int -> Seq Problem -> Problem
indexProblem i ps = S.index ps i

getProblems :: (Unify m) => m (Seq Problem)
getProblems = view

solveRemainingProblems :: (Unify m) => m CanUnify
solveRemainingProblems = do
  ps <- getProblems
  _ <-
    S.traverseWithIndex
      ( \i p -> do
          c <- unify p.lvl p.lhs p.rhs
          case c of
            No e | all unifyErrorIsMetaRelated e -> return $ Yes
            No _ -> return $ No [PrevError p.prevErrorString] -- @@Todo: keep new error
            Yes -> removeProblem i >> return Yes
      )
      ps
  return Yes

runSolveT :: (Unify m) => Lvl -> MetaVar -> Spine VTm -> VTm -> SolveT m () -> m CanUnify
runSolveT l m sp t f = do
  f' <- runExceptT f
  ns <- view
  loc <- view
  case f' of
    Left e -> do
      e' <- pretty e
      addProblem -- not if it is there already ??
        ( Problem
            { lvl = l,
              names = ns,
              lhs = VNeu (VApp (VFlex m) sp),
              rhs = t,
              loc = loc,
              prevErrorString = e' -- this is a hack
            }
        )
        >> return Yes
    Right () -> solveRemainingProblems >> return Yes

unifyFlex :: (Unify m) => Lvl -> MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyFlex l m sp t = runSolveT l m sp t $ do
  pren <- invertSpine l sp
  rhs <- rename m pren t
  solution <- lift $ uniqueSLams (reverse $ map (\a -> a.mode) (toList sp)) rhs >>= eval []
  lift $ solveMetaVar m solution

unifyRigid :: (Unify m) => Lvl -> Lvl -> Spine VTm -> VTm -> m CanUnify
unifyRigid l x Empty t = return $ Maybe (subbing l x t)
unifyRigid _ _ _ _ = return $ Maybe mempty

unfoldDefAndUnify :: (Unify m) => Lvl -> DefGlobal -> Spine VTm -> VTm -> m CanUnify
unfoldDefAndUnify l g sp t' = do
  gu <- access (unfoldDef g)
  case gu of
    Nothing -> return $ Maybe mempty
    Just gu' -> do
      t <- vApp gu' sp
      unify l t t'

unifyLit :: (Unify m) => Lvl -> Lit VTm -> VTm -> m CanUnify
unifyLit l a t = case t of
  VLit a' -> case (a, a') of
    (StringLit x, StringLit y) | x == y -> return Yes
    (CharLit x, CharLit y) | x == y -> return Yes
    (NatLit x, NatLit y) | x == y -> return Yes
    (FinLit d n, FinLit d' n') | d == d' -> unify l n n'
    _ -> return $ No [Mismatching (VLit a) (VLit a')]
  _ -> unify l (unfoldLit a) t

unifyClosure :: (Unify m) => Lvl -> Closure -> Closure -> m CanUnify
unifyClosure l cl1 cl2 = do
  t1 <- evalInOwnCtx l cl1
  t2 <- evalInOwnCtx l cl2
  if cl1.numVars == cl2.numVars
    then unify (nextLvls l cl1.numVars) t1 t2
    else error "unifyClosure: different number of variables"

etaConvert :: (Unify m) => Lvl -> VTm -> PiMode -> Closure -> m CanUnify
etaConvert l t m c = do
  x <- evalInOwnCtx l c
  x' <- vApp t (S.singleton (Arg m (VNeu (VVar l))))
  unify (nextLvl l) x x'

unify :: (Unify m) => Lvl -> VTm -> VTm -> m CanUnify
unify l t1 t2 = do
  t1' <- force t1
  t2' <- force t2
  case (t1', t2') of
    (VPi m _ t c, VPi m' _ t' c') | m == m' -> do
      a <- unify l t t'
      b <- unifyClosure l c c'
      return $ a /\ b
    (VLam m _ c, VLam m' _ c') | m == m' -> unifyClosure l c c'
    (t, VLam m' _ c') -> etaConvert l t m' c'
    (VLam m _ c, t) -> etaConvert l t m c
    (VU, VU) -> return Yes
    (t, VLit a') -> unifyLit l a' t
    (VLit a, t') -> unifyLit l a t'
    (VGlob (CtorGlob c) sp, VGlob (CtorGlob c') sp') | c == c' -> unifySpines l sp sp'
    (VGlob (DataGlob d) sp, VGlob (DataGlob d') sp') | d == d' -> unifySpines l sp sp'
    (VGlob (PrimGlob f) sp, VGlob (PrimGlob f') sp') ->
      if f == f'
        then unifySpines l sp sp'
        else return $ Maybe mempty
    (VGlob (DefGlob f) sp, VGlob (DefGlob f') sp') ->
      if f == f'
        then do
          a <- unifySpines l sp sp'
          b <- unfoldDefAndUnify l f sp t2'
          return $ a \/ b
        else unfoldDefAndUnify l f sp t2'
    (VGlob (DefGlob f) sp, t') -> unfoldDefAndUnify l f sp t'
    (t, VGlob (DefGlob f') sp') -> unfoldDefAndUnify l f' sp' t
    (VNeu (VCaseApp a s bs sp), VNeu (VCaseApp b s' bs' sp')) | a == b -> do
      c <- unify l (VNeu s) (VNeu s')
      d <- unifyClauses l bs bs'
      e <- unifySpines l sp sp'
      return $ (c /\ d /\ e) \/ Maybe mempty
    (VNeu (VReprApp m v sp), VNeu (VReprApp m' v' sp')) | m == m' && v == v' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VRigid x) sp), VNeu (VApp (VRigid x') sp')) | x == x' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VFlex x) sp), VNeu (VApp (VFlex x') sp')) | x == x' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VFlex x) sp), t') -> unifyFlex l x sp t'
    (t, VNeu (VApp (VFlex x') sp')) -> unifyFlex l x' sp' t
    (VNeu (VApp (VRigid x) sp), t') -> unifyRigid l x sp t'
    (t, VNeu (VApp (VRigid x') sp')) -> unifyRigid l x' sp' t
    (VNeu (VReprApp {}), _) -> return $ Maybe mempty
    (_, VNeu (VReprApp {})) -> return $ Maybe mempty
    (VNeu (VCaseApp {}), _) -> return $ Maybe mempty
    (_, VNeu (VCaseApp {})) -> return $ Maybe mempty
    _ -> return $ No [Mismatching t1' t2']
