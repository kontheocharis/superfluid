module Unification (Unify (..), unify, CanUnify (..)) where

import Algebra.Lattice (Lattice (..))
import Common
  ( Arg (..),
    Clause (..),
    DefGlobal,
    Glob (..),
    Lit (..),
    Lvl (..),
    MetaVar,
    PiMode (..),
    Spine,
    Times,
    lvlToIdx,
    nextLvl,
    nextLvls,
    pattern Impossible,
    pattern Possible,
  )
import Control.Exception (assert)
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Control.Monad.Trans (MonadTrans (lift))
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Either (fromRight)
import Data.Foldable (toList)
import qualified Data.IntMap as IM
import Data.Sequence (Seq (..), ViewR (..))
import qualified Data.Sequence as S
import Debug.Trace (trace, traceM)
import Evaluation (Eval, eval, evalInOwnCtx, force, vApp, ($$))
import Globals (HasSig (accessSig), KnownGlobal (..), knownCtor, knownData, unfoldDef)
import Literals (unfoldLit)
import Meta (HasMetas (solveMetaVar))
import Numeric.Natural (Natural)
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
    pattern VVar,
  )

data UnifyError = InvertError | RenameError

data CanUnify = Yes | No [UnifyError] | Maybe Sub

instance Lattice CanUnify where
  Yes \/ _ = Yes
  _ \/ Yes = Yes
  No _ \/ a = a
  a \/ No _ = a
  Maybe x \/ Maybe _ = Maybe x

  Yes /\ a = a
  a /\ Yes = a
  No xs /\ No ys = No (xs ++ ys)
  No xs /\ _ = No xs
  _ /\ No xs = No xs
  Maybe x /\ Maybe y = Maybe (x <> y)

class (Eval m) => Unify m

invertSpine :: (Unify m) => Lvl -> Spine VTm -> ExceptT UnifyError m PRen
invertSpine l Empty = return $ PRen (Lvl 0) l mempty
invertSpine l (sp' :|> Arg _ t) = do
  (PRen dom cod ren) <- invertSpine l sp'
  f <- lift $ force t
  case f of
    VNeu (VVar (Lvl l')) | IM.notMember l' ren -> return $ PRen (nextLvl dom) cod (IM.insert l' dom ren)
    _ -> throwError InvertError

renameSp :: (Unify m) => MetaVar -> PRen -> STm -> Spine VTm -> ExceptT UnifyError m STm
renameSp m pren t Empty = return t
renameSp m pren t (sp :|> Arg i u) = do
  xs <- renameSp m pren t sp
  ys <- rename m pren u
  return $ SApp i xs ys

renameClosure :: (Unify m) => MetaVar -> PRen -> Closure -> ExceptT UnifyError m STm
renameClosure m pren cl = do
  vt <- lift $ evalInOwnCtx cl
  rename m (liftPRenN cl.numVars pren) vt

renamePat :: (Unify m) => MetaVar -> PRen -> VPatB -> ExceptT UnifyError m SPat
renamePat m pren (VPatB p binds) = do
  let n = length binds
  p' <- rename m (liftPRenN n pren) p
  return $ SPat p' binds

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: (Unify m) => MetaVar -> PRen -> VTm -> ExceptT UnifyError m STm
rename m pren tm = do
  f <- lift $ force tm
  case f of
    VNeu (VApp (VFlex m') sp)
      | m == m' -> throwError RenameError -- occurs check
      | otherwise -> renameSp m pren (SMeta m' []) sp
    VNeu (VApp (VRigid (Lvl x)) sp) -> case IM.lookup x pren.vars of
      Nothing -> throwError RenameError -- scope error ("escaping variable" error)
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
    VGlobal g sp -> renameSp m pren (SGlobal g) sp
    VLit lit -> SLit <$> traverse (rename m pren) lit

unifySpines :: (Unify m) => Lvl -> Spine VTm -> Spine VTm -> m CanUnify
unifySpines _ Empty Empty = return Yes
unifySpines l (sp :|> Arg _ u) (sp' :|> Arg _ u') = do
  x <- unifySpines l sp sp'
  (x /\) <$> unify l u u'
unifySpines _ _ _ = return $ No []

unifyClauses :: (Unify m) => Lvl -> [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses l [] [] = return Yes
unifyClauses l (c : cs) (c' : cs') = do
  a <- unifyClause l c c'
  (a /\) <$> unifyClauses l cs cs'
unifyClauses _ _ _ = return $ No []

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
unifyClause _ _ _ = return $ No []

handleUnifyError :: (Unify m) => ExceptT UnifyError m () -> m CanUnify
handleUnifyError f = do
  f' <- runExceptT f
  case f' of
    Left e -> return $ No [e]
    Right () -> return Yes

unifyFlex :: (Unify m) => Lvl -> MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyFlex l m sp t = handleUnifyError $ do
  pren <- invertSpine l sp
  rhs <- rename m pren t
  solution <- lift $ uniqueSLams (reverse $ map (\a -> a.mode) (toList sp)) rhs >>= eval []
  lift $ solveMetaVar m solution

unifyRigid :: (Unify m) => Lvl -> Lvl -> Spine VTm -> VTm -> m CanUnify
unifyRigid _ x Empty t = return $ Maybe (subbing x t)
unifyRigid _ _ _ _ = return $ Maybe mempty

unfoldDefAndUnify :: (Unify m) => Lvl -> DefGlobal -> Spine VTm -> VTm -> m CanUnify
unfoldDefAndUnify l g sp t' = do
  gu <- accessSig (unfoldDef g)
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
    _ -> return $ No []
  _ -> unify l (unfoldLit a) t

unifyClosure :: (Unify m) => Lvl -> Closure -> Closure -> m CanUnify
unifyClosure l cl1 cl2 = do
  t1 <- evalInOwnCtx cl1
  t2 <- evalInOwnCtx cl2
  if cl1.numVars == cl2.numVars
    then unify (nextLvls l cl1.numVars) t1 t2
    else return $ No []

etaConvert :: (Unify m) => Lvl -> VTm -> PiMode -> Closure -> m CanUnify
etaConvert l t m c = do
  x <- evalInOwnCtx c
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
    (VGlobal (CtorGlob c) sp, VGlobal (CtorGlob c') sp') | c == c' -> unifySpines l sp sp'
    (VGlobal (DataGlob d) sp, VGlobal (DataGlob d') sp') | d == d' -> unifySpines l sp sp'
    (VGlobal (PrimGlob f) sp, VGlobal (PrimGlob f') sp') ->
      if f == f'
        then unifySpines l sp sp'
        else return $ Maybe mempty
    (VGlobal (DefGlob f) sp, VGlobal (DefGlob f') sp') ->
      if f == f'
        then do
          a <- unifySpines l sp sp'
          b <- unfoldDefAndUnify l f sp t2'
          return $ a \/ b
        else unfoldDefAndUnify l f sp t2'
    (VGlobal (DefGlob f) sp, t') -> unfoldDefAndUnify l f sp t'
    (t, VGlobal (DefGlob f') sp') -> unfoldDefAndUnify l f' sp' t
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
    _ -> return $ No []
