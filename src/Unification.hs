module Unification (Unify (..), unify, CanUnify (..)) where

import Algebra.Lattice (Lattice (..))
import Common
  ( Arg (..),
    Clause,
    DefGlobal,
    Glob (..),
    Lit (..),
    Lvl,
    MetaVar,
    PiMode (..),
    Spine,
    Times,
    nextLvl,
    nextLvls,
    pattern Impossible,
    pattern Possible,
  )
import Control.Exception (assert)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation (Eval, evalInOwnCtx, force, vApp)
import Globals (HasSig (accessSig), KnownGlobal (..), knownCtor, knownData, unfoldDef)
import Numeric.Natural (Natural)
import Value
  ( Closure,
    Sub,
    VHead (..),
    VNeu (..),
    VPatB (..),
    VTm (..),
    numBinds,
    pattern VGl,
    pattern VVar,
  )
import Literals (unfoldLit)

data CanUnify = Yes | No | Maybe Sub

instance Lattice CanUnify where
  Yes \/ _ = Yes
  _ \/ Yes = Yes
  No \/ a = a
  a \/ No = a
  Maybe x \/ Maybe _ = Maybe x

  Yes /\ a = a
  a /\ Yes = a
  No /\ _ = No
  _ /\ No = No
  Maybe x /\ Maybe y = Maybe (x <> y)

class (Eval m) => Unify m

unifySpines :: (Unify m) => Lvl -> Spine VTm -> Spine VTm -> m CanUnify
unifySpines _ Empty Empty = return Yes
unifySpines l (sp :|> Arg _ u) (sp' :|> Arg _ u') = do
  x <- unifySpines l sp sp'
  (x /\) <$> unify l u u'
unifySpines _ _ _ = return No

unifyClauses :: (Unify m) => Lvl -> [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses l [] [] = return Yes
unifyClauses l (c : cs) (c' : cs') = do
  a <- unifyClause l c c'
  (a /\) <$> unifyClauses l cs cs'
unifyClauses _ _ _ = return No

unifyClause :: (Unify m) => Lvl -> Clause VPatB Closure -> Clause VPatB Closure -> m CanUnify
unifyClause l (Possible p t) (Possible p' t') = do
  let n = p.numBinds
  let n' = p'.numBinds
  assert (n == n') (return ())
  a <- unify (nextLvls l n) p.vPat p'.vPat
  x <- evalInOwnCtx t
  x' <- evalInOwnCtx t'
  (a /\) <$> unify (nextLvls l n) x x'
unifyClause l (Impossible p) (Impossible p') = do
  let n = p.numBinds
  let n' = p'.numBinds
  assert (n == n') (return ())
  unify (nextLvls l n) p.vPat p'.vPat
unifyClause _ _ _ = return No

unifyFlex :: (Unify m) => Lvl -> MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyFlex = undefined

unifyRigid :: (Unify m) => Lvl -> Lvl -> Spine VTm -> VTm -> m CanUnify
unifyRigid = undefined

unifyReprApp :: (Unify m) => Lvl -> Times -> VHead -> Spine VTm -> VTm -> m CanUnify
unifyReprApp = undefined

unfoldDefAndUnify :: (Unify m) => Lvl -> DefGlobal -> Spine VTm -> VTm -> m CanUnify
unfoldDefAndUnify l g sp t' = do
  gu <- accessSig (unfoldDef g)
  t <- vApp gu sp
  unify l t t'

unifyLit :: (Unify m) => Lvl -> Lit VTm -> VTm -> m CanUnify
unifyLit l a t = case t of
  VLit a' -> case (a, a') of
    (StringLit x, StringLit y) | x == y -> return Yes
    (CharLit x, CharLit y) | x == y -> return Yes
    (NatLit x, NatLit y) | x == y -> return Yes
    (FinLit d n, FinLit d' n') | d == d' -> unify l n n'
    _ -> return No
  _ -> unify l (unfoldLit a) t

unify :: (Unify m) => Lvl -> VTm -> VTm -> m CanUnify
unify l t1 t2 = do
  t1' <- force t1
  t2' <- force t2
  case (t1', t2') of
    (VPi m _ t c, VPi m' _ t' c') | m == m' -> do
      a <- unify l t t'
      x <- evalInOwnCtx c
      x' <- evalInOwnCtx c'
      (a /\) <$> unify (nextLvl l) x x'
    (VLam m _ c, VLam m' _ c') | m == m' -> do
      x <- evalInOwnCtx c
      x' <- evalInOwnCtx c'
      unify (nextLvl l) x x'
    (t, VLam m' _ c') -> do
      x <- vApp t (S.singleton (Arg m' (VNeu (VVar l))))
      x' <- evalInOwnCtx c'
      unify (nextLvl l) x x'
    (VLam m _ c, t) -> do
      x <- evalInOwnCtx c
      x' <- vApp t (S.singleton (Arg m (VNeu (VVar l))))
      unify (nextLvl l) x x'
    (VU, VU) -> return Yes
    (t, VLit a') -> unifyLit l a' t
    (VLit a, t') -> unifyLit l a t'
    (VGlobal (CtorGlob c) sp, VGlobal (CtorGlob c') sp') ->
      if c == c'
        then
          unifySpines l sp sp'
        else return No
    (VGlobal (DataGlob d) sp, VGlobal (DataGlob d') sp') ->
      if d == d'
        then
          unifySpines l sp sp'
        else return No
    (VGlobal (DefGlob f) sp, VGlobal (DefGlob f') sp') ->
      if f == f'
        then do
          a <- unifySpines l sp sp'
          b <- unfoldDefAndUnify l f sp t2'
          return $ a \/ b
        else unfoldDefAndUnify l f sp t2'
    (VGlobal (DefGlob f) sp, t') -> unfoldDefAndUnify l f sp t'
    (t, VGlobal (DefGlob f') sp') -> unfoldDefAndUnify l f' sp' t
    (VNeu (VCaseApp a s bs sp), VNeu (VCaseApp b s' bs' sp')) -> do
      if a /= b
        then return No
        else do
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
    (VNeu (VReprApp m v sp), t') -> unifyReprApp l m v sp t'
    (t, VNeu (VReprApp m' v' sp')) -> unifyReprApp l m' v' sp' t
    (VNeu (VCaseApp {}), _) -> return $ Maybe mempty
    (_, VNeu (VCaseApp {})) -> return $ Maybe mempty
    _ -> return No
