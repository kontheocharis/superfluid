module Unification (Unify (..), unify, CanUnify (..)) where

import Algebra.Lattice (Lattice (..))
import Common
  ( Arg (..),
    Clause,
    Lvl,
    MetaVar,
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
import Globals
  ( DefGlobal,
    Glob (..),
  )
import Value
  ( Closure,
    Sub,
    VHead (..),
    VNeu (..),
    VPatB (..),
    VTm (..),
    numBinds,
    pattern VVar,
  )

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

class (Eval m) => Unify m where
  inPat :: m Bool
  setInPat :: Bool -> m ()

  enterPat :: m a -> m a
  enterPat a = do
    b <- inPat
    setInPat True
    a' <- a
    setInPat b
    return a'

  ifInPat :: m a -> m a -> m a
  ifInPat a b = do
    b' <- inPat
    if b' then a else b

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

unifyMeta :: (Unify m) => Lvl -> MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyMeta = undefined

unifyRigid :: (Unify m) => Lvl -> Lvl -> Spine VTm -> VTm -> m CanUnify
unifyRigid = undefined

unifyReprApp :: (Unify m) => Lvl -> Times -> VHead -> Spine VTm -> VTm -> m CanUnify
unifyReprApp = undefined

unfoldAndUnify :: (Unify m) => Lvl -> DefGlobal -> Spine VTm -> VTm -> m CanUnify
unfoldAndUnify = undefined

unify :: (Unify m) => Lvl -> VTm -> VTm -> m CanUnify
unify l t1 t2 = do
  t1' <- force l t1
  t2' <- force l t2
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
      x <- vApp l t (S.singleton (Arg m' (VNeu (VVar l))))
      x' <- evalInOwnCtx c'
      unify (nextLvl l) x x'
    (VLam m _ c, t) -> do
      x <- evalInOwnCtx c
      x' <- vApp l t (S.singleton (Arg m (VNeu (VVar l))))
      unify (nextLvl l) x x'
    (VU, VU) -> return Yes
    (VLit a, VLit a') | a == a' -> return Yes
    (VGlobal (CtorGlob c) sp, VGlobal (CtorGlob c') sp') -> if c == c' then unifySpines l sp sp' else return No
    (VGlobal (DataGlob d) sp, VGlobal (DataGlob d') sp') -> if d == d' then unifySpines l sp sp' else return No
    (VGlobal (DefGlob f) sp, VGlobal (DefGlob f') sp') ->
      if f == f'
        then do
          a <- unifySpines l sp sp'
          b <- unfoldAndUnify l f sp t2'
          return $ a \/ b
        else unfoldAndUnify l f sp t2'
    (VGlobal (DefGlob f) sp, t') -> unfoldAndUnify l f sp t'
    (t, VGlobal (DefGlob f') sp') -> unfoldAndUnify l f' sp' t
    (VNeu (VCase s bs), VNeu (VCase s' bs')) -> do
      a <- unify l (VNeu s) (VNeu s')
      b <- unifyClauses l bs bs'
      return $ (a /\ b) \/ Maybe mempty
    (VNeu (VReprApp m v sp), VNeu (VReprApp m' v' sp')) | m == m' && v == v' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VRigid x) sp), VNeu (VApp (VRigid x') sp')) | x == x' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VFlex x) sp), VNeu (VApp (VFlex x') sp')) | x == x' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VFlex x) sp), t') -> unifyMeta l x sp t'
    (t, VNeu (VApp (VFlex x') sp')) -> unifyMeta l x' sp' t
    (VNeu (VApp (VRigid x) sp), t') -> unifyRigid l x sp t'
    (t, VNeu (VApp (VRigid x') sp')) -> unifyRigid l x' sp' t
    (VNeu (VReprApp m v sp), t') -> unifyReprApp l m v sp t'
    (t, VNeu (VReprApp m' v' sp')) -> unifyReprApp l m' v' sp' t
    (VNeu (VCase _ _), _) -> return $ Maybe mempty
    (_, VNeu (VCase _ _)) -> return $ Maybe mempty
    _ -> return No
