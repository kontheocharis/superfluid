module Representation (reprInfSig) where

import Common
  ( Clause (..),
    DefGlobal (..),
    Glob (..),
    Has (..),
    Logger (..),
    Lvl (..),
    PiMode (..),
    Qty (Many),
    Spine,
    Tag (..),
    mapSpineM,
    nextLvl,
    nextLvls,
  )
import Data.Sequence (Seq (..))
import Evaluation (Eval (..), caseToSpine, closureToLam, quote)
import Globals
  ( getCaseRepr,
    getGlobalRepr,
    getGlobalTags,
    mapSigContentsM,
    removeRepresentedItems,
    unfoldDef,
  )
import Syntax
  ( Case (..),
    SCase,
    SPat (..),
    STm (..),
    sAppSpine,
    sGlobWithParams,
    uniqueSLams,
  )
import Traversal (mapGlobalInfoM)

reprInfSig :: (Eval m) => m ()
reprInfSig = do
  s <- view
  let s' = removeRepresentedItems s
  s'' <- mapSigContentsM (mapGlobalInfoM (const return)) s'
  s''' <- mapSigContentsM (mapGlobalInfoM reprInf) s''
  modify (const s''')

sCaseToSpine :: (Eval m) => SCase -> m (Spine STm)
sCaseToSpine = caseToSpine id (\p -> uniqueSLams (map (const (Explicit, Many)) p.binds)) True

reprInfGlob :: (Eval m) => Lvl -> Glob -> Spine STm -> m STm
reprInfGlob l g xs = do
  d' <- access (getGlobalRepr g)
  case d' of
    Just r' -> do
      r'' <- closureToLam r'
      let res = sAppSpine r'' xs
      reprInf l res
    Nothing -> do
      xs' <- mapSpineM (reprInf l) xs
      return $ sGlobWithParams g xs'

reprInfCase :: (Eval m) => Lvl -> SCase -> m STm
reprInfCase l c = do
  r <- access (getCaseRepr c.dat)
  case r of
    Just r' -> do
      r'' <- closureToLam r'
      sp <- sCaseToSpine c
      let res = sAppSpine r'' sp
      reprInf l res
    Nothing -> do
      datParams' <- mapSpineM (reprInf l) c.datParams
      subject' <- reprInf l c.subject
      subjectIndices' <- mapSpineM (reprInf l) c.subjectIndices
      elimTy' <- reprInf l c.elimTy
      clauses' <-
        traverse
          ( \case
              Clause p t -> do
                t' <- traverse (reprInf (nextLvls l (length p.binds))) t
                return $ Clause p t'
          )
          c.clauses
      return $ SCase (Case c.dat datParams' subject' subjectIndices' elimTy' clauses')

reprInf :: (Eval m) => Lvl -> STm -> m STm
reprInf l (SPi m q x a b) = do
  a' <- reprInf l a
  b' <- reprInf (nextLvl l) b
  return $ SPi m q x a' b'
reprInf l (SLam m q x t) = do
  t' <- reprInf (nextLvl l) t
  return $ SLam m q x t'
reprInf _ SU = return SU
reprInf l (SLit t) = SLit <$> traverse (reprInf l) t
reprInf l (SApp m q a b) = do
  a' <- reprInf l a
  b' <- reprInf l b
  return $ SApp m q a' b'
reprInf l (SData d) = reprInfGlob l (DataGlob d) Empty
reprInf l (SCtor (c, xs)) = reprInfGlob l (CtorGlob c) xs
reprInf l (SDef d) = do
  ts <- access (getGlobalTags d.globalName)
  if UnfoldTag `elem` ts
    then do
      g' <- access (unfoldDef d)
      case g' of
        Just t -> quote l t >>= reprInf l
        Nothing -> error "Found UnfoldTag but no syntax for def"
    else reprInfGlob l (DefGlob d) Empty
reprInf l (SPrim p) = reprInfGlob l (PrimGlob p) Empty
reprInf l (SCase c) = reprInfCase l c
reprInf l (SRepr x) = reprInf l x
reprInf l (SUnrepr x) = reprInf l x
reprInf _ (SMeta m bs) = do
  warnMsg $ "found metavariable while representing program: " ++ show m
  return $ SMeta m bs
reprInf l (SLet q x ty t y) = do
  ty' <- reprInf l ty
  t' <- reprInf l t
  y' <- reprInf (nextLvl l) y
  return $ SLet q x ty' t' y'
reprInf _ (SVar i) = return $ SVar i
