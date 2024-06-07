module Checking.Unification (unifyTerms, unifyAllTerms) where

import Checking.Context
  ( FlexApp (..),
    Tc,
    TcState (..),
    addSubst,
    classifyApp,
    freshMeta,
    inCtx,
    lookupSubst,
    modifyCtx,
    solveMeta,
  )
import Checking.Errors (TcError (..))
import Checking.Normalisation (normaliseTerm, normaliseTermFully, resolveShallow)
import Checking.Vars (alphaRename)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.State (gets)
import Lang
  ( PiMode (..),
    Term (..),
    TermValue (..),
    Var,
    lams,
  )

-- | Unify the list of terms together into a meta.
unifyAllTerms :: [Term] -> Tc Term
unifyAllTerms ts = do
  m <- freshMeta
  mapM_ (unifyTerms m) ts
  return m

-- \| Unify two terms.
-- This might produce a substitution.
-- Unification is symmetric.
unifyTerms :: Term -> Term -> Tc ()
unifyTerms a' b' = do
  a <- resolveShallow a'
  b <- resolveShallow b'
  case (classifyApp a, classifyApp b) of
    (Just (Flex v1 _), Just (Flex v2 _)) | v1 == v2 -> unifyTerms' a b
    (Just (Flex h1 ts1), _) -> do
      res <- solve h1 ts1 b
      if res
        then return ()
        else unifyTerms' a b
    (_, Just (Flex h2 ts2)) -> do
      res <- solve h2 ts2 a
      if res
        then return ()
        else unifyTerms' a b
    _ -> unifyTerms' a b
  where
    -- \| Unify a variable with a term. Returns True if successful.
    unifyVarWithTerm :: Term -> Var -> Term -> Tc ()
    unifyVarWithTerm vOrigin v t = do
      -- If in a pattern, then we can add a substitution straight away.
      pt <- gets (\s -> s.inPat)
      if pt
        then modifyCtx (addSubst v t)
        else do
          -- Check if the variable exists in a substitution in
          -- the context.
          subst <- inCtx (lookupSubst v)
          case subst of
            Just s -> unifyTerms s t
            Nothing -> throwError $ Mismatch vOrigin t

    unifyTerms' :: Term -> Term -> Tc ()
    unifyTerms' (Term (Meta m1) _) (Term (Meta m2) _) | m1 == m2 = return ()
    unifyTerms' (Term (PiT m1 lv l1 l2) d1) (Term (PiT m2 rv r1 r2) _) | m1 == m2 = do
      unifyTerms l1 r1
      unifyTerms l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (SigmaT lv l1 l2) d1) (Term (SigmaT rv r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (Lam m1 lv l) d1) (Term (Lam m2 rv r) _) | m1 == m2 = do
      unifyTerms l (alphaRename rv (lv, d1) r)
    unifyTerms' (Term (Pair l1 l2) _) (Term (Pair r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 r2
    unifyTerms' (Term TyT _) (Term TyT _) = return ()
    unifyTerms' (Term (V l) _) (Term (V r) _) | l == r = return ()
    unifyTerms' a@(Term (V l) _) b@(Term (V r) _) = do
      unifyVarWithTerm a l b `catchError` (\_ -> unifyVarWithTerm b r a)
    unifyTerms' a@(Term (V l) _) b = unifyVarWithTerm a l b
    unifyTerms' a b@(Term (V r) _) = unifyVarWithTerm b r a
    unifyTerms' a@(Term (Global l) _) b@(Term (Global r) _) =
      if l == r
        then return ()
        else normaliseAndUnifyTerms a b
    unifyTerms' (Term (Case su1 cs1) _) (Term (Case su2 cs2) _) = do
      unifyTerms su1 su2
      mapM_
        ( \((p1, t1), (p2, t2)) -> do
            unifyTerms p1 p2
            unifyTerms t1 t2
        )
        (zip cs1 cs2)
    unifyTerms' a@(Term (App m1 l1 l2) _) b@(Term (App m2 r1 r2) _)
      | m1 == m2 =
          do
            unifyTerms l1 r1
            unifyTerms l2 r2
            `catchError` (\_ -> normaliseAndUnifyTerms a b)
    unifyTerms' l r = normaliseAndUnifyTerms l r

-- | Unify two terms, normalising them first.
normaliseAndUnifyTerms :: Term -> Term -> Tc ()
normaliseAndUnifyTerms l r = do
  let l' = normaliseTerm l
  case l' of
    Nothing -> do
      let r' = normaliseTerm r
      case r' of
        Nothing -> throwError $ Mismatch l r
        Just r'' -> unifyTerms l r''
    Just l'' -> do
      unifyTerms l'' r

-- | Validate a pattern unification problem, returning the spine variables.
validateProb :: Var -> [Term] -> Term -> Tc (Maybe [Var])
validateProb _ [] _ = return (Just [])
validateProb hole (x : xs) rhs = do
  x' <- resolveShallow x
  case x'.value of
    V v -> do
      xs' <- validateProb hole xs rhs
      return $ (v :) <$> xs'
    _ -> return Nothing

-- | Solve a pattern unification problem.
solve :: Var -> [Term] -> Term -> Tc Bool
solve hole spine rhs = do
  vars <- validateProb hole spine rhs
  case vars of
    Nothing -> return False
    Just vars' -> do
      let solution = normaliseTermFully (lams (map (Explicit,) vars') rhs)
      solveMeta hole solution
      return True
