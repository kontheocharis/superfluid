module Checking.Unification
  ( unifyTerms,
    unifyAllTerms,
    introSubst,
  )
where

import Checking.Context
  ( FlexApp (..),
    Tc,
    TcState (..),
    addSubst,
    classifyApp,
    enterCtxMod,
    freshMeta,
    inCtx,
    lookupSubst,
    modifyCtx,
    resolveInCtx,
    solveMeta,
  )
import Checking.Errors (TcError (..))
import Checking.Normalisation (expandLit, normaliseTerm, normaliseTermFully, resolveShallow)
import Checking.Utils (showSolvedMetas)
import Checking.Vars (alphaRename)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.State (gets)
import Lang
  ( PiMode (..),
    Term (..),
    TermValue (..),
    Var (..),
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
    (Just (Flex h1 ts1), _) -> solveOr h1 ts1 b (unifyTerms' a b)
    (_, Just (Flex h2 ts2)) -> solveOr h2 ts2 a (unifyTerms' a b)
    _ -> unifyTerms' a b
  where
    -- \| Unify a variable with a term. Returns True if successful.
    unifyVarWithTerm :: Term -> Var -> Term -> Tc ()
    unifyVarWithTerm vOrigin v t = do
      -- If in a pattern, then we can add a substitution straight away.
      pt <- gets (\s -> s.inPat)
      if pt
        then introSubst v t
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
    unifyTerms' (Term (Rep t) _) (Term (Rep t') _) = unifyTerms t t'
    unifyTerms' (Term (Unrep n t) _) (Term (Unrep n' t') _) | n == n' = unifyTerms t t'
    unifyTerms' a@(Term (Lit l1) _) b@(Term (Lit l2) _) = if l1 == l2 then return () else throwError $ Mismatch a b
    unifyTerms' (Term (Lit l1) _) b = unifyTerms (expandLit l1) b
    unifyTerms' a (Term (Lit l2) _) = unifyTerms a (expandLit l2)
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

-- | Introduce a substitution for a variable.
introSubst :: Var -> Term -> Tc ()
introSubst v t = do
  s <- inCtx (lookupSubst v)
  case s of
    Nothing -> modifyCtx (addSubst v t)
    Just t' -> unifyTerms t t'

-- | Unify two terms, normalising them first.
normaliseAndUnifyTerms :: Term -> Term -> Tc ()
normaliseAndUnifyTerms l r = do
  sig <- gets (\s -> s.signature)
  let l' = normaliseTerm sig l
  case l' of
    Nothing -> do
      let r' = normaliseTerm sig r
      case r' of
        Nothing -> do
          throwError $ Mismatch l r
        Just r'' -> unifyTerms l r''
    Just l'' -> do
      unifyTerms l'' r

-- | Validate a pattern unification problem, returning the spine variables.
validateProb :: Var -> [Term] -> Term -> Tc ([Var], Term)
validateProb hole spine rhs = do
  rhs' <- resolveShallow rhs

  -- Get the spine variables.
  vars <-
    mapM
      ( \x -> do
          x' <- resolveShallow x
          x'' <- resolveInCtx x'
          case (x'.value, x''.value) of
            (_, V v) -> return v
            (V v, _) -> return v
            _ -> throwError $ CannotSolveProblem hole spine rhs
      )
      spine

  -- Validate the RHS
  rhs'' <- validateRhs vars rhs'

  return (vars, rhs'')
  where
    validateRhs :: [Var] -> Term -> Tc Term
    validateRhs vs r = do
      r' <- resolveInCtx r
      case r'.value of
        Meta m | m == hole -> throwError $ CannotSolveProblem hole spine rhs
        V v | v `notElem` vs -> throwError $ VariableEscapesMeta hole spine rhs v
        SigmaT v t1 t2 -> do
          t1' <- validateRhs vs t1
          t2' <- validateRhs (v : vs) t2
          return $ Term (SigmaT v t1' t2') r'.dat
        PiT m v t1 t2 -> do
          t1' <- validateRhs vs t1
          t2' <- validateRhs (v : vs) t2
          return $ Term (PiT m v t1' t2') r'.dat
        Lam m v t -> do
          t' <- validateRhs (v : vs) t
          return $ Term (Lam m v t') r'.dat
        Let x ty t v -> do
          ty' <- validateRhs vs ty
          t' <- validateRhs vs t
          v' <- validateRhs (x : vs) v
          return $ Term (Let x ty' t' v') r'.dat
        Case t cs -> do
          t' <- validateRhs vs t
          cs' <- mapM (\(p, c) -> (,) <$> validateRhs vs p <*> validateRhs vs c) cs
          return $ Term (Case t' cs') r'.dat
        App m t1 t2 -> do
          t1' <- validateRhs vs t1
          t2' <- validateRhs vs t2
          return $ Term (App m t1' t2') r'.dat
        Pair t1 t2 -> do
          t1' <- validateRhs vs t1
          t2' <- validateRhs vs t2
          return $ Term (Pair t1' t2') r'.dat
        _ -> return r'

-- | Solve a pattern unification problem.
solve :: Var -> [Term] -> Term -> Tc ()
solve hole spine rhs = do
  (vars, rhs') <- validateProb hole spine rhs
  let solution = normaliseTermFully mempty $ lams (map (Explicit,) vars) rhs'
  solveMeta hole solution

-- | Solve a pattern unification problem, or try another action if it fails.
solveOr :: Var -> [Term] -> Term -> Tc () -> Tc ()
solveOr hole spine rhs action = solve hole spine rhs `catchError` (\e -> action `catchError` (\_ -> throwError e))
