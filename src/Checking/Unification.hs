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
    freshMeta,
    inCtx,
    lookupSubst,
    modifyCtx,
    resolveInCtx,
    solveMeta,
  )
import Checking.Errors (TcError (..))
import Checking.Normalisation (expandLit, normaliseTerm, normaliseTermFully, resolveDeep, resolveShallow)
import Checking.Vars (alphaRename)
import Control.Monad (when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.State (gets)
import Debug.Trace (traceM)
import Interface.Pretty (Print (printVal))
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

onlyPotential :: Tc () -> Tc ()
onlyPotential f =
  f
    `catchError` ( \e -> case e of
                     PotentialMismatch _ _ -> return ()
                     Many es -> do
                       let es' =
                             filter
                               ( \case
                                   PotentialMismatch _ _ -> True
                                   _ -> False
                               )
                               es
                       when (null es') $ throwError e
                     _ -> throwError e
                 )

definite :: Tc () -> Tc ()
definite f =
  f
    `catchError` ( \e -> case e of
                     PotentialMismatch l r -> throwError $ Mismatch l r
                     Many es ->
                       throwError $
                         Many
                           ( map
                               ( \e' -> case e' of
                                   PotentialMismatch l r -> Mismatch l r
                                   _ -> e'
                               )
                               es
                           )
                     _ -> throwError e
                 )

-- \| Unify two terms.
-- This might produce a substitution.
-- Unification is symmetric.
unifyTerms :: Term -> Term -> Tc ()
unifyTerms a' b' = do
  a <- resolveShallow a'
  b <- resolveShallow b'

  pt <- gets (\s -> s.inPat)
  let process = if pt then onlyPotential else definite

  case (classifyApp a, classifyApp b) of
    (Just (Flex v1 _), Just (Flex v2 _)) | v1 == v2 -> process $ unifyTerms' a b
    (Just (Flex h1 ts1), _) -> solve h1 ts1 b
    (_, Just (Flex h2 ts2)) -> solve h2 ts2 a
    _ -> process $ unifyTerms' a b
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
    unifyTerms' a@(Term (V l) _) b@(Term (V r) _) = unifyVarWithTerm a l b `catchError` (\e -> unifyVarWithTerm b r a `catchError` (\e' -> throwError (e <> e')))
    unifyTerms' a@(Term (V l) _) b = unifyVarWithTerm a l b `catchError` (\e -> normaliseAndUnifyTerms a b (PotentialMismatch a b <> e))
    unifyTerms' a b@(Term (V r) _) = unifyVarWithTerm b r a `catchError` (\e -> normaliseAndUnifyTerms a b (PotentialMismatch a b <> e))
    unifyTerms' a@(Term (Global l) _) b@(Term (Global r) _) =
      if l == r
        then return ()
        else normaliseAndUnifyTerms a b (Mismatch a b)
    unifyTerms' a@(Term (Case _ su1 cs1) _) b@(Term (Case _ su2 cs2) _) = do
      unifyTerms su1 su2
      mapM_
        ( \((p1, t1), (p2, t2)) -> do
            unifyTerms p1 p2
            case (t1, t2) of
              (Just t1', Just t2') -> unifyTerms t1' t2'
              (Nothing, Nothing) -> return ()
              _ -> throwError $ Mismatch a b
        )
        (zip cs1 cs2)
    -- unifyTerms' a@(Term (Case ))
    unifyTerms' a@(Term (App m1 l1 l2) _) b@(Term (App m2 r1 r2) _)
      | m1 == m2 -- @@Fixme : This is wrong! Inconsistent for non-injective l1/r1
        =
          do
            unifyTerms l1 r1
            unifyTerms l2 r2
            `catchError` (\e -> normaliseAndUnifyTerms a b (PotentialMismatch a b <> e))
    unifyTerms' l r = normaliseAndUnifyTerms l r (PotentialMismatch l r)

-- | Introduce a substitution for a variable.
introSubst :: Var -> Term -> Tc ()
introSubst v t = do
  s <- inCtx (lookupSubst v)
  case s of
    Nothing -> modifyCtx (addSubst v t)
    Just t' -> unifyTerms t t'

-- @@Fixme: if they dont unify because we *don't know if they are equal* we should just remove the previous substitution??
-- unifyTerms t t' `catchError` (\_ -> return ()) -- If the terms don't unify, just ignore the substitution.

-- | Unify two terms, normalising them first.
normaliseAndUnifyTerms :: Term -> Term -> TcError -> Tc ()
normaliseAndUnifyTerms l r err = do
  c <- gets (\s -> s.ctx)
  sig <- gets (\s -> s.signature)
  l' <- resolveDeep l
  let l'' = normaliseTerm c sig l'
  case l'' of
    Nothing -> do
      r' <- resolveDeep r
      let r'' = normaliseTerm c sig r'
      case r'' of
        Nothing -> do
          throwError err
        Just r''' -> do
          unifyTerms l r'''
    Just l''' -> do
      unifyTerms l''' r

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
      r' <- resolveShallow r >>= resolveInCtx
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
        Case e t cs -> do
          e' <- traverse (validateRhs vs) e
          t' <- validateRhs vs t
          cs' <- mapM (\(p, c) -> (,) <$> validateRhs vs p <*> traverse (validateRhs vs) c) cs
          return $ Term (Case e' t' cs') r'.dat
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
  let solution = normaliseTermFully mempty mempty $ lams (map (Explicit,) vars) rhs'
  solveMeta hole solution
