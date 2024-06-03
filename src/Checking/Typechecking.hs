{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Checking.Typechecking
  ( checkTerm,
    unifyTerms,
    inferTerm,
    normaliseTermFully,
    checkProgram,
    representProgram,
  )
where

import Checking.Context
  ( FlexApp (..),
    Tc,
    TcError (..),
    TcState (..),
    addCaseItemToRepr,
    addCtorItemToRepr,
    addEmptyDataItemToRepr,
    addEmptyRepr,
    addItem,
    addItemToRepr,
    addItems,
    addSubst,
    addTyping,
    addTypings,
    classifyApp,
    enterCtx,
    enterCtxMod,
    enterPat,
    enterSignatureMod,
    findReprForCase,
    findReprForGlobal,
    freshMeta,
    freshMetaAt,
    freshVar,
    getDataItem,
    getType,
    inCtx,
    inSignature,
    lookupItemOrCtor,
    lookupSubst,
    lookupType,
    modifyCtx,
    modifySignature,
    registerHole,
    registerWild,
    setType,
    solveMeta,
  )
import Checking.Vars (alphaRename, subVar)
import Control.Monad (filterM, replicateM, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.State (gets)
import Data.Foldable (find)
import Data.List (sort, sortBy)
import Data.Map (Map, lookup, (!?))
import Data.Maybe (fromJust)
import Lang
  ( CtorItem (..),
    DataItem (..),
    DeclItem (..),
    HasLoc (..),
    Item (..),
    Loc,
    MapResult (..),
    Pat,
    Program (..),
    ReprDataCaseItem (..),
    ReprDataCtorItem (..),
    ReprDataItem (..),
    ReprDeclItem (ReprDeclItem),
    ReprItem (..),
    ReprSomeItem (..),
    Term (..),
    TermMappable (mapTermMappableM),
    TermValue (..),
    Type,
    TypeValue,
    Var,
    appToList,
    genTerm,
    lams,
    listToApp,
    listToPiType,
    locatedAt,
    mapTermM,
    piTypeToList,
    typedAs,
  )
import Lang as DI (DeclItem (..), TermMappable (mapTermMappable))

-- | Check the program
checkProgram :: Program -> Tc Program
checkProgram (Program decls) = do
  p <- Program <$> mapM checkItem decls
  types <- gets (\s -> s.termTypes)
  p' <- mapTermMappableM fillAllMetas p
  mapTermMappableM (fillType types) p'
  where
    fillType :: Map Loc Type -> Term -> Tc (MapResult Term)
    fillType types t = case types !? getLoc t of
      Just ty -> do
        ty' <- mapTermM fillAllMetas ty
        return $ ReplaceAndContinue (typedAs ty' t)
      Nothing -> return Continue

-- | Fill all the metavariables in a term.
fillAllMetas :: Term -> Tc (MapResult Term)
fillAllMetas t = ReplaceAndContinue <$> resolveFinal t

-- | Resolve a term by filling in metas if present, or turning them back into holes.
resolveFinal :: Term -> Tc Term
resolveFinal t = do
  case classifyApp t of
    Just (Flex h ts) -> do
      metas <- gets (\s -> s.metaValues)
      case metas !? h of
        Just t' -> do
          -- If the meta is already solved, then we can resolve the term.
          r <- resolveShallow (listToApp (t', ts))
          return $ normaliseTermFully r
        Nothing -> do
          -- If the meta is not resolved, then substitute the original hole
          let tLoc = getLoc t
          hole <- gets (\s -> Data.Map.lookup tLoc s.holeLocs)
          case hole of
            Just (Just v) -> return $ locatedAt tLoc (Hole v)
            Just Nothing -> return $ locatedAt tLoc Wild
            Nothing -> do
              -- If the hole is not registered, then it is a fresh hole.
              locatedAt tLoc . Hole <$> freshVar
    _ -> return t

-- | Resolve a term by filling in metas if present.
resolveShallow :: Term -> Tc Term
resolveShallow (Term (Meta h) d) = do
  metas <- gets (\s -> s.metaValues)
  case metas !? h of
    Just t -> resolveShallow t
    Nothing -> return $ Term (Meta h) d
resolveShallow (Term (App t1 t2) d) = do
  t1' <- resolveShallow t1
  return $ normaliseTermFully (Term (App t1' t2) d)
resolveShallow t = return t

-- | Represent a checked program
representProgram :: Program -> Tc Program
representProgram (Program decls) = do
  -- Filter out all the (checked) repr items from the program
  let (reprs, rest) =
        foldr
          ( \x (reprs', rest') -> case x of
              Repr r -> (Repr r : reprs', rest')
              _ -> (reprs', x : rest')
          )
          ([], [])
          decls

  -- Add them to the signature
  modifySignature $ addItems reprs

  -- Then, represent all the items in the program
  Program rest' <- mapTermMappableM representTermRec (Program rest)

  -- Finally, normalise the program
  return $ mapTermMappable (ReplaceAndContinue . normaliseTermFully) (Program rest')

-- | Check some item in the program.
checkItem :: Item -> Tc Item
checkItem (Decl decl) = Decl <$> checkDeclItem decl
checkItem (Data dat) = Data <$> checkDataItem dat
checkItem (Repr r) = Repr <$> checkReprItem r

-- | Check a repr item.
checkReprItem :: ReprItem -> Tc ReprItem
checkReprItem (ReprItem name cs) = do
  -- Check each item and add it to the context.
  modifySignature (addEmptyRepr name)
  cs' <- mapM (checkSomeReprItem name) cs
  return (ReprItem name cs')

-- | Check an item inside a repr.
checkSomeReprItem :: String -> ReprSomeItem -> Tc ReprSomeItem
checkSomeReprItem rName (ReprData d) = ReprData <$> checkReprDataItem rName d
checkSomeReprItem _ (ReprDecl d) = ReprDecl <$> checkReprDeclItem d

-- | Check that a term (t x1..xn) is a valid (full) application of a pi type.
--
-- Also takes a closure to run more stuff in the same context, given the goal.
checkBindAppMatchesPi :: Term -> [Var] -> Type -> (Type -> Tc a) -> Tc a
checkBindAppMatchesPi subject binds ty f = do
  let (params, ret) = piTypeToList ty
  let typings = zipWith (curry (\(b, (_, t)) -> (b, t))) binds params
  enterCtxMod (addTypings typings) $ do
    -- Check that the LHS fully applied is a type
    let lhs = listToApp (subject, map (genTerm . V) binds)
    _ <- checkTerm lhs ret
    return ()
  typings' <- mapM (\(b, t) -> (,) b <$> representTerm t) typings
  enterCtxMod (addTypings typings') $ do
    ret' <- representTerm ret
    f ret'

-- | Check a repr data item.
checkReprDataItem :: String -> ReprDataItem -> Tc ReprDataItem
checkReprDataItem rName (ReprDataItem name binds target ctors cse) = do
  -- Ensure that the name exists
  decl <- inSignature (lookupItemOrCtor name)
  case decl of
    Just (Left (Data d)) -> do
      -- Check the type:
      target' <- checkBindAppMatchesPi (genTerm (Global name)) binds d.ty $ \ret -> do
        -- Check that the target is also of the same (represented!) type
        (target', _) <- checkTerm target ret
        return target'

      -- Check that all the constructors are present
      let given = map (\c -> c.name) ctors
      let expected = map (\c -> c.name) d.ctors
      when (sort given /= sort expected) $ throwError $ WrongConstructors given expected

      -- Add the data type to the context without constructors
      modifySignature $ addEmptyDataItemToRepr rName name binds target'

      -- Check each constructor
      ctors' <- mapM (checkReprDataCtorItem rName d.name) ctors

      -- Check the case expression
      cse' <- traverse (checkReprDataCaseItem rName d) cse

      -- Add the final data type to the context
      let result = ReprDataItem name binds target' ctors' cse'
      modifySignature $ addItemToRepr rName (ReprData result)

      return result
    _ -> throwError $ ItemNotFound name

-- | Check a repr data constructor item.
checkReprDataCtorItem :: String -> String -> ReprDataCtorItem -> Tc ReprDataCtorItem
checkReprDataCtorItem rName dName (ReprDataCtorItem name binds target) = do
  -- Ensure that the name exists
  decl <- inSignature (lookupItemOrCtor name)
  case decl of
    Just (Right (CtorItem _ ty _ _)) -> do
      -- Check the target against the represented constructor type
      target' <- checkBindAppMatchesPi (genTerm (Global name)) binds ty $ \ret -> do
        -- Check that the target is also of the same type
        (target', _) <- checkTerm target ret
        return target'

      -- Add the constructor to the context
      let result = ReprDataCtorItem name binds target'
      modifySignature $ addCtorItemToRepr rName dName result

      return result
    _ -> throwError $ ItemNotFound name

-- | Check a repr data case item.
checkReprDataCaseItem :: String -> DataItem -> ReprDataCaseItem -> Tc ReprDataCaseItem
checkReprDataCaseItem rName dat (ReprDataCaseItem (subject, ctors) target) = do
  -- Ensure that all the constructors are present
  let given = map fst ctors
  let expected = map (\c -> c.name) dat.ctors
  when (sort given /= sort expected) $ throwError $ WrongConstructors given expected

  -- Type of the subject is the represented data type
  let (params, _) = piTypeToList dat.ty
  let subjectTy = listToApp (genTerm (Global dat.name), map (genTerm . V . fst) params)
  subjectReprIndices <- mapM (\(a, b) -> (a,) <$> representTerm b) params
  subjectReprTy <- representTerm subjectTy

  -- Form the elimination type family
  elimTySubjectVar <- freshVar
  let elimFam = listToPiType (params ++ [(elimTySubjectVar, subjectTy)], genTerm TyT)
  elimReprFam <- representTerm elimFam
  elimName <- freshVar

  -- Form the elimination type
  let elimTy = listToApp (genTerm (V elimName), map snd subjectReprIndices ++ [genTerm (V subject)])

  -- Gather all the eliminators
  eliminators <-
    mapM
      ( \(cName, cBind) -> do
          -- Represented constructor parameters
          let c = fromJust (find (\n -> n.name == cName) dat.ctors)
          let (ctorParams, ctorRet) = piTypeToList c.ty
          ctorReprParams <- mapM (\(a, b) -> (a,) <$> representTerm b) ctorParams

          -- Represented constructor return indices
          let (_, ctorRetIndices) = appToList ctorRet
          ctorReprRetIndices <- mapM representTerm ctorRetIndices

          -- Represented constructor return type
          let ctorParamVarTerms = map (genTerm . V . fst) ctorParams
          let ctorRetTy = listToApp (genTerm (Global c.name), ctorParamVarTerms)
          ctorReprRetTy <- representTerm ctorRetTy

          -- Form the eliminator type
          let elimCtorTy =
                listToPiType
                  ( ctorReprParams,
                    listToApp
                      ( genTerm (V elimName),
                        ctorReprRetIndices
                          ++ [ctorReprRetTy]
                      )
                  )

          -- The eliminator is bound to the given binding in the case
          -- representation.
          return (cBind, elimCtorTy)
      )
      ctors

  -- Overall the RHS of a case representation should have in context:
  -- 1. The subject indices
  -- 2. The subject type
  -- 3. The subject itself
  -- 4. The elimination indices
  -- 5. The elimination type
  -- 6. For each constructor, the eliminator
  target' <- enterCtxMod (addTypings (subjectReprIndices ++ [(subject, subjectReprTy), (elimName, elimReprFam)] ++ eliminators)) $ do
    -- Check the target
    (target', _) <- checkTerm target elimTy
    return target'

  -- Add the case representation to the context
  let result = ReprDataCaseItem (elimTySubjectVar, ctors) target'
  modifySignature $ addCaseItemToRepr rName dat.name result
  return result

-- | Check a repr decl item.
checkReprDeclItem :: ReprDeclItem -> Tc ReprDeclItem
checkReprDeclItem (ReprDeclItem name target) = do
  -- Ensure that the name exists
  decl <- inSignature (lookupItemOrCtor name)
  case decl of
    Just (Left (Decl d)) -> do
      rDeclTy <- representTerm d.ty
      -- Check the target against the represented declaration type
      (target', _) <- checkTerm target rDeclTy
      let result = ReprDeclItem name target'
      modifySignature $ addItemToRepr name (ReprDecl result)
      return result
    _ -> throwError $ ItemNotFound name

-- | Convert a list of case eliminations to a list of arguments for the "represented" application.
-- Assumes the case expression has already been checked.
caseElimsToAppArgs :: String -> [(Pat, Term)] -> Tc [Term]
caseElimsToAppArgs dName clauses = do
  dCtors <- inSignature (getDataItem dName)
  clauses' <-
    sortBy
      (\(p1, _) (p2, _) -> compare p1 p2)
      <$> mapM
        ( \(p, t) -> do
            let (h, xs) = appToList p
            -- Ensure the pattern head is a global variable that corresponds to
            -- a constructor.
            (c, idx) <- case h of
              Term (Global c) _ ->
                return
                  ( c,
                    (fromJust $ find (\n -> n.name == c) dCtors.ctors).idx
                  )
              _ -> throwError $ PatternNotSupported p

            -- Ensure the pattern arguments are variables.
            xs' <-
              mapM
                ( \case
                    Term (V v) _ -> return v
                    _ -> throwError (PatternNotSupported p)
                )
                xs
            return (idx, (c, lams xs' t))
        )
        clauses

  -- Ensure all the constructors are present
  if map fst clauses' /= [0 .. length dCtors.ctors - 1]
    then throwError $ WrongConstructors (map (fst . snd) clauses') (map (\c -> c.name) dCtors.ctors)
    else return $ map (snd . snd) clauses'

-- | Represent a checked term through defined representations.
representTermRec :: Term -> Tc (MapResult Term)
representTermRec = \case
  Term (Global g) _ -> do
    r <- findReprForGlobal g
    case r of
      Nothing -> return Continue
      Just (_, term) -> return $ ReplaceAndContinue term
  Term (Case s cs) _ -> do
    sTy <- getType s
    case sTy of
      Just t -> case appToList t of
        (Term (Global g) _, _) -> do
          r <- findReprForCase g
          case r of
            Nothing -> return Continue
            Just (dName, term) -> do
              xs <- caseElimsToAppArgs dName cs
              return $ ReplaceAndContinue (listToApp (term, xs))
        _ -> return Continue
      _ -> return Continue
  _ -> return Continue

-- | Represent a checked term through defined representations.
representTerm :: Term -> Tc Term
representTerm = mapTermM representTermRec

-- | Check a data item.
checkDataItem :: DataItem -> Tc DataItem
checkDataItem (DataItem name ty ctors) = do
  -- Check the signature of the data type.
  (ty', _) <- checkTerm ty (locatedAt ty TyT)
  let (_, ret) = piTypeToList ty'
  unifyTerms ret (locatedAt ret TyT)

  -- Then, add the declaration to the context.
  ctors' <- enterSignatureMod (addItem (Data (DataItem name ty' ctors))) $ do
    -- Then, check each constructor.
    mapM (checkCtorItem ty') ctors

  -- Now add the final data type to the context.
  let dTy = DataItem name ty' ctors'
  modifySignature (addItem (Data dTy))
  return dTy

checkCtorItem :: Type -> CtorItem -> Tc CtorItem
checkCtorItem dTy (CtorItem name ty i dTyName) = do
  -- The amount of arguments of the data type
  let dTyArgCount = length . fst $ piTypeToList dTy

  -- Check the signature of the constructor.
  (ty', _) <- checkTerm ty (genTerm TyT)
  let (tys, ret) = piTypeToList ty'

  -- \| Add all the arguments to the context
  enterCtxMod (\c -> foldr (\(v, t) c' -> addTyping v t c') c tys) $ do
    -- \| Check that the return type is the data type.
    dummyArgs <- replicateM dTyArgCount freshMeta
    let dummyRet = listToApp (genTerm (Global dTyName), dummyArgs)
    unifyTerms ret dummyRet

  return (CtorItem name ty' i dTyName)

-- | Check a declaration.
-- This is self-contained, so it does not produce a substitution.
checkDeclItem :: DeclItem -> Tc DeclItem
checkDeclItem decl = do
  -- First, check the type of the declaration.
  let ty = decl.ty
  (ty', _) <- checkTerm ty (genTerm TyT)

  -- Add the partially checked decl to the context and check the body
  (tm', ty'') <- enterSignatureMod (addItem (Decl $ decl {DI.ty = ty'})) $ do
    let tm = decl.value
    checkTerm tm ty'

  -- Add the final decl to the context
  let decl' = DeclItem decl.name ty'' tm' decl.loc
  modifySignature (addItem (Decl decl'))

  return decl'

-- | Check the type of a term, and set the type in the context.
checkTerm :: Term -> Type -> Tc (Term, Type)
checkTerm v t = do
  (v', t') <- checkTerm' v t
  setType v t'
  return (v', t')

-- | Check the type of a term.
--
-- The location of the type is inherited from the term.
checkTermExpected :: Term -> TypeValue -> Tc (Term, Type)
checkTermExpected v t = checkTerm v (locatedAt v t)

-- | Unify two terms and return the first one.
unifyTermsTo :: Term -> Term -> Tc Term
unifyTermsTo t1 t2 = do
  unifyTerms t1 t2
  return t1

-- | Check the type of a term. (The type itself should already be checked.)
--
-- This also performs elaboration by filling named holes and wildcards with metavariables.
checkTerm' :: Term -> Type -> Tc (Term, Type)
checkTerm' ((Term (Lam v t) d1)) ((Term (PiT var' ty1 ty2) d2)) = do
  (t', ty2') <- enterCtxMod (addTyping v ty1) $ checkTerm t (alphaRename var' (v, d2) ty2)
  return (locatedAt d1 (Lam v t'), locatedAt d2 (PiT var' ty1 ty2'))
checkTerm' ((Term (Lam v t1) d1)) typ = do
  varTy <- freshMeta
  (t1', bodyTy) <- enterCtxMod (addTyping v varTy) $ inferTerm t1
  typ' <- unifyTermsTo typ $ locatedAt d1 (PiT v varTy bodyTy)
  return (locatedAt d1 (Lam v t1'), typ')
checkTerm' (Term (Pair t1 t2) d1) (Term (SigmaT v ty1 ty2) d2) = do
  (t1', ty1') <- checkTerm t1 ty1
  (t2', ty2') <- checkTerm t2 (subVar v t1 ty2)
  return (locatedAt d1 (Pair t1' t2'), locatedAt d2 (SigmaT v ty1' ty2'))
checkTerm' (Term (Pair t1 t2) d1) typ = do
  (t1', ty1) <- inferTerm t1
  (t2', ty2) <- inferTerm t2
  v <- freshVar
  typ' <- unifyTermsTo typ $ locatedAt d1 (SigmaT v ty1 ty2)
  return (locatedAt d1 (Pair t1' t2'), typ')
checkTerm' (Term (PiT v t1 t2) d1) typ = do
  (t1', _) <- checkTermExpected t1 TyT
  (t2', _) <- enterCtxMod (addTyping v t1) $ checkTermExpected t2 TyT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (PiT v t1' t2'), typ')
checkTerm' (Term (SigmaT v t1 t2) d1) typ = do
  (t1', _) <- checkTermExpected t1 TyT
  (t2', _) <- enterCtxMod (addTyping v t1) $ checkTermExpected t2 TyT
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (locatedAt d1 (SigmaT v t1' t2'), typ')
checkTerm' (Term TyT d1) typ = do
  typ' <- unifyTermsTo typ (locatedAt d1 TyT)
  return (Term TyT d1, typ')
checkTerm' t@(Term (V v) _) typ = do
  vTyp <- inCtx (lookupType v)
  case vTyp of
    Nothing -> do
      -- If we are in a pattern, then this is a bound variable so we can add it
      -- to the context.
      p <- gets (\s -> s.inPat)
      if p
        then do
          modifyCtx (addTyping v typ)
          return (t, typ)
        else throwError $ VariableNotFound v
    Just vTyp' -> do
      typ' <- unifyTermsTo typ vTyp'
      return (t, typ')
checkTerm' (Term (App t1 t2) _) typ = do
  (t1', subjectTy) <- inferTerm t1
  subjectTyRes <- resolveShallow subjectTy

  let go v varTy bodyTy = do
        (t2', _) <- checkTerm t2 varTy
        typ' <- unifyTermsTo typ $ subVar v t2' bodyTy
        return (locatedAt t1 (App t1' t2'), typ')

  -- Try to normalise to a pi type.
  case subjectTyRes of
    (Term (PiT v varTy bodyTy) _) -> go v varTy bodyTy
    _ -> do
      let subjectTy' = normaliseTerm subjectTyRes
      subjectTyRes' <- case subjectTy' of
        Just t -> Just <$> resolveShallow t
        Nothing -> return Nothing
      case subjectTyRes' of
        Just (Term (PiT v varTy bodyTy) _) -> go v varTy bodyTy
        _ -> throwError $ NotAFunction subjectTy
checkTerm' t@(Term (Global g) _) typ = do
  decl <- inSignature (lookupItemOrCtor g)
  case decl of
    Nothing -> throwError $ ItemNotFound g
    Just (Left (Decl decl')) -> do
      typ' <- unifyTermsTo typ decl'.ty
      return (t, typ')
    Just (Left (Data dat)) -> do
      typ' <- unifyTermsTo typ dat.ty
      return (t, typ')
    Just (Left (Repr _)) -> do
      throwError $ CannotUseReprAsTerm g
    Just (Right ctor) -> do
      typ' <- unifyTermsTo typ ctor.ty
      return (t, typ')
checkTerm' (Term (Case s cs) _) typ = do
  (s', sTy) <- inferTerm s
  cs' <-
    mapM
      ( \(p, t) -> enterCtx $ do
          pt <- patToTerm p
          pt' <- enterPat $ do
            (pt', _) <- checkTerm pt sTy

            -- If the pattern is a variable,
            -- then we can unify with the subject for dependent
            -- pattern matching.
            case s' of
              Term (V _) _ -> unifyTerms pt' s'
              _ -> return ()

            return pt'
          (t', _) <- checkTerm t typ
          return (pt', t')
      )
      cs
  return (locatedAt s (Case s' cs'), typ)

-- Wild and hole are turned into metavars:
checkTerm' (Term Wild d1) typ = do
  m <- freshMetaAt d1
  registerWild (getLoc d1)
  return (m, typ)
checkTerm' (Term (Hole h) d1) typ = do
  m <- freshMetaAt d1
  registerHole (getLoc d1) h
  return (m, typ)
checkTerm' t@(Term (Meta _) _) typ = error $ "Found metavar during checking: " ++ show t ++ " : " ++ show typ

-- | Infer the type of a term.
inferTerm :: Term -> Tc (Term, Type)
inferTerm t = do
  ty <- freshMeta
  checkTerm t ty

-- | Reduce a term to normal form (one step).
-- If this is not possible, return Nothing.
normaliseTerm :: Term -> Maybe Term
normaliseTerm (Term (App (Term (Lam v t1) _) t2) _) =
  return $ subVar v t2 t1
normaliseTerm (Term (App t1 t2) d1) = do
  t1' <- normaliseTerm t1
  return (Term (App t1' t2) d1)
normaliseTerm _ = Nothing -- @@Todo: normalise declarations

-- | Reduce a term to normal form (fully).
normaliseTermFully :: Term -> Term
normaliseTermFully t = maybe t normaliseTermFully (normaliseTerm t)

-- \| Unify two terms.
-- This might produce a substitution.
-- Unification is symmetric.
unifyTerms :: Term -> Term -> Tc ()
unifyTerms a' b' = do
  a <- resolveShallow a'
  b <- resolveShallow b'
  case (classifyApp a, classifyApp b) of
    (Just (Flex v1 _), Just (Flex v2 _)) | v1 == v2 -> unifyTerms' a b
    (Just (Flex h1 ts1), _) -> solve h1 ts1 b
    (_, Just (Flex h2 ts2)) -> solve h2 ts2 a
    _ -> unifyTerms' a b
  where
    -- \| Unify a variable with a term. Returns True if successful.
    unifyVarWithTerm :: Term -> Var -> Term -> Tc ()
    unifyVarWithTerm vOrigin v t = do
      -- Check if the variable exists in a substitution in
      -- the context.
      subst <- inCtx (lookupSubst v)
      case subst of
        Just s -> unifyTerms s t
        Nothing -> do
          pt <- gets (\s -> s.inPat)
          if pt
            then modifyCtx (addSubst v t)
            else throwError $ Mismatch vOrigin t

    unifyTerms' :: Term -> Term -> Tc ()
    unifyTerms' (Term (PiT lv l1 l2) d1) (Term (PiT rv r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (SigmaT lv l1 l2) d1) (Term (SigmaT rv r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 (alphaRename rv (lv, d1) r2)
    unifyTerms' (Term (Lam lv l) d1) (Term (Lam rv r) _) = do
      unifyTerms l (alphaRename rv (lv, d1) r)
    unifyTerms' (Term (Pair l1 l2) _) (Term (Pair r1 r2) _) = do
      unifyTerms l1 r1
      unifyTerms l2 r2
    unifyTerms' (Term TyT _) (Term TyT _) = return ()
    unifyTerms' (Term (V l) _) (Term (V r) _) | l == r = return ()
    unifyTerms' a@(Term (V l) _) b = unifyVarWithTerm a l b
    unifyTerms' a b@(Term (V l) _) = unifyVarWithTerm b l a
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
    unifyTerms' a@(Term (App l1 l2) _) b@(Term (App r1 r2) _) =
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

-- | Convert a pattern to a term, converting wildcards to fresh variables.
patToTerm :: Pat -> Tc Term
patToTerm =
  mapTermM
    ( \t -> case t.value of
        Wild -> do
          v <- freshVar
          return . Replace $ Term (V v) t.dat
        _ -> return Continue
    )

-- | Validate a pattern unification problem, returning the spine variables.
validateProb :: Var -> [Term] -> Term -> Tc [Var]
validateProb _ [] _ = return []
validateProb hole (x : xs) rhs = do
  x' <- resolveShallow x
  case x'.value of
    V v -> do
      xs' <- validateProb hole xs rhs
      return $ v : xs'
    _ -> throwError $ Mismatch (listToApp (genTerm (Meta hole), x : xs)) rhs -- @@Todo : better error message

-- | Solve a pattern unification problem.
solve :: Var -> [Term] -> Term -> Tc ()
solve hole spine rhs = do
  vars <- validateProb hole spine rhs
  let solution = normaliseTermFully (lams vars rhs)
  solveMeta hole solution
