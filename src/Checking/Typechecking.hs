module Checking.Typechecking
  ( checkTerm,
    inferTerm,
    checkProgram,
  )
where

import Checking.Context
  ( Tc,
    TcState (..),
    addCaseItemToDataRepr,
    addCtorItemToDataRepr,
    addEmptyDataItem,
    addItem,
    addTyping,
    addTypings,
    enterCtx,
    enterCtxEffect,
    enterCtxMod,
    enterPat,
    enterSignatureMod,
    findReprForGlobal,
    freshMeta,
    freshMetaAt,
    freshVar,
    globalAppSubjectName,
    globalAppSubjectNameM,
    inCtx,
    inSignature,
    lookupItemOrCtor,
    lookupType,
    modifyCtx,
    modifyItem,
    modifySignature,
    setType,
  )
import Checking.Errors (TcError (..))
import Checking.Normalisation (fillAllMetas, normaliseTerm, normaliseTermFully, resolveShallow, resolveDeep)
import Checking.Unification (introSubst, unifyAllTerms, unifyTerms)
import Checking.Utils (showHole, showSolvedMetas, showContext)
import Checking.Vars (Sub (..), Subst (..), alphaRename, subVar)
import Control.Monad (mapAndUnzipM, when)
import Control.Monad.Except (throwError, tryError)
import Control.Monad.State (get, gets, modify, put)
import Data.Foldable (find)
import Data.List (sort)
import Data.Map (insert)
import Data.Maybe (fromJust)
import Interface.Pretty (printVal)
import Lang
  ( CtorItem (..),
    DataItem (..),
    DeclItem (..),
    HasLoc (..),
    Item (..),
    Lit (..),
    Loc,
    Pat,
    PiMode (..),
    PrimItem (..),
    Program (..),
    ReprDataCaseItem (..),
    ReprDataCtorItem (..),
    ReprDataItem (..),
    ReprDeclItem (ReprDeclItem),
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
    piTypeToList,
    termDataAt,
  )
import Lang as DI (DeclItem (..), ItemId (ReprDataId))
import Debug.Trace (traceM)

-- | Check the program
checkProgram :: Program -> Tc Program
checkProgram (Program decls) = do
  p <- Program <$> mapM checkItem decls
  mapTermMappableM fillAllMetas p

-- | Check some item in the program.
checkItem :: Item -> Tc Item
checkItem (Decl decl) = Decl <$> checkDeclItem decl
checkItem (Data dat) = Data <$> checkDataItem dat
checkItem (ReprData r) = ReprData <$> checkReprDataItem r
checkItem (ReprDecl r) = ReprDecl <$> checkReprDeclItem r
checkItem (Prim p) = Prim <$> checkPrimItem p

-- | Check a prim item.
checkPrimItem :: PrimItem -> Tc PrimItem
checkPrimItem (PrimItem name ty) = do
  (ty', _) <- checkTerm ty (locatedAt ty TyT)
  let result = PrimItem name ty'
  modifySignature (addItem (Prim result))
  return result

-- | Check that a term (t x1..xn) is a valid (full) application of a pi type.
--
-- Also takes a closure to run more stuff in the same context, given the goal.
checkBindAppMatchesPi :: Pat -> Type -> (Type -> Tc a) -> Tc (Pat, a)
checkBindAppMatchesPi src ty f = do
  let (params, ret) = piTypeToList ty

  enterCtx $ do
    (src', srcTy) <- enterPat $ inferAtomicTerm src

    holeSub <-
      Sub
        <$> mapM
          ( \(_, v, _) -> do
              m <- freshMeta
              return (v, m)
          )
          params
    let retApplied = sub holeSub ret
    unifyTerms srcTy retApplied
    let ret' = locatedAt retApplied (Rep retApplied)
    res <- f ret'
    return (src', res)

-- | Check a repr data item.
checkReprDataItem :: ReprDataItem -> Tc ReprDataItem
checkReprDataItem (ReprDataItem src target ctors cse) = do
  -- Ensure that the name exists
  name <- globalAppSubjectNameM src
  decl <- inSignature (lookupItemOrCtor name)
  case decl of
    Just (Left (Data d)) -> do
      -- Check the type:
      (src', target') <- checkBindAppMatchesPi src d.ty $ \ret -> do
        -- Check that the target is also of the same (represented!) type
        (target', _) <- checkTerm target ret
        return target'

      -- Add the data type to the context without constructors
      modifySignature $ addEmptyDataItem src' target'

      -- Check each constructor
      ctors' <- mapM (checkReprDataCtorItem d.name) ctors

      -- Check that all the constructors are present
      let given = map (\c -> globalAppSubjectName c.src) ctors
      let expected = map (\c -> c.name) d.ctors
      when (sort given /= sort expected) $ throwError $ WrongConstructors given expected

      -- Check the case expression
      cse' <- traverse (checkReprDataCaseItem d) cse

      -- Add the final data type to the context
      let result = ReprDataItem src' target' ctors' cse'
      modifySignature $ modifyItem (ReprDataId d.name) (const (ReprData result))

      return result
    _ -> throwError $ ItemNotFound name

-- | Check a repr data constructor item.
checkReprDataCtorItem :: String -> ReprDataCtorItem -> Tc ReprDataCtorItem
checkReprDataCtorItem dName (ReprDataCtorItem src target) = do
  -- Ensure that the name exists
  name <- globalAppSubjectNameM src
  decl <- inSignature (lookupItemOrCtor name)
  case decl of
    Just (Right (CtorItem _ ty _ _)) -> do
      -- Check the target against the represented constructor type
      (src', target') <- checkBindAppMatchesPi src ty $ \ret -> do
        -- Check that the target is also of the same type
        (target', _) <- checkTerm target ret
        return target'

      -- Add the constructor to the context
      let result = ReprDataCtorItem src' target'
      modifySignature $ addCtorItemToDataRepr dName result

      return result
    _ -> throwError $ ItemNotFound name

-- | Check a repr data case item.
checkReprDataCaseItem :: DataItem -> ReprDataCaseItem -> Tc ReprDataCaseItem
checkReprDataCaseItem dat (ReprDataCaseItem (subject, elimName, ctors) target) = do
  -- Ensure that all the constructors are present
  let given = map fst ctors
  let expected = map (\c -> c.name) dat.ctors
  when (sort given /= sort expected) $ throwError $ WrongConstructors given expected

  -- Type of the subject is the represented data type
  let (params, _) = piTypeToList dat.ty
  let subjectTy = listToApp (genTerm (Global dat.name), map (\(m, p, _) -> (m, genTerm (V p))) params)
  -- subjectReprIndices <- mapM (\(m, a, b) -> (m,a,) <$> representTerm b) params
  -- subjectReprTy <- representTerm subjectTy
  enterCtxMod id $ do
    (subjectAsTerm, _) <- enterPat $ checkTerm subject subjectTy
    enterCtxMod (addTypings (map (\(_, v, t) -> (v, t)) params)) $ do
      -- Form the elimination type family
      elimTySubjectVar <- freshVar
      let elimFam = listToPiType (params ++ [(Explicit, elimTySubjectVar, subjectTy)], genTerm TyT)
      -- elimReprFam <- representTerm elimFam

      enterCtxMod (addTypings [(elimName, elimFam)]) $ do
        -- Form the elimination type
        let elimTy = listToApp (genTerm (V elimName), map (\(m, v, _) -> (m, genTerm (V v))) params ++ [(Explicit, subjectAsTerm)])

        -- Gather all the eliminators
        ctors' <-
          mapM
            ( \(cName, cBind) -> do
                -- Represented constructor parameters
                let c = fromJust (find (\n -> n.name == cName) dat.ctors)
                let (ctorParams, ctorRet) = piTypeToList c.ty
                -- ctorReprParams <- mapM (\(m, a, b) -> (m,a,) <$> representTerm b) ctorParams

                -- Represented constructor return indices
                let (_, ctorRetIndices) = appToList ctorRet
                -- ctorReprRetIndices <- mapM (\(m, t) -> (m,) <$> representTerm t) ctorRetIndices

                -- Represented constructor return type
                let ctorParamVarTerms = map (\(m, t, _) -> (m, genTerm (V t))) ctorParams
                let ctorRetTy = listToApp (genTerm (Global c.name), ctorParamVarTerms)
                -- ctorReprRetTy <- representTerm ctorRetTy

                -- Form the eliminator type
                let elimCtorTy =
                      listToPiType
                        ( ctorParams,
                          listToApp
                            ( genTerm (V elimName),
                              ctorRetIndices
                                ++ [(Explicit, ctorRetTy)]
                            )
                        )

                -- The eliminator is bound to the given binding in the case
                -- representation.
                (cBindAsTerm, _) <- enterPat $ checkTerm cBind elimCtorTy
                return (cName, cBindAsTerm)
            )
            ctors

        -- Overall the RHS of a case representation should have in context:
        -- 1. The subject indices
        -- 2. The subject type
        -- 3. The subject itself
        -- 4. The elimination indices
        -- 5. The elimination type
        -- 6. For each constructor, the eliminator
        (target', _) <- checkTerm target elimTy

        -- @@TODO: hide eliminators from the context in the end!

        -- Add the case representation to the context
        let result = ReprDataCaseItem (subjectAsTerm, elimName, ctors') target'
        modifySignature $ addCaseItemToDataRepr dat.name result
        return result

-- | Check a repr decl item.
checkReprDeclItem :: ReprDeclItem -> Tc ReprDeclItem
checkReprDeclItem (ReprDeclItem name target) = do
  -- Ensure that the name exists
  decl <- inSignature (lookupItemOrCtor name)
  case decl of
    Just (Left (Decl d)) -> do
      -- rDeclTy <- representTerm d.ty
      -- Check the target against the represented declaration type
      (target', _) <- checkTerm target d.ty
      let result = ReprDeclItem name target'
      modifySignature $ addItem (ReprDecl result)
      return result
    _ -> throwError $ ItemNotFound name

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
  let dTyArgs = fst (piTypeToList dTy)

  -- Check the signature of the constructor.
  (ty', _) <- checkTerm ty (genTerm TyT)
  let (tys, ret) = piTypeToList ty'

  -- \| Add all the arguments to the context
  enterCtxMod (\c -> foldr (\(_, v, t) c' -> addTyping v t c') c tys) $ do
    -- \| Check that the return type is the data type.
    dummyArgs <- mapM (\(m, _, _) -> (m,) <$> freshMeta) dTyArgs
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
  let env = if decl.isRecursive then enterSignatureMod (addItem (Decl $ decl {DI.ty = ty'})) else id
  (tm', ty'') <- env $ do
    let tm = decl.value
    checkTerm tm ty'

  -- Add the final decl to the context
  let decl' = DeclItem decl.name ty'' tm' decl.loc decl.isRecursive decl.unfold
  modifySignature (addItem (Decl decl'))

  return decl'

-- | Insert an implicit application.
applyImplicitUnchecked :: Term -> Term
applyImplicitUnchecked t = genTerm (App Implicit t (genTerm Wild))

freshMetaOrPat :: Type -> Tc Term
freshMetaOrPat ty = do
  p <- gets (\s -> s.inPat)
  if p
    then do
      v <- freshVar
      modifyCtx (addTyping v ty)
      return . genTerm $ V v
    else freshMeta

-- | Apply implicits to an already checked term.
fullyApplyImplicits :: Term -> Type -> Tc (Term, Type)
fullyApplyImplicits t ty = do
  case ty of
    (Term (PiT Implicit v typ b) _) -> do
      m <- freshMetaOrPat typ
      fullyApplyImplicits (genTerm (App Implicit t m)) (subVar v m b)
    _ -> return (t, ty)

-- | Infer the type of a term and apply implicits.
inferAtomicTerm :: Term -> Tc (Term, Type)
inferAtomicTerm t = do
  (t', ty') <- inferTerm t
  fullyApplyImplicits t' ty'

inferTerm :: Term -> Tc (Term, Type)
inferTerm t = do
  (t', ty) <- inferTerm' t
  t'' <- setType t' ty
  return (t'', ty)

-- | Infer the type of a term.
inferTerm' :: Term -> Tc (Term, Type)
inferTerm' ((Term (Lam m v t1) d1)) = do
  varTy <- freshMeta
  (t1', bodyTy) <- enterCtxMod (addTyping v varTy) $ inferAtomicTerm t1
  return (locatedAt d1 (Lam m v t1'), locatedAt d1 (PiT m v varTy bodyTy))
inferTerm' (Term (Pair t1 t2) d1) = do
  (t1', ty1) <- inferAtomicTerm t1
  (t2', ty2) <- inferAtomicTerm t2
  v <- freshVar
  return (locatedAt d1 (Pair t1' t2'), locatedAt d1 (SigmaT v ty1 ty2))
inferTerm' (Term (PiT m v t1 t2) d1) = do
  (t1', _) <- checkTermExpected t1 TyT
  (t2', _) <- enterCtxMod (addTyping v t1) $ checkTermExpected t2 TyT
  return (locatedAt d1 (PiT m v t1' t2'), locatedAt d1 TyT)
inferTerm' (Term (SigmaT v t1 t2) d1) = do
  (t1', _) <- checkTermExpected t1 TyT
  (t2', _) <- enterCtxMod (addTyping v t1) $ checkTermExpected t2 TyT
  return (locatedAt d1 (SigmaT v t1' t2'), locatedAt d1 TyT)
inferTerm' (Term TyT d1) = do
  return (Term TyT d1, locatedAt d1 TyT)
inferTerm' (Term (App m t1 t2) d1) = do
  (t1', subjectTy) <- inferTerm t1
  subjectTyRes <- resolveShallow subjectTy

  let go v varTy bodyTy = do
        (t2', _) <- checkTerm t2 varTy
        return (locatedAt t1 (App m t1' t2'), subVar v t2' bodyTy)

  let goImplicit = do
        let t1Ins = applyImplicitUnchecked t1
        inferTerm (Term (App m t1Ins t2) d1)

  -- Try to normalise to a pi type.
  case subjectTyRes of
    (Term (PiT m' v varTy bodyTy) _) | m == m' -> go v varTy bodyTy
    (Term (PiT Implicit _ _ _) _) -> goImplicit
    _ -> do
      sig <- gets (\s -> s.signature)
      c <- gets (\s -> s.ctx)
      let subjectTy' = normaliseTerm c sig subjectTyRes
      subjectTyRes' <- case subjectTy' of
        Just t -> Just <$> resolveShallow t
        Nothing -> return Nothing
      case subjectTyRes' of
        Just (Term (PiT m' v varTy bodyTy) _) | m == m' -> go v varTy bodyTy
        Just (Term (PiT Implicit _ _ _) _) -> goImplicit
        _ -> throwError $ NotAFunction subjectTy
inferTerm' t@(Term (Global g) _) = do
  decl <- inSignature (lookupItemOrCtor g)
  expectedTyp <- case decl of
    Nothing -> throwError $ ItemNotFound g
    Just (Left (Decl decl')) -> return decl'.ty
    Just (Left (Data dat)) -> return dat.ty
    Just (Left (ReprData _)) -> throwError $ CannotUseReprAsTerm g
    Just (Left (ReprDecl _)) -> throwError $ CannotUseReprAsTerm g
    Just (Left (Prim p)) -> return p.ty
    Just (Right ctor) -> return ctor.ty
  return (t, expectedTyp)
inferTerm' t@(Term (V v) _) = do
  vTyp <- inCtx (lookupType v)
  case vTyp of
    Nothing -> throwError $ VariableNotFound v
    Just vTyp' -> return (t, vTyp')
inferTerm' (Term (Let var ty tm ret) d1) = do
  ((ty'', tm', ret'), typ') <- inferOrCheckLet inferTerm var ty tm ret
  return (locatedAt d1 (Let var ty'' tm' ret'), typ')
inferTerm' (Term (Case e s cs) _) = do
  ((s', cs'), tys) <- inferOrCheckCase inferTerm s cs
  ret <- unifyAllTerms tys
  sTy <- makeCaseElimTy s' ret
  e' <- unifyMaybes e (Just sTy)
  return (locatedAt s (Case e' s' cs'), ret)
inferTerm' (Term Wild d1) = do
  typ <- freshMetaAt d1
  m <- registerWild (getLoc d1) typ
  return (m, typ)
inferTerm' hole@(Term (Hole h) d1) = do
  typ <- freshMetaAt d1
  m <- registerHole (getLoc d1) h
  showHole hole Nothing
  return (m, typ)
inferTerm' t@(Term (Meta _) _) = error $ "Found metavar during inference: " ++ show t
inferTerm' (Term (Rep r) d1) = do
  (r', ty) <- inferTerm r
  return (locatedAt d1 (Rep r'), locatedAt d1 (Rep ty))
inferTerm' (Term (Unrep n r) d1) = do
  (r', ty) <- inferTerm r
  rep <- findReprForGlobal n
  case rep of
    Nothing -> throwError $ ItemNotFound n
    Just (params, term) -> do
      paramMetas <- mapM (\(m, _) -> (m,) <$> freshMeta) params
      -- Ensure that the term to be unrepresented has the correct represented type
      unifyTerms (listToApp (term, paramMetas)) ty
      return (locatedAt d1 (Unrep n r'), listToApp (locatedAt d1 (Global n), paramMetas))
inferTerm' (Term (Lit (StringLit l)) d1) = do
  return (locatedAt d1 (Lit (StringLit l)), locatedAt d1 (Global "String"))
inferTerm' (Term (Lit (CharLit l)) d1) = do
  return (locatedAt d1 (Lit (CharLit l)), locatedAt d1 (Global "Char"))
inferTerm' (Term (Lit (NatLit l)) d1) = do
  return (locatedAt d1 (Lit (NatLit l)), locatedAt d1 (Global "Nat"))
inferTerm' (Term (Lit (FinLit i n)) d1) = do
  (n', _) <- checkTerm n (locatedAt n (Global "Nat"))
  m <- freshMeta
  -- Shortcut if both are literals
  case n'.value of
    Lit (NatLit l)
      | i < l + 1 ->
          return
            ( locatedAt d1 (Lit (FinLit i n')),
              listToApp (locatedAt d1 (Global "Fin"), [(Explicit, genTerm (Lit (NatLit (l + 1))))])
            )
    _ -> do
      let minIndex = listToApp (genTerm (Global "add"), [(Explicit, genTerm (Lit (NatLit i))), (Explicit, m)])
      unifyTerms minIndex n'
      return
        ( locatedAt d1 (Lit (FinLit i n')),
          listToApp (locatedAt d1 (Global "Fin"), [(Explicit, listToApp (genTerm (Global "s"), [(Explicit, n')]))])
        )

inferOrCheckLet :: (Term -> Tc (Term, Type)) -> Var -> Type -> Term -> Term -> Tc ((Type, Term, Term), Type)
inferOrCheckLet f var ty tm ret = do
  (ty', _) <- checkTermExpected ty TyT
  (tm', ty'') <- checkTerm tm ty'
  (ret', typ') <- enterCtxMod (addTyping var ty') . enterCtxEffect (introSubst var tm') $ f ret
  return ((ty'', tm', ret'), subVar var tm' typ')

inferOrCheckCase :: (Term -> Tc (Term, Type)) -> Term -> [(Pat, Maybe Term)] -> Tc ((Term, [(Pat, Maybe Term)]), [Type])
inferOrCheckCase f s cs = do
  (s', sTy) <- inferAtomicTerm s
  (cs', tys) <-
    mapAndUnzipM
      ( \(p, t) -> enterCtx $ do
          case t of
            Nothing -> do
              -- Ensure that checking the pattern is impossible
              pt' <- tryError . enterPat $ do
                (pt', _) <- checkTerm p sTy
                -- If the subject is a variable,
                -- then we can unify with the pattern for dependent
                -- pattern matching.
                case s' of
                  Term (V _) _ -> unifyTerms pt' s'
                  _ -> return ()
              case pt' of
                Left _ -> do
                  m <- freshMeta
                  return ((p, Nothing), m)
                Right _ -> throwError $ PatternNotImpossible p
            Just t' -> do
              pt' <- enterPat $ do
                (pt', _) <- checkTerm p sTy

                -- If the subject is a variable,
                -- then we can unify with the pattern for dependent
                -- pattern matching.
                case s' of
                  Term (V _) _ -> unifyTerms pt' s'
                  _ -> return ()

                return pt'
              (t'', ty) <- f t'
              return ((pt', Just t''), ty)
      )
      cs

  return ((s', cs'), tys)

unifyMaybes :: Maybe Term -> Maybe Term -> Tc (Maybe Term)
unifyMaybes (Just t1) (Just t2) = unifyTerms t1 t2 >> return (Just t1)
unifyMaybes Nothing Nothing = return Nothing
unifyMaybes (Just t1) Nothing = return $ Just t1
unifyMaybes Nothing (Just t2) = return $ Just t2

makeCaseElimTy :: Term -> Type -> Tc Term
makeCaseElimTy s ty = do
  case s of
    Term (V v) _ -> do
      let elimTy = lams [(Explicit, v)] ty
      return elimTy
    _ -> do
      v <- freshVar
      let elimTy = lams [(Explicit, v)] ty
      return elimTy

-- | Register a hole.
registerHole :: Loc -> Var -> Tc Term
registerHole l v = do
  m <- freshMetaAt l
  s <- get
  put $ s {holeLocs = insert l (Just v) s.holeLocs}
  return m

-- | Register an underscore/wild.
registerWild :: Loc -> Type -> Tc Term
registerWild l typ = do
  p <- gets (\s -> s.inPat)
  if p
    then do
      v <- freshVar
      modifyCtx (addTyping v typ)
      return $ Term (V v) (termDataAt l)
    else do
      m <- freshMetaAt l
      modify $ \s -> s {holeLocs = insert l Nothing s.holeLocs}
      return m

-- | Check the type of a term, and set the type in the context.
checkTerm :: Term -> Type -> Tc (Term, Type)
checkTerm v t = do
  tResolved <- resolveShallow t
  (v', t') <- checkTerm' v tResolved
  c <- gets (\s -> s.ctx)
  let t'' = normaliseTermFully c mempty t'
  v'' <- setType v' t''
  return (v'', t'')

-- | Check the type of a term.
-- mempty
-- The location of the type is inherited from the term.
checkTermExpected :: Term -> TypeValue -> Tc (Term, Type)
checkTermExpected v t = checkTerm v (locatedAt v t)

-- | Check the type of a term. (The type itself should already be checked.)
--
-- This also performs elaboration by filling named holes and wildcards with metavariables.
checkTerm' :: Term -> Type -> Tc (Term, Type)
checkTerm' ((Term (Lam m1 v t) d1)) ((Term (PiT m2 var' ty1 ty2) d2))
  | m1 == m2 = do
      (t', ty2') <- enterCtxMod (addTyping v ty1) $ checkTerm t (alphaRename var' (v, d2) ty2)
      return (locatedAt d1 (Lam m1 v t'), locatedAt d2 (PiT m2 var' ty1 (alphaRename v (var', d2) ty2')))
checkTerm' t ty@((Term (PiT Implicit _ _ _) _)) = do
  p <- gets (\s -> s.inPat)
  if p
    then checkTerm'' t ty
    else do
      v <- freshVar
      checkTerm (genTerm (Lam Implicit v t)) ty
checkTerm' t ty = checkTerm'' t ty

checkTerm'' :: Term -> Term -> Tc (Term, Type)
checkTerm'' (Term (Pair t1 t2) d1) (Term (SigmaT v ty1 ty2) d2) = do
  (t1', ty1') <- checkTerm t1 ty1
  (t2', ty2') <- checkTerm t2 (subVar v t1' ty2)
  return (locatedAt d1 (Pair t1' t2'), locatedAt d2 (SigmaT v ty1' ty2'))
checkTerm'' t@(Term (V v) _) typ = do
  p <- gets (\s -> s.inPat)
  if p
    then do
      modifyCtx (addTyping v typ)
      return (t, typ)
    else checkByInfer t typ
checkTerm'' (Term (Let var ty tm ret) d1) typ = do
  ((ty'', tm', ret'), typ') <- inferOrCheckLet (`checkTerm` typ) var ty tm ret
  return (locatedAt d1 (Let var ty'' tm' ret'), typ')
checkTerm'' (Term (Case e s cs) _) typ = do
  ((s', cs'), _) <- inferOrCheckCase (`checkTerm` typ) s cs
  sTy <- makeCaseElimTy s' typ
  e' <- unifyMaybes e (Just sTy)
  return (locatedAt s (Case e' s' cs'), typ)
checkTerm'' (Term Wild d1) typ = do
  m <- registerWild (getLoc d1) typ
  return (m, typ)
checkTerm'' hole@(Term (Hole h) d1) typ = do
  m <- registerHole (getLoc d1) h
  showHole hole (Just typ)
  return (m, typ)
checkTerm'' t@(Term (Meta _) _) typ = error $ "Found metavar during checking: " ++ show t ++ " : " ++ show typ
checkTerm'' t typ = do
  -- Try to normalise the type and try again
  c <- gets (\s -> s.ctx)
  sig <- gets (\s -> s.signature)
  let typ' = normaliseTerm c sig typ
  case typ' of
    Nothing -> checkByInfer t typ
    Just typ'' -> checkTerm t typ''

checkByInfer :: Term -> Type -> Tc (Term, Type)
checkByInfer t typ = do
  (t', typ') <- inferAtomicTerm t
  unifyTerms typ typ'
  return (t', typ')
