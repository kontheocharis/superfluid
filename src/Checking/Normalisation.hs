module Checking.Normalisation
  ( normaliseTermFully,
    fillAllMetasAndNormalise,
    fillAllMetas,
    resolveDeep,
    resolveShallow,
    normaliseProgram,
    normaliseTerm,
    expandLit,
  )
where

import Checking.Context
  ( Ctx,
    FlexApp (..),
    Signature (Signature),
    Tc,
    TcState (..),
    classifyApp,
    findReprForGlobal',
    lookupItemOrCtor,
    lookupSubst,
  )
import Checking.Vars (Sub (..), Subst (..), noSub, subVar)
import Control.Applicative ((<|>))
import Control.Monad.State (gets)
import Data.Map (lookup, (!?))
import Debug.Trace (traceM, trace)
import GHC.Natural (Natural)
import Interface.Pretty (printVal)
import Lang
  ( HasLoc (..),
    Item (..),
    Lit (..),
    MapResult (..),
    Pat,
    PiMode (..),
    Program (..),
    Term (..),
    TermMappable (..),
    TermValue (..),
    genTerm,
    isRecursive,
    listToApp,
    locatedAt,
    mapTermM,
  )
import Lang as DI (DeclItem (..), appToList)

-- | Normalise a program fully.
normaliseProgram :: Program -> Program
normaliseProgram (Program decls) = do
  let decls' =
        filter
          ( \case
              Decl d -> d.unfold
              _ -> False
          )
          decls
  mapTermMappable (ReplaceAndContinue . normaliseTermFully mempty (Signature decls')) (Program decls)

-- | Match a term against a pattern.
--
-- This does not expect wildcards in the pattern.
caseMatch :: Term -> Pat -> Maybe Sub
caseMatch (Term (Pair t1 t2) _) (Term (Pair p1 p2) _) = do
  s1 <- caseMatch t1 p1
  s2 <- caseMatch t2 p2
  return $ s1 <> s2
caseMatch (Term (Global l) _) (Term (Global r) _) | l == r = return noSub
caseMatch (Term (App m t1 t2) _) (Term (App m' t1' t2') _) | m == m' = do
  s1 <- caseMatch t1 t1'
  s2 <- caseMatch t2 t2'
  return $ s1 <> s2
caseMatch a (Term (V v) _) = return $ Sub [(v, a)]
caseMatch (Term (Lit l) _) b = caseMatch (expandLit l) b
caseMatch _ _ = Nothing

tryCaseMatch :: Ctx -> Signature -> Term -> Pat -> Maybe Sub
tryCaseMatch c sig t p = case caseMatch t p of
  Just s -> Just s
  Nothing -> case normaliseTerm c sig t of
    Just t' -> tryCaseMatch c sig t' p
    Nothing -> Nothing

expandRep :: Signature -> Term -> Maybe Term
expandRep _ t@(Term TyT _) = Just t
expandRep sig t = do
  let t' = appToList t
  case t' of
    (Term (Global g) _, xs) -> do
      case findReprForGlobal' sig g of
        Just (_, x') -> Just $ listToApp (x', xs)
        _ -> Nothing
    _ -> Nothing

tryExpandRep :: Ctx -> Signature -> Term -> Maybe Term
tryExpandRep c sig t = case expandRep sig t of
  Just t' -> Just t'
  Nothing -> case normaliseTerm c sig t of
    Just t' -> tryExpandRep c sig t'
    Nothing -> Nothing

-- | Reduce a term to normal form (one step).
-- If this is not possible, return Nothing.
normaliseTerm :: Ctx -> Signature -> Term -> Maybe Term
normaliseTerm c s t = normaliseTerm' c s t
  where
    normaliseTerm' :: Ctx -> Signature -> Term -> Maybe Term
    normaliseTerm' _ _ (Term (App m (Term (Lam m' v t1) _) t2) _)
      | m == m' =
          return $ subVar v t2 t1
    normaliseTerm' c sig (Term (App m t1 t2) d1) = do
      t1' <- normaliseTerm' c sig t1
      return (Term (App m t1' t2) d1)
    normaliseTerm' c sig (Term (Case e s cs) d1) =
      foldr
        ( \(p, t) acc ->
            case t of
              Just c' ->
                acc <|> do
                  sb <- tryCaseMatch c sig s p
                  return (sub sb c')
              Nothing -> acc
        )
        Nothing
        cs
        <|> ( case normaliseTerm' c sig s of
                Just s' -> Just (Term (Case e s' cs) d1)
                Nothing -> Nothing
            )
    normaliseTerm' c _ (Term (V v) _) | Just t <- lookupSubst v c = Just t
    normaliseTerm' _ sig (Term (Global g) _) = maybeExpand sig g
    normaliseTerm' c sig (Term (Rep r) _) = tryExpandRep c sig r
    normaliseTerm' _ _ _ = Nothing -- @@Todo: normalise declarations

expandLit :: Lit -> Term
expandLit (StringLit s) = expandStringToTermOnce s
expandLit (CharLit c) = expandCharToTermOnce c
expandLit (NatLit n) = expandNatToTermOnce n
expandLit (FinLit i n) = expandFinToTermOnce n i

expandNatToTermOnce :: Natural -> Term
expandNatToTermOnce 0 = genTerm (Global "z")
expandNatToTermOnce n = listToApp (genTerm (Global "s"), [(Explicit, genTerm (Lit (NatLit (n - 1))))])

expandFinToTermOnce :: Term -> Natural -> Term
expandFinToTermOnce n 0 = listToApp (genTerm (Global "fz"), [(Implicit, n)])
expandFinToTermOnce n i =
  listToApp
    ( genTerm (Global "fs"),
      [ (Implicit, n),
        ( Explicit,
          genTerm
            ( Lit
                ( FinLit
                    (i - 1)
                    ( listToApp
                        ( genTerm (Global "s"),
                          [(Explicit, n)]
                        )
                    )
                )
            )
        )
      ]
    )

expandCharToTermOnce :: Char -> Term
expandCharToTermOnce c =
  listToApp
    ( genTerm (Global "char-from-num"),
      [ (Explicit, genTerm (Lit (FinLit (fromIntegral (fromEnum c)) (genTerm (Lit (NatLit (2 ^ (32 :: Natural))))))))
      ]
    )

expandStringToTermOnce :: String -> Term
expandStringToTermOnce [] = genTerm (Global "snil")
expandStringToTermOnce (s : ss) =
  listToApp
    ( genTerm (Global "scons"),
      [(Explicit, genTerm (Lit (CharLit s))), (Explicit, genTerm (Lit (StringLit ss)))]
    )

-- | Try to expand the given definition to the given term.
maybeExpand :: Signature -> String -> Maybe Term
maybeExpand sig n = do
  i <- lookupItemOrCtor n sig
  case i of
    Left (Decl d) -> Just d.value
    _ -> Nothing

-- | Reduce a term to normal form (fully).
normaliseTermFully :: Ctx -> Signature -> Term -> Term
normaliseTermFully c sig =
  mapTermMappable
    ( \t -> case normaliseTerm c sig t of
        Just t' -> ReplaceAndContinue (normaliseTermFully c sig t')
        Nothing -> Continue
    )

-- | Fill all the metavariables in a term.
fillAllMetas :: Term -> Tc (MapResult Term)
fillAllMetas t = ReplaceAndContinue <$> resolveFinal t

fillAllMetasAndNormalise :: (TermMappable t) => t -> Tc t
fillAllMetasAndNormalise t = do
  t' <- mapTermMappableM fillAllMetas t
  return $ mapTermMappable (Replace . normaliseTermFully mempty mempty) t'

-- | Resolve a term by filling in metas if present, or turning them back into holes.
resolveFinal :: Term -> Tc Term
resolveFinal t = do
  case classifyApp t of
    Just (Flex h ts) -> do
      metas <- gets (\s -> s.metaValues)
      case metas !? h of
        Just t' -> do
          -- If the meta is already solved, then we can resolve the term.
          resolveFinal (listToApp (t', map (Explicit,) ts))
        Nothing -> do
          -- If the meta is not resolved, then substitute the original hole
          let tLoc = getLoc t
          hole <- gets (\s -> Data.Map.lookup tLoc s.holeLocs)
          case hole of
            Just (Just v) -> return $ locatedAt tLoc (Hole v)
            Just Nothing -> return $ locatedAt tLoc Wild
            Nothing -> do
              -- If the hole is not registered, then it is still a meta
              return t
    _ -> return t

-- | Resolve a term by filling in metas if present.
resolveShallow :: Term -> Tc Term
resolveShallow (Term (Meta h) d) = do
  metas <- gets (\s -> s.metaValues)
  case metas !? h of
    Just t -> resolveShallow t
    Nothing -> return $ Term (Meta h) d
resolveShallow (Term (App m t1 t2) d) = do
  t1' <- resolveShallow t1
  return $ normaliseTermFully mempty mempty (Term (App m t1' t2) d)
resolveShallow (Term (Case e s cs) d) = do
  s' <- resolveShallow s
  return $ Term (Case e s' cs) d
resolveShallow t = return t

resolveDeep :: Term -> Tc Term
resolveDeep = mapTermM (fmap ReplaceAndContinue . resolveShallow)
