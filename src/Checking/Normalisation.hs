module Checking.Normalisation
  ( normaliseTermFully,
    fillAllMetasAndNormalise,
    fillAllMetas,
    resolveDeep,
    resolveShallow,
    normaliseProgram,
    normaliseTerm,
  )
where

import Checking.Context
  ( FlexApp (..),
    Tc,
    TcState (..),
    classifyApp,
    freshVar,
  )
import Checking.Vars (Sub (..), Subst (..), noSub, subVar)
import Control.Monad.State (gets)
import Data.Map (lookup, (!?))
import Lang
  ( HasLoc (..),
    MapResult (..),
    Pat,
    PiMode (..),
    Program (..),
    Term (..),
    TermMappable (..),
    TermValue (..),
    listToApp,
    locatedAt,
    mapTermM,
  )
import Language.Haskell.TH (noSig)
import Control.Monad (foldM)
import Control.Applicative ((<|>))

-- | Normalise a program fully.
normaliseProgram :: Program -> Program
normaliseProgram (Program decls) = mapTermMappable (ReplaceAndContinue . normaliseTermFully) (Program decls)

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
caseMatch _ _ = Nothing

-- | Reduce a term to normal form (one step).
-- If this is not possible, return Nothing.
normaliseTerm :: Term -> Maybe Term
normaliseTerm (Term (App m (Term (Lam m' v t1) _) t2) _)
  | m == m' =
      return $ subVar v t2 t1
normaliseTerm (Term (App m t1 t2) d1) = do
  t1' <- normaliseTerm t1
  return (Term (App m t1' t2) d1)
normaliseTerm (Term (Case s cs) d1) = do
  let s' = normaliseTerm s
  let s'f = normaliseTermFully s
  let res =
        foldr
          ( \(p, c) acc -> acc <|> do
                  sb <- caseMatch s'f p
                  return (sub sb c))
          Nothing
          cs
  case res of
    Just t -> return t
    Nothing -> case s' of
      Just s'' -> return $ Term (Case s'' cs) d1
      Nothing -> Nothing
normaliseTerm _ = Nothing -- @@Todo: normalise declarations

-- | Reduce a term to normal form (fully).
normaliseTermFully :: Term -> Term
normaliseTermFully t = maybe t normaliseTermFully (normaliseTerm t)

-- | Fill all the metavariables in a term.
fillAllMetas :: Term -> Tc (MapResult Term)
fillAllMetas t = ReplaceAndContinue <$> resolveFinal t

fillAllMetasAndNormalise :: (TermMappable t) => t -> Tc t
fillAllMetasAndNormalise t = do
  t' <- mapTermMappableM fillAllMetas t
  return $ mapTermMappable (ReplaceAndContinue . normaliseTermFully) t'

-- | Resolve a term by filling in metas if present, or turning them back into holes.
resolveFinal :: Term -> Tc Term
resolveFinal t = do
  case classifyApp t of
    Just (Flex h ts) -> do
      metas <- gets (\s -> s.metaValues)
      case metas !? h of
        Just t' -> do
          -- If the meta is already solved, then we can resolve the term.
          r <- resolveShallow (listToApp (t', map (Explicit,) ts))
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
resolveShallow (Term (App m t1 t2) d) = do
  t1' <- resolveShallow t1
  return $ normaliseTermFully (Term (App m t1' t2) d)
resolveShallow t = return t

resolveDeep :: Term -> Tc Term
resolveDeep = mapTermM (fmap ReplaceAndContinue . resolveShallow)
