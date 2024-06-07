module Checking.Representation (representProgram, representCtx, representTerm) where

import Checking.Context
  ( Tc,
    addItems,
    findReprForCase,
    findReprForGlobal,
    getDataItem,
    getType,
    inSignature,
    modifyCtxM,
    modifySignature,
  )
import Checking.Errors (TcError (..))
import Checking.Normalisation (normaliseTermFully, resolveDeep, resolveShallow)
import Control.Monad.Except (throwError)
import Data.Foldable (find)
import Data.List (sortBy)
import Data.Maybe (fromJust)
import Debug.Trace (trace)
import Interface.Pretty (Print (..))
import Lang
  ( CtorItem (..),
    DataItem (..),
    Item (..),
    MapResult (..),
    Pat,
    PiMode (..),
    Program (..),
    Term (..),
    TermMappable (mapTermMappableM),
    TermValue (..),
    appToList,
    lams,
    listToApp,
    mapTermM,
  )
import Lang as DI (TermMappable (mapTermMappable))

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

-- | Represent the current context.
representCtx :: Tc ()
representCtx = modifyCtxM $ mapTermMappableM representTermRec

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
                ( \(m, t') -> case t' of
                    Term (V v) _ -> return (m, v)
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
      Just (_, term) -> do
        term' <- resolveDeep term
        return $ ReplaceAndContinue term'
  Term (Case s cs) _ -> do
    sTy <- getType s
    case sTy of
      Just t -> do
        t' <- resolveShallow t
        case appToList t' of
          (Term (Global g) _, _) -> do
            r <- findReprForCase g
            case r of
              Nothing -> return Continue
              Just (_, term) -> do
                term' <- resolveDeep term
                xs <- caseElimsToAppArgs g cs
                s' <- resolveDeep s
                xs' <- mapM resolveDeep xs
                return $ ReplaceAndContinue (listToApp (term', map (Explicit,) (s' : xs')))
          _ -> error $ "Case subject is not a global type: " ++ printVal t'
      _ -> trace ("No type found for subject " ++ printVal s) $ return Continue
  _ -> return Continue

-- | Represent a checked term through defined representations.
representTerm :: Term -> Tc Term
representTerm = mapTermM representTermRec
