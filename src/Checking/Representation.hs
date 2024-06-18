module Checking.Representation (representProgram, representCtx, representTerm) where

import Checking.Context
  ( Signature (Signature),
    Tc,
    addItems,
    enterSignatureMod,
    findReprForCase,
    findReprForGlobal,
    getDataItem,
    inSignature,
    modifyCtxM,
    modifySignature, freshMeta,
  )
import Checking.Errors (TcError (..))
import Checking.Normalisation (resolveDeep, resolveShallow)
import Control.Monad.Except (throwError)
import Data.Foldable (find, foldrM)
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
    itemName,
    lams,
    listToApp,
    mapTermM, annotTy,
  )

-- | Represent a checked program
representProgram :: Program -> Tc Program
representProgram (Program decls) = do
  -- Filter out all the (checked) repr items from the program
  (reprs, rest) <-
    foldrM
      ( \x (reprs', rest') -> case x of
          Repr r -> return (Repr r : reprs', rest')
          it -> do
            itRepr <- enterSignatureMod (const (Signature decls)) $ findReprForGlobal (itemName it)
            case itRepr of
              Nothing -> return (reprs', x : rest') -- Not a repr item, so retain
              Just _ -> return (reprs', rest') -- Already represented, so discard
      )
      ([], [])
      decls

  -- Add them to the signature
  modifySignature $ addItems reprs

  -- Then, represent all the items in the program
  Program rest' <- mapTermMappableM representTermRec (Program rest)

  -- Finally, return the program
  return (Program rest')

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
    case s.dat.annotTy of
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
                elimTy <- freshMeta
                -- @@FIXME: This is not the right elimination type!
                return $ ReplaceAndContinue (listToApp (term', map (Explicit,) (elimTy : s' : xs')))
          _ -> error $ "Case subject is not a global type: " ++ printVal t'
      _ -> trace ("No type found for subject " ++ printVal s) $ return Continue
  _ -> return Continue

-- | Represent a checked term through defined representations.
representTerm :: Term -> Tc Term
representTerm = mapTermM representTermRec
