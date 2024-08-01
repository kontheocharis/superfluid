module Checking.Errors (TcError (..)) where

import Data.List (intercalate)
import Interface.Pretty (Print (..))
import Lang (HasLoc (getLoc), Pat, Term, TermMappable (..), Var, mapTermM)

data TcError
  = VariableNotFound Var
  | Mismatch Term Term
  | PotentialMismatch Term Term
  | ItemNotFound String
  | NotAFunction Term
  | CannotSolveProblem Var [Term] Term
  | VariableEscapesMeta Var [Term] Term Var
  | PatternNotSupported Pat
  | PatternNotImpossible Pat
  | WrongConstructors [String] [String]
  | CannotUseReprAsTerm String
  | Many [TcError]

instance Semigroup TcError where
  (Many es1) <> (Many es2) = Many (es1 <> es2)
  (Many es) <> e = Many (es <> [e])
  e <> (Many es) = Many (e : es)
  e1 <> e2 = Many [e1, e2]

instance Monoid TcError where
  mempty = Many []
  mappend = (<>)

instance TermMappable TcError where
  mapTermMappableM f (NotAFunction t) = NotAFunction <$> mapTermM f t
  mapTermMappableM f (PatternNotSupported p) = PatternNotSupported <$> mapTermM f p
  mapTermMappableM f (Mismatch t1 t2) = Mismatch <$> mapTermM f t1 <*> mapTermM f t2
  mapTermMappableM f (CannotSolveProblem m spine rhs) = CannotSolveProblem m <$> mapM (mapTermM f) spine <*> mapTermM f rhs
  mapTermMappableM f (VariableEscapesMeta m spine rhs rhsVar) = VariableEscapesMeta m <$> mapM (mapTermM f) spine <*> mapTermM f rhs <*> pure rhsVar
  mapTermMappableM f (PatternNotImpossible p) = PatternNotImpossible <$> mapTermM f p
  mapTermMappableM f (Many es) = Many <$> mapM (mapTermMappableM f) es
  mapTermMappableM _ e = return e

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ printVal v
  show (Mismatch t1 t2) =
    "Term mismatch: " ++ printSingleVal t1 ++ " vs " ++ printSingleVal t2 ++ " (at " ++ printVal (getLoc t1) ++ " and " ++ printVal (getLoc t2) ++ ")"
  show (PotentialMismatch t1 t2) = "Potential term mismatch: " ++ printSingleVal t1 ++ " vs " ++ printSingleVal t2
  show (ItemNotFound s) = "Item not found: " ++ s
  show (NotAFunction t) = "Not a function: " ++ printSingleVal t
  show (CannotSolveProblem m spine rhs) = "Cannot solve problem: " ++ printVal m ++ " " ++ intercalate " " (map printSingleVal spine) ++ " ?= " ++ printVal rhs
  show (VariableEscapesMeta m spine rhs rhsVar) = "Variable " ++ printVal rhsVar ++ " in " ++ printVal rhs ++ " escapes meta " ++ printVal m ++ " " ++ intercalate " " (map printSingleVal spine)
  show (PatternNotSupported p) = "Pattern is not supported yet: " ++ printVal p
  show (WrongConstructors cs1 cs2) = "Wrong constructors: got " ++ intercalate ", " cs1 ++ " but expected " ++ intercalate ", " cs2
  show (CannotUseReprAsTerm r) = "Cannot use representation " ++ r ++ " as a term yet!"
  show (PatternNotImpossible p) = "Pattern is not impossible: " ++ printVal p
  show (Many es) = intercalate "\n" $ map show es
