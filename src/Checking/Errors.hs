module Checking.Errors (TcError (..)) where

import Data.List (intercalate)
import Interface.Pretty (Print (..))
import Lang (HasLoc (getLoc), Pat, Term, TermMappable (..), Var, mapTermM)

data TcError
  = VariableNotFound Var
  | Mismatch Term Term
  | ItemNotFound String
  | CannotUnifyTwoHoles Var Var
  | CannotInferHoleType Var
  | NotAFunction Term
  | PatternNotSupported Pat
  | WrongConstructors [String] [String]
  | CannotUseReprAsTerm String

instance TermMappable TcError where
  mapTermMappableM f (NotAFunction t) = NotAFunction <$> mapTermM f t
  mapTermMappableM f (PatternNotSupported p) = PatternNotSupported <$> mapTermM f p
  mapTermMappableM f (Mismatch t1 t2) = Mismatch <$> mapTermM f t1 <*> mapTermM f t2
  mapTermMappableM _ e = return e

instance Show TcError where
  show (VariableNotFound v) = "Variable not found: " ++ printVal v
  show (Mismatch t1 t2) =
    "Term mismatch: " ++ printSingleVal t1 ++ " vs " ++ printSingleVal t2 ++ " (at " ++ printVal (getLoc t1) ++ " and " ++ printVal (getLoc t2) ++ ")"
  show (ItemNotFound s) = "Item not found: " ++ s
  show (CannotUnifyTwoHoles h1 h2) = "Cannot unify two holes: " ++ printSingleVal h1 ++ " and " ++ printSingleVal h2
  show (CannotInferHoleType h) = "Cannot infer hole type: " ++ printSingleVal h
  show (NotAFunction t) = "Not a function: " ++ printSingleVal t
  show (PatternNotSupported p) = "Pattern is not supported yet: " ++ printVal p
  show (WrongConstructors cs1 cs2) = "Wrong constructors: got " ++ intercalate ", " cs1 ++ " but expected " ++ intercalate ", " cs2
  show (CannotUseReprAsTerm r) = "Cannot use representation " ++ r ++ " as a term yet!"
