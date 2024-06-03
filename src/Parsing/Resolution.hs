module Parsing.Resolution (resolveGlobalsRec) where

import Checking.Context (Signature, lookupItemOrCtor)
import Lang
  ( MapResult (Continue, Replace),
    Term (..),
    TermValue (..),
    Var (..),
  )

-- | Resolve global variables in a term.
resolveGlobalsRec :: Signature -> Term -> MapResult Term
resolveGlobalsRec ctx (Term (V (Var v _)) d) = case lookupItemOrCtor v ctx of
  Just _ -> Replace (Term (Global v) d)
  Nothing -> Continue
resolveGlobalsRec _ _ = Continue
