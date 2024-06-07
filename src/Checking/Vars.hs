module Checking.Vars (var, Sub (..), Subst, sub, subVar, alphaRename, noSub) where

import Checking.Context (Ctx (..), Judgement (..))
import Data.List (intercalate)
import Lang

-- | Helper function to create a variable without caring about the unique identifier.
var :: String -> Var
var x = Var x 0

-- | A substitution, represented as a list of variable-term pairs.
newtype Sub = Sub [(Var, Term)]

instance Show Sub where
  show (Sub s) = "[" ++ intercalate ", " (map (\(v, t) -> show v ++ " -> " ++ show t) s) ++ "]"

-- | Empty substitution.
noSub :: Sub
noSub = Sub []

instance Monoid Sub where
  mempty = noSub

instance Semigroup Sub where
  -- This is not a particularly smart way to do this, but it works.
  (<>) (Sub s1) (Sub s2) = Sub (as ++ bs)
    where
      Sub as = sub (Sub s2) (Sub s1)
      Sub bs = sub (Sub s1) (Sub s2)

-- | A typeclass for things that can be substituted.
class Subst a where
  -- | Apply a `Sub` to a term.
  sub :: Sub -> a -> a
  sub (Sub ((v, t') : ss)) t = sub (Sub ss) (subVar v t' t)
  sub (Sub []) t = t

  -- | Substitute a variable for a term in a term.
  subVar :: Var -> Term -> a -> a

instance Subst Term where
  subVar v t' =
    mapTerm
      ( \t'' -> case t''.value of
          V v' | v == v' -> Replace t'
          Hole v' | v == v' -> Replace t'
          _ -> Continue
      )

instance Subst Sub where
  subVar v' t' (Sub ((v, t) : s)) = Sub ((v, subVar v' t' t) : let Sub rs = subVar v' t' (Sub s) in rs)
  subVar _ _ (Sub []) = Sub []

instance Subst Ctx where
  subVar v' t' (Ctx js) =
    Ctx
      ( map
          ( \case
              (Typing v t) -> Typing v (subVar v' t' t)
              (Subst v t) -> Subst v (subVar v' t' t)
          )
          js
      )

-- | Alpha rename a variable in a term.
alphaRename :: Var -> (Var, TermData) -> Term -> Term
alphaRename v1 (v2, d) = subVar v1 (Term (V v2) d)
