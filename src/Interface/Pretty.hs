module Interface.Pretty (Print (..), indented, indentedFst) where

import Data.List (intercalate)
import Lang

-- | Typeclass like Show but for syntax.
class Print a where
  printVal :: a -> String

  printSingleVal :: a -> String
  printSingleVal = printVal

-- | Replace each newline with a newline followed by 2 spaces.
indented :: String -> String
indented str
  | (l : ls) <- lines str = intercalate "\n" $ l : map ("  " ++) ls
  | [] <- lines str = ""

curlies :: String -> String
curlies str = "{\n" ++ indentedFst str ++ "\n}"

-- | Replace each newline with a newline followed by 2 spaces (and the first line).
indentedFst :: String -> String
indentedFst str = "  " ++ indented str

instance Print Var where
  -- printVal (Var s n) = s ++ show n
  printVal (Var s _) = s

instance Print TermValue where
  -- \| Show a term value, with parentheses if it is compound.
  printSingleVal v | (isCompound . getTermValue) v = "(" ++ printVal v ++ ")"
  printSingleVal v = printVal v

  printVal (PiT v t1 t2) = "(" ++ printVal v ++ " : " ++ printVal t1 ++ ") -> " ++ printVal t2
  printVal l@(Lam _ _) = let (vs, b) = lamsToList (genTerm l) in "\\" ++ intercalate " " (map printSingleVal vs) ++ " => " ++ printVal b
  printVal (SigmaT v t1 t2) = "(" ++ printVal v ++ " : " ++ printVal t1 ++ ") ** " ++ printVal t2
  printVal (Pair t1 t2) = "(" ++ printVal t1 ++ ", " ++ printVal t2 ++ ")"
  printVal t@(App _ _) = intercalate " " $ map printSingleVal (let (x, xs) = appToList (genTerm t) in x : xs)
  printVal l@(Let {}) =
    curlies $
      let (binds, ret) = letToList (genTerm l)
       in intercalate "\n" $
            map
              (\(v, ty, t) -> "let " ++ printVal v ++ " : " ++ printVal ty ++ " = " ++ printVal t ++ ";")
              binds
              ++ [printVal ret]
  printVal (Case t cs) =
    "case "
      ++ printVal t
      ++ " "
      ++ curlies
        ( intercalate
            ",\n"
            (map (\(p, c) -> printVal p ++ " => " ++ printVal c) cs)
        )
  printVal TyT = "Type"
  printVal Wild = "_"
  printVal (V v) = printVal v
  printVal (Global s) = s
  printVal (Hole i) = "?" ++ printVal i
  printVal (Meta i) = "!" ++ printVal i

instance Print Loc where
  printVal NoLoc = ""
  printVal (Loc l c) = printVal l ++ "--" ++ printVal c

instance Print Pos where
  printVal (Pos l c) = show l ++ ":" ++ show c

instance Print TermData where
  printVal (TermData l Nothing) = "loc=" ++ printVal l ++ ", type=" ++ "Nothing"
  printVal (TermData l (Just t)) = "loc=" ++ printVal l ++ ", type=" ++ "Just " ++ printSingleVal t

instance Print Term where
  printVal (Term t _) = printVal t --  ++ " " ++ printTermData d

  printSingleVal (Term t _) = printSingleVal t

instance Print Item where
  printVal (Decl d) = printVal d
  printVal (Data d) = printVal d
  printVal (Repr r) = printVal r

instance Print DeclItem where
  printVal (DeclItem v ty term _) =
    "def " ++ v ++ " : " ++ printVal ty ++ " " ++ case term.value of
      Let {} -> printVal term
      _ -> curlies $ printVal term

instance Print DataItem where
  printVal (DataItem name ty ctors) =
    "data "
      ++ name
      ++ " : "
      ++ printVal ty
      ++ " "
      ++ curlies (intercalate ",\n" (map printVal ctors))

instance Print CtorItem where
  printVal (CtorItem name ty _ _) = name ++ " : " ++ printVal ty

instance Print ReprItem where
  printVal (ReprItem name cs) =
    "repr "
      ++ name
      ++ " "
      ++ curlies (intercalate "\n\n" (map printVal cs))

instance Print ReprSomeItem where
  printVal (ReprData d) = printVal d
  printVal (ReprDecl d) = printVal d

instance Print ReprDataItem where
  printVal (ReprDataItem name binds target ctors cse) =
    "data "
      ++ name
      ++ (if null binds then "" else " ")
      ++ intercalate " " (map printVal binds)
      ++ " as "
      ++ printVal target
      ++ " "
      ++ curlies
        ( intercalate ",\n" (map printVal ctors)
            ++ case cse of
              Just cse' ->
                ",\n" ++ printVal cse'
              Nothing -> ""
        )

instance Print ReprDataCtorItem where
  printVal (ReprDataCtorItem name binds target) = name ++ (if null binds then "" else " ") ++ intercalate " " (map printVal binds) ++ " as " ++ printVal target

instance Print ReprDataCaseItem where
  printVal (ReprDataCaseItem (subject, ctors) target) =
    "case "
      ++ printVal subject
      ++ " "
      ++ curlies
        ( intercalate ",\n" (map (\(c, b) -> c ++ " => " ++ printVal b) ctors)
        )
      ++ " as "
      ++ printVal target

instance Print ReprDeclItem where
  printVal (ReprDeclItem name target) = "def " ++ name ++ " as " ++ printVal target

instance Print Program where
  printVal (Program ds) = intercalate "\n\n" $ map printVal ds
