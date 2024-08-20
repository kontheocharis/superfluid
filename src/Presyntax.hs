module Presyntax
  ( PTy,
    PPat,
    Tag,
    PDef (..),
    PCtor (..),
    PData (..),
    PCtorRep (..),
    PCaseRep (..),
    PDataRep (..),
    PDefRep (..),
    PItem (..),
    PTm (..),
    PPrim (..),
    PProgram (..),
    tagged,
    pApp,
  )
where

import Common (Arg, Clause, Lit, Loc, Name, PiMode, Pos, Tag, Times, arg, mode)
import Data.Set (Set)
import Data.Typeable (Typeable)
import Printing (Pretty (..))

type PTy = PTm

type PPat = PTm

data PDef = MkPDef
  { name :: Name,
    ty :: PTy,
    tm :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

tagged :: Set Tag -> PItem -> PItem
tagged ts (PData d) = PData $ d {tags = ts}
tagged ts (PDef d) = PDef $ d {tags = ts}
tagged ts (PDataRep d) = PDataRep $ d {tags = ts}
tagged ts (PDefRep d) = PDefRep $ d {tags = ts}
tagged ts (PPrim d) = PPrim $ d {tags = ts}
tagged ts (PLocatedItem loc i) = PLocatedItem loc $ tagged ts i

data PCtor = MkPCtor
  { name :: Name,
    ty :: PTy,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PData = MkPData
  { name :: Name,
    ty :: PTy,
    ctors :: [PCtor],
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PCtorRep = MkPCtorRep
  { src :: PPat,
    target :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PCaseRep = MkPCaseRep
  { srcSubject :: PPat,
    srcBranches :: [(Name, PPat)],
    target :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PDataRep = MkPDataRep
  { src :: PPat,
    target :: PTy,
    ctors :: [PCtorRep],
    caseExpr :: PCaseRep,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PDefRep = MkPDefRep
  { src :: PPat,
    target :: PTm,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PPrim = MkPPrim
  { name :: Name,
    ty :: PTy,
    tags :: Set Tag
  }
  deriving (Eq, Show)

data PItem
  = PDef PDef
  | PData PData
  | PDataRep PDataRep
  | PDefRep PDefRep
  | PPrim PPrim
  | PLocatedItem Loc PItem
  deriving (Eq, Typeable, Show)

newtype PProgram = PProgram [PItem] deriving (Eq, Show)

data PTm
  = PPi PiMode Name PTy PTy
  | PLam PiMode Name PTm
  | PLet Name PTy PTm PTm
  | PApp PiMode PTm PTm
  | PCase PTm [Clause PPat PTm]
  | PU
  | PName Name
  | PLit (Lit PTm)
  | PHole Name
  | PRepr Times PTm
  | PWild
  | PLocated Loc PTm
  deriving (Eq, Show)

pApp :: PTm -> [Arg PTm] -> PTm
pApp = foldl (\g x -> PApp x.mode g x.arg)

isCompound :: PTm -> Bool
isCompound (PPi {}) = True
isCompound (PLam {}) = True
isCompound (PLet {}) = True
isCompound (PCase {}) = True
isCompound (PApp {}) = True
isCompound (PRepr {}) = True
isCompound (PLocated _ t) = isCompound t
isCompound _ = False


instance Pretty PTm where
  -- \| Show a term value, with parentheses if it is compound.
  singlePretty v | isCompound v = "(" ++ pretty v ++ ")"
  singlePretty v = pretty v

  -- printVal (PiT Explicit v t1 t2) = "(" ++ printVal v ++ " : " ++ printVal t1 ++ ") -> " ++ printVal t2
  -- printVal (PiT Implicit v t1 t2) = "[" ++ printVal v ++ " : " ++ printVal t1 ++ "] -> " ++ printVal t2
  -- printVal (PiT Instance v t1 t2) = "[[" ++ printVal v ++ " : " ++ printVal t1 ++ "]] -> " ++ printVal t2
  -- printVal l@(Lam {}) =
  --   let (vs, b) = lamsToList (genTerm l)
  --    in "\\"
  --         ++ intercalate
  --           " "
  --           ( map
  --               ( \(m, v) -> case m of
  --                   Explicit -> printSingleVal v
  --                   Implicit -> "[" ++ printVal v ++ "]"
  --                   Instance -> "[[" ++ printVal v ++ "]]"
  --               )
  --               vs
  --           )
  --         ++ " => "
  --         ++ printVal b
  -- printVal (SigmaT v t1 t2) = "(" ++ printVal v ++ " : " ++ printVal t1 ++ ") * " ++ printVal t2
  -- printVal (Pair t1 t2) = "(" ++ printVal t1 ++ ", " ++ printVal t2 ++ ")"
  -- printVal t@(App {}) =
  --   let (x, xs) = appToList (genTerm t)
  --    in printSingleVal x
  --         ++ " "
  --         ++ intercalate
  --           " "
  --           ( map
  --               ( \(m, x') -> case m of
  --                   Explicit -> printSingleVal x'
  --                   Implicit -> "[" ++ printVal x' ++ "]"
  --                   Instance -> "[[" ++ printVal x' ++ "]]"
  --               )
  --               xs
  --           )
  -- printVal l@(Let {}) =
  --   curlies $
  --     let (binds, ret) = letToList (genTerm l)
  --      in intercalate "\n" $
  --           map
  --             (\(v, ty, t) -> "let " ++ printVal v ++ " : " ++ printVal ty ++ " = " ++ printVal t ++ ";")
  --             binds
  --             ++ [printVal ret]
  -- printVal (Case _ t cs) =
  --   "case "
  --     ++ printSingleVal t
  --     ++ " "
  --     ++ curlies
  --       ( intercalate
  --           ",\n"
  --           ( map
  --               ( \(p, c) ->
  --                   printVal p ++ " => " ++ maybe "!" printVal c
  --               )
  --               cs
  --           )
  --       )
  -- printVal TyT = "Type"
  -- printVal Wild = "_"
  -- printVal (V v) = printVal v
  -- printVal (Global s) = s
  -- printVal (Hole i) = "?" ++ printVal i
  -- printVal (Meta i) = "!" ++ printVal i
  -- printVal (Lit s) = printVal s
  -- printVal (Rep s) = "repr " ++ printSingleVal s
  -- printVal (Unrep n s) = "unrepr " ++ n ++ " " ++ printSingleVal s
