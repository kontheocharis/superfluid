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

import Common (Arg (..), Clause (..), Lit, Loc, Name, PiMode (..), Pos, Tag, Times (..), arg, mode)
import Data.List (intercalate)
import Data.Set (Set)
import Data.Typeable (Typeable)
import Printing (Pretty (..), curlies)

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
  | PSigma Name PTy PTy
  | PLam PiMode Name PTm
  | PLet Name PTy PTm PTm
  | PPair PTm PTm
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

pLamsToList :: PTm -> ([Arg Name], PTm)
pLamsToList (PLam m n t) = let (ns, b) = pLamsToList t in (Arg m n : ns, b)
pLamsToList t = ([], t)

pAppToList :: PTm -> (PTm, [Arg PTm])
pAppToList (PApp m t u) = let (t', us) = pAppToList t in (t', us ++ [Arg m u])
pAppToList t = (t, [])

pLetToList :: PTm -> ([(Name, PTy, PTm)], PTm)
pLetToList (PLet n ty t1 t2) = let (binds, ret) = pLetToList t2 in ((n, ty, t1) : binds, ret)
pLetToList t = ([], t)

isCompound :: PTm -> Bool
isCompound (PPi {}) = True
isCompound (PSigma {}) = True
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

  pretty (PPi Explicit v t1 t2) = "(" ++ pretty v ++ " : " ++ pretty t1 ++ ") -> " ++ pretty t2
  pretty (PPi Implicit v t1 t2) = "[" ++ pretty v ++ " : " ++ pretty t1 ++ "] -> " ++ pretty t2
  pretty (PPi Instance v t1 t2) = "[[" ++ pretty v ++ " : " ++ pretty t1 ++ "]] -> " ++ pretty t2
  pretty l@(PLam {}) =
    let (vs, b) = pLamsToList l
     in "\\" ++ intercalate " " (map pretty vs) ++ " => " ++ pretty b
  pretty (PSigma v t1 t2) = "(" ++ pretty v ++ " : " ++ pretty t1 ++ ") * " ++ pretty t2
  pretty (PPair t1 t2) = "(" ++ pretty t1 ++ ", " ++ pretty t2 ++ ")"
  pretty t@(PApp {}) =
    let (x, xs) = pAppToList t
     in pretty x ++ " " ++ intercalate " " (map pretty xs)
  pretty l@(PLet {}) =
    curlies $
      let (binds, ret) = pLetToList l
       in intercalate "\n" $
            map
              (\(v, ty, t) -> "let " ++ pretty v ++ " : " ++ pretty ty ++ " = " ++ pretty t ++ ";")
              binds
              ++ [pretty ret]
  pretty (PCase t cs) =
    "case "
      ++ pretty t
      ++ " "
      ++ curlies
        ( intercalate
            ",\n"
            ( map
                ( \(Clause p c) ->
                    pretty p ++ " => " ++ maybe "impossible" pretty c
                )
                cs
            )
        )
  pretty PU = "Type"
  pretty PWild = "_"
  pretty (PName n) = pretty n
  pretty (PLit l) = pretty l
  pretty (PHole i) = "?" ++ pretty i
  pretty (PRepr n s) = "repr " ++ if n == Finite 1 then "" else (pretty n ++ " ") ++ pretty s
  pretty (PLocated _ t) = pretty t
