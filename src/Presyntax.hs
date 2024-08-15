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
