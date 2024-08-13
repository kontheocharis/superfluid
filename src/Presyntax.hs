module Presyntax
  ( PTy,
    PPat,
    PDef (..),
    PCtor (..),
    PData (..),
    PCtorRep (..),
    PCaseRep (..),
    PDataRep (..),
    PDefRep (..),
    PItem (..),
    PTm (..),
  )
where

import Common (Clause, Lit, Name, PiMode, Pos, Times)
import Data.Typeable (Typeable)

type PTy = PTm

type PPat = PTm

data PDef = MkPDef
  { name :: Name,
    ty :: PTy,
    tm :: PTm,
    unfold :: Bool,
    recursive :: Bool
  }
  deriving (Eq, Show)

data PCtor = MkPCtor
  { name :: Name,
    ty :: PTy
  }
  deriving (Eq, Show)

data PData = MkPData
  { name :: Name,
    ty :: PTy,
    ctors :: [PCtor]
  }
  deriving (Eq, Show)

data PCtorRep = MkPCtorRep
  { src :: PPat,
    target :: PTm
  }
  deriving (Eq, Show)

data PCaseRep = MkPCaseRep
  { srcSubject :: PPat,
    srcBranches :: [Clause Name PPat],
    target :: PTm
  }
  deriving (Eq, Show)

data PDataRep = MkPRep
  { src :: PPat,
    target :: PTy,
    ctors :: [PCtorRep],
    caseExpr :: PCaseRep
  }
  deriving (Eq, Show)

data PDefRep = MkPDefRep
  { src :: PPat,
    target :: PTm
  }
  deriving (Eq, Show)

data PItem
  = PDef PDef
  | PData PData
  | PDataRep PDataRep
  | PDefRep PDefRep
  deriving (Eq, Typeable, Show)

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
  | PLocated Pos PTm
  deriving (Eq, Show)
