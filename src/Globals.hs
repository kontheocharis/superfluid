module Globals
  ( CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (..),
    Glob (..),
  )
where

import Common (Name)

newtype CtorGlobal = CtorGlobal Name deriving (Eq, Show)

newtype DataGlobal = DataGlobal Name deriving (Eq, Show)

newtype DefGlobal = DefGlobal Name deriving (Eq, Show)

data Glob = CtorGlob CtorGlobal | DataGlob DataGlobal | DefGlob DefGlobal deriving (Eq, Show)
