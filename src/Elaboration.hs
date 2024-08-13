module Elaboration
  ( ElabError (..),
  )
where

import Common (Name, PiMode)
import Presyntax (PTm)

data ElabError
  = Mismatch PTm PTm
  | UnresolvedVariable Name
  | ImplicitMismatch PiMode PiMode
  | InvalidPattern PTm
  | InvalidCaseSubject PTm
