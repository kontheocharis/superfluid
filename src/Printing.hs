module Printing (Pretty (..), indented, curlies, indentedFst) where

import Data.List (intercalate)

class Pretty a where
  pretty :: a -> String

  singlePretty :: a -> String
  singlePretty = pretty

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
