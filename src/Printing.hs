{-# LANGUAGE MultiParamTypeClasses #-}
module Printing (Pretty (..), indented, curlies, indentedFst) where

import Data.List (intercalate)
import Control.Monad.Identity (Identity(runIdentity))

class (Monad m) => Pretty m a where
  pretty :: a -> m String

  prettyPure :: (m ~ Identity) => a -> String
  prettyPure x = runIdentity (pretty x)

  singlePretty :: a -> m String
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
