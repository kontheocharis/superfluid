{-# LANGUAGE TemplateHaskell #-}

module Persistence (preludePath) where

import Data.FileEmbed (makeRelativeToProject, strToExp)

-- | The contents of the Prelude file.
preludePath :: FilePath
preludePath = $(makeRelativeToProject "bootstrap/prelude.sf" >>= strToExp)
