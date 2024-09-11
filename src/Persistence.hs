{-# LANGUAGE TemplateHaskell #-}

module Persistence (preludePath, preludeContents) where

import Data.FileEmbed (embedStringFile, makeRelativeToProject, strToExp)
import Data.String (IsString)

-- | The contents of the Prelude file.
preludePath :: FilePath
preludePath = $(makeRelativeToProject "src/Resources/prelude.sf" >>= strToExp)

-- | The contents of the Prelude file.
preludeContents :: (IsString a) => a
preludeContents = $(makeRelativeToProject "src/Resources/prelude.sf" >>= embedStringFile)
