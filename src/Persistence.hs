{-# LANGUAGE TemplateHaskell #-}

module Persistence (preludePath, bootPath) where

import Data.FileEmbed (makeRelativeToProject, strToExp)

-- | The path of the Prelude file.
preludePath :: FilePath
preludePath = $(makeRelativeToProject "bootstrap/prelude.sf" >>= strToExp)

-- | The path of the Boot file.
bootPath :: FilePath
bootPath = $(makeRelativeToProject "bootstrap/boot.js" >>= strToExp)
