module Codegen.Generate (Gen, runGen, generateProgram) where

import Control.Monad.State (StateT, gets, runStateT)
import Lang (Item (..), Program (Program), PrimItem, DataItem, DeclItem)
import Language.C (CExtDecl, CExternalDeclaration, CTranslUnit, CTranslationUnit (..), undefNode)

data GenState = GenState
  { decls :: [CExtDecl]
  }

data GenError = GenError

instance Show GenError where
  show _ = "Generation error"

type Gen a = StateT GenState (Either GenError) a

emptyGenState :: GenState
emptyGenState =
  GenState
    { decls = []
    }

runGen :: Gen a -> Either GenError a
runGen x = do
  (r, _) <- runStateT x emptyGenState
  return r

generateProgram :: Program -> Gen CTranslUnit
generateProgram (Program items) = do
  mapM_ generateItem items
  ds <- gets (\s -> s.decls)
  return $ CTranslUnit ds undefNode

generateItem :: Item -> Gen ()
generateItem (Data d) = generateDataItem d
generateItem (Repr _) = error "Found repr item in generateItem"
generateItem (Decl d) = generateDeclItem d
generateItem (Prim p) = resolvePrimItem p

generateDeclItem :: DeclItem -> Gen ()
generateDeclItem = undefined

generateDataItem :: DataItem -> Gen ()
generateDataItem = undefined

resolvePrimItem :: PrimItem -> Gen ()
resolvePrimItem = undefined
