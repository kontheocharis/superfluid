module Codegen.Generate (Gen, runGen, generateProgram, JsProg (..), renderJsProg) where

import Checking.Context (patVarToVar)
import Checking.Vars (Sub)
import Control.Monad.State (StateT, gets, modify, runStateT)
import Data.List (intercalate)
import Interface.Pretty (indentedFst)
import Lang (CtorItem (..), DataItem (DataItem), DeclItem, Item (..), PrimItem, Program (Program), Term (..), TermValue (..), appToList, letToList, listToApp, name, piTypeToList, value)
import Language.C (CExtDecl, CExternalDeclaration, CTranslUnit, CTranslationUnit (..), undefNode)
import Language.JavaScript.Parser (JSAST (JSAstProgram), JSAnnot (JSNoAnnot), JSAssignOp (..), JSExpression (JSAssignExpression, JSIdentifier, JSStringLiteral), JSStatement (JSConstant))
import Language.JavaScript.Parser.AST (JSCommaList (JSLOne), JSSemi (..))

data GenState = GenState
  { decls :: [JsStat]
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

data JsStat = JsStat String

data JsExpr = JsExpr String

data JsProg = JsProg String

renderJsProg :: JsProg -> String
renderJsProg (JsProg s) = s

jsProgFromStats :: [JsStat] -> JsProg
jsProgFromStats stats = JsProg $ intercalate "\n" $ map (\(JsStat s) -> s) stats

jsConst :: String -> JsExpr -> JsStat
jsConst name (JsExpr e) = JsStat $ "const " ++ name ++ " = " ++ e ++ ";"

jsName :: String -> String
jsName "false" = "FALSE"
jsName "true" = "TRUE"
jsName "null" = "NULL"
jsName "undefined" = "UNDEFINED"
jsName n = concatMap (\c -> if c == '-' then "_" else if c == '\'' then "_p_" else [c]) n

jsNull :: JsExpr
jsNull = JsExpr "null"

jsLam :: String -> JsExpr -> JsExpr
jsLam arg (JsExpr b) = JsExpr $ "(" ++ arg ++ ") => " ++ b

jsReturn :: JsExpr -> JsStat
jsReturn (JsExpr e) = JsStat $ "return " ++ e ++ ";"

jsApp :: JsExpr -> JsExpr -> JsExpr
jsApp (JsExpr f) (JsExpr a) = JsExpr $ "(" ++ f ++ ")" ++ "(" ++ a ++ ")"

jsBlockExpr :: [JsStat] -> JsExpr
jsBlockExpr ss = JsExpr $ "(() => {\n" ++ indentedFst (intercalate "\n" (map (\(JsStat s) -> s) ss)) ++ "\n})()"

jsVariable :: String -> JsExpr
jsVariable s = JsExpr s

jsStringLit :: String -> JsExpr
jsStringLit s = JsExpr $ "\"" ++ s ++ "\""

jsArray :: [JsExpr] -> JsExpr
jsArray es = JsExpr $ "[" ++ intercalate ", " (map (\(JsExpr e) -> e) es) ++ "]"

jsSwitch :: JsExpr -> [(JsExpr, JsExpr)] -> JsExpr
jsSwitch (JsExpr e) cs = JsExpr $ "switch (" ++ e ++ ") {\n" ++ indentedFst (intercalate "\n" (map (\(JsExpr c, JsExpr s) -> "case " ++ c ++ ": " ++ s) cs)) ++ "\n}"

jsAccess :: JsExpr -> String -> JsExpr
jsAccess (JsExpr e) s = JsExpr $ e ++ "." ++ s

jsObj :: [(String, JsExpr)] -> JsExpr
jsObj ps = JsExpr $ "{" ++ intercalate ", " (map (\(s, JsExpr e) -> s ++ ": " ++ e) ps) ++ "}"

addDecl :: JsStat -> Gen ()
addDecl d = modify (\s -> s {decls = d : s.decls})

primAccess :: JsExpr -> String -> JsExpr
primAccess (JsExpr e) s = JsExpr $ "(" ++ e ++ ")" ++ "." ++ s

generateProgram :: Program -> Gen JsProg
generateProgram (Program items) = do
  mapM_ generateItem items
  ds <- gets (\s -> s.decls)
  return $ jsProgFromStats ds

generateItem :: Item -> Gen ()
generateItem (Data d) = generateDataItem d
generateItem (Repr _) = error "Found repr item in generateItem"
generateItem (Decl d) = generateDeclItem d
generateItem (Prim p) = resolvePrimItem p

generateDeclItem :: DeclItem -> Gen ()
generateDeclItem d = do
  t <- generateExpr d.value
  addDecl $ jsConst (jsName d.name) t

generateExpr :: Term -> Gen JsExpr
generateExpr (Term (PiT {}) _) = return jsNull
generateExpr (Term (SigmaT {}) _) = return jsNull
generateExpr (Term TyT _) = return jsNull
generateExpr (Term (Lam _ v t) _) = do
  t' <- generateExpr t
  return $ jsLam (jsName v.name) t'
generateExpr ls@(Term (Let {}) _) = do
  let (xs, ret) = letToList ls
  statements <-
    mapM
      ( \(v, _, t) -> do
          t' <- generateExpr t
          return $ jsConst (jsName v.name) t'
      )
      xs
  ret' <- jsReturn <$> generateExpr ret
  return $ jsBlockExpr (statements ++ [ret'])
generateExpr (Term (App _ t u) _) = do
  t' <- generateExpr t
  u' <- generateExpr u
  return $ jsApp t' u'
generateExpr (Term (Global s) _) = return $ jsVariable (jsName s)
generateExpr (Term (V v) _) = return $ jsVariable (jsName v.name)
generateExpr (Term (Pair t1 t2) _) = do
  t1' <- generateExpr t1
  t2' <- generateExpr t2
  return $ jsArray [t1', t2']
generateExpr (Term (Case t cs) _) = do
  t' <- generateExpr t
  cs' <-
    mapM
      ( \(p, c) -> do
          (p', args) <- generatePat p
          c' <- generateExpr c
          let c'' = foldr jsLam c' args
          return (p', c'')
      )
      cs
  return $ jsSwitch (jsAccess t' "tag") cs'
generateExpr (Term Wild _) = return jsNull
generateExpr (Term (Hole _) _) = return jsNull
generateExpr (Term (Meta _) _) = return jsNull

generatePat :: Term -> Gen (JsExpr, [String])
generatePat t = do
  let (t', ts) = appToList t
  case t' of
    Term (Global s) _ -> do
      let ts' =
            map
              ( \(_, x) ->
                  ( case x of
                      Term (V v) _ -> jsName v.name
                      _ -> error "Non-variable in pattern"
                  )
              )
              ts
      return (jsStringLit (jsName s), ts')
    _ -> error "Non-global in pattern"

generateDataItem :: DataItem -> Gen ()
generateDataItem (DataItem _ _ ctors) = mapM_ generateDataCtor ctors

generateDataCtor :: CtorItem -> Gen ()
generateDataCtor (CtorItem name ty _ _) = do
  let (args, _) = piTypeToList ty
  let fn =
        foldr
          (\(_, n, _) acc -> jsLam (jsName n.name) acc)
          ( jsObj
              ( ("tag", jsStringLit (jsName name))
                  : map (\(_, n, _) -> (jsName n.name, jsVariable (jsName n.name))) args
              )
          )
          args
  addDecl $ jsConst (jsName name) fn

resolvePrimItem :: PrimItem -> Gen ()
resolvePrimItem _ = return ()
