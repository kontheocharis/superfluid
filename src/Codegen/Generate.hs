module Codegen.Generate (Gen, runGen, generateProgram, JsProg (..), renderJsProg) where

import Checking.Context (classifyApp, patVarToVar)
import Checking.Vars (Sub)
import Control.Monad.State (StateT, gets, modify, runStateT)
import Data.List (intercalate)
import Interface.Pretty (indentedFst)
import Lang (CtorItem (..), DataItem (DataItem), DeclItem, Item (..), PrimItem (..), Program (Program), Term (..), TermValue (..), appToList, letToList, listToApp, name, piTypeToList, value)
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

jsExprStat :: JsExpr -> JsStat
jsExprStat (JsExpr e) = JsStat e

jsAccess :: JsExpr -> String -> JsExpr
jsAccess (JsExpr e) s = JsExpr $ "(" ++ e ++ ")" ++ "." ++ s

jsIntIndex :: JsExpr -> Int -> JsExpr
jsIntIndex (JsExpr e) i = JsExpr $ "(" ++ e ++ ")" ++ "[" ++ show i ++ "]"

jsName :: String -> String
jsName "false" = "FALSE"
jsName "true" = "TRUE"
jsName "null" = "NULL"
jsName "undefined" = "UNDEFINED"
jsName n = concatMap (\c -> if c == '-' then "_" else if c == '\'' then "_p_" else [c]) n

addDecl :: JsStat -> Gen ()
addDecl d = modify (\s -> s {decls = s.decls ++ [d]})

addStdlibImports :: Gen ()
addStdlibImports = do
  addDecl $ jsConst "prompt" (JsExpr "require('prompt-sync')()")

generateProgram :: Program -> Gen JsProg
generateProgram (Program items) = do
  addStdlibImports
  mapM_ generateItem items
  addDecl $ jsExprStat (jsInvoke $ jsVar "main")
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
generateExpr t@(Term (App _ a b) _) = do
  case classifyApp t of
    Just _ -> do
      return jsNull
    Nothing -> do
      a' <- generateExpr a
      b' <- generateExpr b
      return $ jsApp a' b'
generateExpr (Term (Global s) _) = return $ jsVar (jsName s)
generateExpr (Term (V v) _) = return $ jsVar (jsName v.name)
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
          let caseBody = foldr jsLam c' args
          let c'' = foldr (flip jsApp . jsIntIndex t') caseBody [1 .. length args]
          return (p', c'')
      )
      cs
  return $ jsSwitch (jsIntIndex t' 0) cs'
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
generateDataItem (DataItem name ty ctors) = do
  let (params, _) = piTypeToList ty
  addDecl $ jsConst (jsName name) (foldr (\(_, n, _) acc -> jsLam (jsName n.name) acc) jsNull params)
  mapM_ generateDataCtor ctors

generateDataCtor :: CtorItem -> Gen ()
generateDataCtor (CtorItem name ty _ _) = do
  let (args, _) = piTypeToList ty
  let fn =
        foldr
          (\(_, n, _) acc -> jsLam (jsName n.name) acc)
          ( jsArray
              ( jsStringLit (jsName name)
                  : map (\(_, n, _) -> jsVar (jsName n.name)) args
              )
          )
          args
  addDecl $ jsConst (jsName name) fn

jsPrimArity0 :: String -> JsExpr -> JsStat
jsPrimArity0 n = jsConst (jsName n)

jsPrimArity1 :: String -> (JsExpr -> JsExpr) -> JsStat
jsPrimArity1 n f = jsConst (jsName n) (jsLam "a" (f (jsVar "a")))

jsPrimArity2 :: String -> (JsExpr -> JsExpr -> JsExpr) -> JsStat
jsPrimArity2 n f = jsConst (jsName n) (jsLam "a" (jsLam "b" (f (jsVar "a") (jsVar "b"))))

resolvePrimItem :: PrimItem -> Gen ()
resolvePrimItem (PrimItem n@"js-null" _) = do
  addDecl $ jsPrimArity0 n jsNull
resolvePrimItem (PrimItem n@"js-undefined" _) = do
  addDecl $ jsPrimArity0 n jsUndefined
resolvePrimItem (PrimItem n@"js-true" _) = do
  addDecl $ jsPrimArity0 n jsTrue
resolvePrimItem (PrimItem n@"js-false" _) = do
  addDecl $ jsPrimArity0 n jsFalse
resolvePrimItem (PrimItem n@"js-zero" _) = do
  addDecl $ jsPrimArity0 n jsZero
resolvePrimItem (PrimItem n@"js-one" _) = do
  addDecl $ jsPrimArity0 n jsOne
resolvePrimItem (PrimItem n@"js-plus" _) = do
  addDecl $ jsPrimArity2 n jsPlus
resolvePrimItem (PrimItem n@"js-minus" _) = do
  addDecl $ jsPrimArity2 n jsMinus
resolvePrimItem (PrimItem n@"js-times" _) = do
  addDecl $ jsPrimArity2 n jsTimes
resolvePrimItem (PrimItem n@"js-div" _) = do
  addDecl $ jsPrimArity2 n jsDiv
resolvePrimItem (PrimItem n@"js-mod" _) = do
  addDecl $ jsPrimArity2 n jsMod
resolvePrimItem (PrimItem n@"js-pow" _) = do
  addDecl $ jsPrimArity2 n jsPow
resolvePrimItem (PrimItem n@"js-neg" _) = do
  addDecl $ jsPrimArity1 n jsNeg
resolvePrimItem (PrimItem n@"js-eq" _) = do
  addDecl $ jsPrimArity2 n jsEq
resolvePrimItem (PrimItem n@"js-eqq" _) = do
  addDecl $ jsPrimArity2 n jsEqq
resolvePrimItem (PrimItem n@"js-neq" _) = do
  addDecl $ jsPrimArity2 n jsNeq
resolvePrimItem (PrimItem n@"js-neqq" _) = do
  addDecl $ jsPrimArity2 n jsNeqq
resolvePrimItem (PrimItem n@"js-lt" _) = do
  addDecl $ jsPrimArity2 n jsLt
resolvePrimItem (PrimItem n@"js-lte" _) = do
  addDecl $ jsPrimArity2 n jsLte
resolvePrimItem (PrimItem n@"js-gt" _) = do
  addDecl $ jsPrimArity2 n jsGt
resolvePrimItem (PrimItem n@"js-gte" _) = do
  addDecl $ jsPrimArity2 n jsGte
resolvePrimItem (PrimItem n@"js-and" _) = do
  addDecl $ jsPrimArity2 n jsAnd
resolvePrimItem (PrimItem n@"js-or" _) = do
  addDecl $ jsPrimArity2 n jsOr
resolvePrimItem (PrimItem n@"js-not" _) = do
  addDecl $ jsPrimArity1 n jsNot
resolvePrimItem (PrimItem n@"js-typeof" _) = do
  addDecl $ jsPrimArity1 n jsTypeof
resolvePrimItem (PrimItem n@"js-if" _) = do
  addDecl $
    jsConst
      (jsName n)
      ( jsLam
          "A"
          ( jsLam
              "cond"
              ( jsLam
                  "t"
                  ( jsLam
                      "f"
                      ( jsCond (jsVar "cond") (jsInvoke $ jsVar "t") (jsInvoke $ jsVar "f")
                      )
                  )
              )
          )
      )
resolvePrimItem (PrimItem n@"cast" _) = do
  addDecl $ jsConst (jsName n) (jsLam "A" (jsLam "B" (jsLam "a" (jsVar "a"))))
resolvePrimItem (PrimItem "IO" _) = do
  addDecl $ jsConst (jsName "IO") jsNull
resolvePrimItem (PrimItem "JS" _) = do
  addDecl $ jsConst (jsName "JS") jsNull
resolvePrimItem (PrimItem n@"io-return" _) = do
  addDecl $ jsConst (jsName n) (jsLam "A" (jsLam "a" (jsLazy $ jsVar "a")))
resolvePrimItem (PrimItem n@"io-bind" _) = do
  addDecl $ jsConst (jsName n) (jsLam "A" (jsLam "B" (jsLam "a" (jsLam "f" (jsLazy $ jsApp (jsVar "f") (jsVar "a"))))))
resolvePrimItem (PrimItem n@"js-console-log" _) = do
  addDecl $ jsConst (jsName n) (jsLam "a" (jsLazy $ jsApp (jsAccess (jsVar "console") "log") (jsVar "a")))
resolvePrimItem (PrimItem n@"js-prompt" _) = do
  addDecl $ jsConst (jsName n) (jsLazy $ jsInvoke (jsVar "prompt"))
resolvePrimItem (PrimItem n@"to-js" _) = do
  addDecl $ jsConst (jsName n) (jsLam "A" (jsLam "a" (jsVar "a")))
resolvePrimItem (PrimItem n _) = error $ "Unknown primitive: " ++ n

jsNull :: JsExpr
jsNull = JsExpr "null"

jsUndefined :: JsExpr
jsUndefined = JsExpr "undefined"

jsTrue :: JsExpr
jsTrue = JsExpr "true"

jsFalse :: JsExpr
jsFalse = JsExpr "false"

jsZero :: JsExpr
jsZero = JsExpr "0"

jsOne :: JsExpr
jsOne = JsExpr "1"

jsPlus :: JsExpr -> JsExpr -> JsExpr
jsPlus (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") + (" ++ b ++ ")"

jsMinus :: JsExpr -> JsExpr -> JsExpr
jsMinus (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") - (" ++ b ++ ")"

jsTimes :: JsExpr -> JsExpr -> JsExpr
jsTimes (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") * (" ++ b ++ ")"

jsDiv :: JsExpr -> JsExpr -> JsExpr
jsDiv (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") / (" ++ b ++ ")"

jsMod :: JsExpr -> JsExpr -> JsExpr
jsMod (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") % (" ++ b ++ ")"

jsPow :: JsExpr -> JsExpr -> JsExpr
jsPow (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") ** (" ++ b ++ ")"

jsNeg :: JsExpr -> JsExpr
jsNeg (JsExpr a) = JsExpr $ "-(" ++ a ++ ")"

jsEq :: JsExpr -> JsExpr -> JsExpr
jsEq (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") == (" ++ b ++ ")"

jsEqq :: JsExpr -> JsExpr -> JsExpr
jsEqq (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") === (" ++ b ++ ")"

jsNeq :: JsExpr -> JsExpr -> JsExpr
jsNeq (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") != (" ++ b ++ ")"

jsNeqq :: JsExpr -> JsExpr -> JsExpr
jsNeqq (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") !== (" ++ b ++ ")"

jsLt :: JsExpr -> JsExpr -> JsExpr
jsLt (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") < (" ++ b ++ ")"

jsLte :: JsExpr -> JsExpr -> JsExpr
jsLte (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") <= (" ++ b ++ ")"

jsGt :: JsExpr -> JsExpr -> JsExpr
jsGt (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") > (" ++ b ++ ")"

jsGte :: JsExpr -> JsExpr -> JsExpr
jsGte (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") >= (" ++ b ++ ")"

jsAnd :: JsExpr -> JsExpr -> JsExpr
jsAnd (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") && (" ++ b ++ ")"

jsOr :: JsExpr -> JsExpr -> JsExpr
jsOr (JsExpr a) (JsExpr b) = JsExpr $ "(" ++ a ++ ") || (" ++ b ++ ")"

jsNot :: JsExpr -> JsExpr
jsNot (JsExpr a) = JsExpr $ "!(" ++ a ++ ")"

jsCond :: JsExpr -> JsExpr -> JsExpr -> JsExpr
jsCond (JsExpr c) (JsExpr t) (JsExpr f) = JsExpr $ "(" ++ c ++ ") ? (" ++ t ++ ") : (" ++ f ++ ")"

jsTypeof :: JsExpr -> JsExpr
jsTypeof (JsExpr e) = JsExpr $ "typeof (" ++ e ++ ")"

jsLam :: String -> JsExpr -> JsExpr
jsLam arg (JsExpr b) = JsExpr $ "(" ++ arg ++ ") => " ++ b

jsLazy :: JsExpr -> JsExpr
jsLazy (JsExpr e) = JsExpr $ "(() => " ++ e ++ ")"

jsReturn :: JsExpr -> JsStat
jsReturn (JsExpr e) = JsStat $ "return " ++ e ++ ";"

jsApp :: JsExpr -> JsExpr -> JsExpr
jsApp (JsExpr f) (JsExpr a) = JsExpr $ "(" ++ f ++ ")" ++ "(" ++ a ++ ")"

jsBlockExpr :: [JsStat] -> JsExpr
jsBlockExpr ss = JsExpr $ "(() => {\n" ++ indentedFst (intercalate "\n" (map (\(JsStat s) -> s) ss)) ++ "\n})()"

jsVar :: String -> JsExpr
jsVar s = JsExpr s

jsStringLit :: String -> JsExpr
jsStringLit s = JsExpr $ "\"" ++ s ++ "\""

jsArray :: [JsExpr] -> JsExpr
jsArray es = JsExpr $ "[" ++ intercalate ", " (map (\(JsExpr e) -> e) es) ++ "]"

jsSwitch :: JsExpr -> [(JsExpr, JsExpr)] -> JsExpr
jsSwitch (JsExpr e) cs =
  let switch =
        JsStat $
          "switch ("
            ++ e
            ++ ") {\n"
            ++ indentedFst
              ( intercalate
                  "\n"
                  (map (\(JsExpr c, s) -> let JsStat r = jsReturn s in "case " ++ c ++ ": " ++ r) cs)
              )
            ++ "\n}"
   in jsBlockExpr [switch]

jsObj :: [(String, JsExpr)] -> JsExpr
jsObj ps = JsExpr $ "{" ++ intercalate ", " (map (\(s, JsExpr e) -> s ++ ": " ++ e) ps) ++ "}"

jsInvoke :: JsExpr -> JsExpr
jsInvoke (JsExpr e) = JsExpr $ "(" ++ e ++ ")()"
