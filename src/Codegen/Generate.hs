module Codegen.Generate (Gen, runGen, generateProgram, JsProg (..), renderJsProg) where

import Checking.Context (Signature, asSig, classifyApp, lookupItemOrCtor, patVarToVar)
import Checking.Vars (Sub)
import Control.Monad.State (StateT, gets, modify, runStateT)
import Data.List (intercalate)
import Interface.Pretty (indentedFst)
import Lang (CtorItem (..), DataItem (DataItem), DeclItem, Item (..), PrimItem (..), Program (Program), Term (..), TermValue (..), Type, appToList, letToList, listToApp, name, piTypeToList, value)
import Language.C (CExtDecl, CExternalDeclaration, CTranslUnit, CTranslationUnit (..), undefNode)
import Language.JavaScript.Parser (JSAST (JSAstProgram), JSAnnot (JSNoAnnot), JSAssignOp (..), JSExpression (JSAssignExpression, JSIdentifier, JSStringLiteral), JSStatement (JSConstant))
import Language.JavaScript.Parser.AST (JSCommaList (JSLOne), JSSemi (..))

data GenState = GenState
  { decls :: [JsStat],
    program :: Program
  }

data GenError = GenError

instance Show GenError where
  show _ = "Generation error"

type Gen a = StateT GenState (Either GenError) a

emptyGenState :: GenState
emptyGenState =
  GenState
    { decls = [],
      program = Program []
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

jsIndex :: JsExpr -> JsExpr -> JsExpr
jsIndex (JsExpr e) (JsExpr i) = JsExpr $ "(" ++ e ++ ")" ++ "[" ++ i ++ "]"

jsIntIndex :: JsExpr -> Int -> JsExpr
jsIntIndex (JsExpr e) i = JsExpr $ "(" ++ e ++ ")" ++ "[" ++ show i ++ "]"

jsName :: String -> String
jsName "false" = "FALSE"
jsName "true" = "TRUE"
jsName "null" = "NULL"
jsName "undefined" = "UNDEFINED"
jsName "String" = "STRING"
jsName n = concatMap (\c -> if c == '-' then "_" else if c == '\'' then "_p_" else [c]) n

addDecl :: JsStat -> Gen ()
addDecl d = modify (\s -> s {decls = s.decls ++ [d]})

addStdlibImports :: Gen ()
addStdlibImports = do
  addDecl $ jsConst "{ Buffer }" (JsExpr "require('node:buffer')")
  addDecl $ jsConst "prompt" (JsExpr "require('prompt-sync')()")

generateProgram :: Program -> Gen JsProg
generateProgram p@(Program items) = do
  modify (\s -> s {program = p})
  addStdlibImports
  mapM_ generateItem items
  addDecl $ jsExprStat (jsInvoke $ jsVar "main")
  ds <- gets (\s -> s.decls)
  return $ jsProgFromStats ds

generateItem :: Item -> Gen ()
generateItem (Data _) = return ()
generateItem (Repr _) = error "Found repr item in generateItem"
generateItem (Decl d) = generateDeclItem d
generateItem (Prim _) = return ()

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
generateExpr t@(Term (App {}) _) = do
  let (subject, args) = appToList t
  args' <- mapM (\(_, x) -> generateExpr x) args
  case subject.value of
    Meta _ -> do
      return jsNull
    Hole _ -> do
      return jsNull
    Wild -> do
      return jsNull
    Global g -> do
      generateGlobal g args'
    _ -> do
      a' <- generateExpr subject
      return $ foldl jsApp a' args'
generateExpr (Term (Global s) _) = generateGlobal s []
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
          let c'' = foldl (\acc x -> jsApp acc (jsIntIndex t' x)) caseBody [1 .. length args]
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

generateGlobal :: String -> [JsExpr] -> Gen JsExpr
generateGlobal name args = do
  sig <- gets (\s -> asSig s.program)
  case lookupItemOrCtor name sig of
    Just (Left (Decl d)) -> return $ foldl jsApp (jsVar (jsName d.name)) args
    Just (Left (Data _)) -> return jsNull
    Just (Left (Repr _)) -> return jsNull
    Just (Left (Prim p)) -> generatePrim p.name args
    Just (Right c) -> generateCtor c.name args
    Nothing -> error $ "Global not found: " ++ name

generateCtor :: String -> [JsExpr] -> Gen JsExpr
generateCtor name args = return $ jsArray (jsStringLit (jsName name) : args)

generatePrim :: String -> [JsExpr] -> Gen JsExpr
generatePrim "js-null" [] = return jsNull
generatePrim "js-undefined" [] = return jsUndefined
generatePrim "js-true" [] = return jsTrue
generatePrim "js-false" [] = return jsFalse
generatePrim "js-empty-array" [] = return jsEmptyArray
generatePrim "js-array-extend-l" [a, b] = return $ jsArrayExtendL a b
generatePrim "js-array-extend-r" [a, b] = return $ jsArrayExtendR a b
generatePrim "js-map" [f, xs] = return $ jsMap f xs
generatePrim "js-fold" [f, i, xs] = return $ jsFold f i xs
generatePrim "js-length" [a] = return $ jsLength a
generatePrim "js-slice" [a, b, c] = return $ jsSlice a b c
generatePrim "js-index" [a, b] = return $ jsIndex a b
generatePrim "js-zero" [] = return jsZero
generatePrim "js-one" [] = return jsOne
generatePrim "js-plus" [a, b] = return $ jsPlus a b
generatePrim "js-minus" [a, b] = return $ jsMinus a b
generatePrim "js-times" [a, b] = return $ jsTimes a b
generatePrim "js-div" [a, b] = return $ jsDiv a b
generatePrim "js-mod" [a, b] = return $ jsMod a b
generatePrim "js-pow" [a, b] = return $ jsPow a b
generatePrim "js-neg" [a] = return $ jsNeg a
generatePrim "js-eq" [a, b] = return $ jsEq a b
generatePrim "js-eqq" [a, b] = return $ jsEqq a b
generatePrim "js-neq" [a, b] = return $ jsNeq a b
generatePrim "js-neqq" [a, b] = return $ jsNeqq a b
generatePrim "js-lt" [a, b] = return $ jsLt a b
generatePrim "js-lte" [a, b] = return $ jsLte a b
generatePrim "js-gt" [a, b] = return $ jsGt a b
generatePrim "js-gte" [a, b] = return $ jsGte a b
generatePrim "js-and" [a, b] = return $ jsAnd a b
generatePrim "js-or" [a, b] = return $ jsOr a b
generatePrim "js-not" [a] = return $ jsNot a
generatePrim "js-typeof" [a] = return $ jsTypeof a
generatePrim "js-if" [_, c, l, r] = return $ jsCond c l r
generatePrim "cast" [_, _, x] = return x
generatePrim "IO" _ = return jsNull
generatePrim "JS" _ = return jsNull
generatePrim "io-return" [_, a] = return $ jsLazy a
generatePrim "io-bind" [_, _, a, f] = return $ jsLazy $ jsApp f (jsInvoke a)
generatePrim "js-console-log" [a] = return $ jsLazy $ jsAccess (jsVar "console") "log" `jsApp` a
generatePrim "js-prompt" [] = return $ jsLazy $ jsInvoke (jsVar "prompt")
generatePrim "to-js" [_, a] = return a
generatePrim "js-buffer-alloc" [a] = return $ jsApp (jsVar "Buffer.allocUnsafe") a
generatePrim "js-buffer-byte-length" [a] = return $ jsApp (jsVar "Buffer.byteLength") a
generatePrim "js-buffer-copy" [t, ts, te, s, ss, se] = return $ jsMultiApp (jsAccess s "copy") [t, ts, te, ss, se]
generatePrim "js-buffer-write-uint16-be" [b, v, o] = return $ jsMultiApp (jsAccess b "writeUInt32BE") [v, o]
generatePrim n _ = error $ "Unknown primitive: " ++ n

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

jsMultiApp :: JsExpr -> [JsExpr] -> JsExpr
jsMultiApp (JsExpr f) as = JsExpr $ "(" ++ f ++ ")" ++ "(" ++ intercalate ", " (map (\(JsExpr a) -> a) as) ++ ")"

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

jsEmptyArray :: JsExpr
jsEmptyArray = JsExpr "[]"

jsArrayExtendL :: JsExpr -> JsExpr -> JsExpr
jsArrayExtendL (JsExpr a) (JsExpr b) = JsExpr $ "[" ++ a ++ ", ...(" ++ b ++ ")]"

jsArrayExtendR :: JsExpr -> JsExpr -> JsExpr
jsArrayExtendR (JsExpr a) (JsExpr b) = JsExpr $ "[...(" ++ a ++ "), " ++ b ++ "]"

jsLength :: JsExpr -> JsExpr
jsLength (JsExpr a) = JsExpr $ "(" ++ a ++ ").length"

jsSlice :: JsExpr -> JsExpr -> JsExpr -> JsExpr
jsSlice (JsExpr a) (JsExpr b) (JsExpr c) = JsExpr $ "(" ++ a ++ ").slice(" ++ b ++ ", " ++ c ++ ")"

jsFold :: JsExpr -> JsExpr -> JsExpr -> JsExpr
jsFold (JsExpr f) (JsExpr i) (JsExpr a) = JsExpr $ "(" ++ a ++ ").reduce(" ++ f ++ ", " ++ i ++ ")"

jsMap :: JsExpr -> JsExpr -> JsExpr
jsMap (JsExpr f) (JsExpr a) = JsExpr $ "(" ++ a ++ ").map(" ++ f ++ ")"
