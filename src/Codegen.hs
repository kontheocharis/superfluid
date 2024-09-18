{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Codegen (Gen (..), generateProgram) where

import Common
  ( Arg (..),
    Has (..),
    Idx (..),
    Lit (..),
    Name (..),
    PiMode (..),
    PrimGlobal (globalName),
    Spine,
    globName,
    mapSpineM,
    pattern Impossible,
    pattern Possible,
  )
import Control.Monad (zipWithM)
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Maybe (fromJust)
import qualified Data.Sequence as S
import Evaluation (Eval)
import Globals
  ( DefGlobalInfo (name, tm),
    GlobalInfo (..),
    KnownGlobal,
    knownPrim,
    mapSigContentsM_,
  )
import Printing (indentedFst)
import Syntax (Case (..), SPat (..), STm (..), sGatherApps, sGatherLets)

newtype JsStat = JsStat String

newtype JsExpr = JsExpr String

newtype JsProg = JsProg String

class (Eval m, Has m [JsStat], Has m [Name]) => Gen m where
  readBootFile :: m String

renderJsProg :: JsProg -> String
renderJsProg (JsProg s) = s

jsProgFromStats :: String -> [JsStat] -> JsProg
jsProgFromStats boot stats = JsProg $ boot ++ "\n" ++ intercalate "\n" ( map (\(JsStat s) -> s) stats)

jsConst :: String -> JsExpr -> JsStat
jsConst name (JsExpr e) = JsStat $ "var " ++ name ++ " = " ++ e ++ ";"

jsExprStat :: JsExpr -> JsStat
jsExprStat (JsExpr e) = JsStat e

jsAccess :: JsExpr -> String -> JsExpr
jsAccess (JsExpr e) s = JsExpr $ "(" ++ e ++ ")" ++ "." ++ s

jsIndex :: JsExpr -> JsExpr -> JsExpr
jsIndex (JsExpr e) (JsExpr i) = JsExpr $ "(" ++ e ++ ")" ++ "[" ++ i ++ "]"

jsName :: Name -> String
jsName (Name "false") = "FALSE"
jsName (Name "true") = "TRUE"
jsName (Name "null") = "NULL"
jsName (Name "undefined") = "UNDEFINED"
jsName (Name "String") = "STRING"
jsName (Name n) = concatMap (\c -> if c == '-' then "_" else if c == '\'' then "_p_" else [c]) n

jsGlobal :: Name -> JsExpr
jsGlobal s = JsExpr $ jsName s

jsVar :: (Gen m) => Idx -> m JsExpr
jsVar i = do
  n <- access (!! i.unIdx)
  return . JsExpr $ jsName n

jsNewBind :: (Gen m) => Name -> m String
jsNewBind v = do
  l <- access (\(n :: [Name]) -> length n)
  return $ jsName v ++ show l

jsLam :: (Gen m) => Name -> m JsExpr -> m JsExpr
jsLam v b = do
  v' <- jsNewBind v
  JsExpr b' <- enter (Name v' :) b
  return . JsExpr $ "(" ++ v' ++ ") => " ++ b'

jsLams :: (Gen m) => [Name] -> m JsExpr -> m JsExpr
jsLams vs b = foldr jsLam b vs

jsLet :: (Gen m) => Name -> m JsExpr -> m [JsStat] -> m [JsStat]
jsLet v t ts = do
  v' <- jsNewBind v
  t' <- t
  ts' <- enter (Name v' :) ts
  return $ jsConst v' t' : ts'

addDecl :: (Gen m) => JsStat -> m ()
addDecl d = modify (++ [d])

generateProgram :: (Gen m) => m JsProg
generateProgram = do
  view >>= mapSigContentsM_ generateItem
  boot <- readBootFile
  addDecl $ jsExprStat (jsInvoke $ jsGlobal (Name "main"))
  ds <- view
  return $ jsProgFromStats boot ds

generateItem :: (Gen m) => GlobalInfo -> m ()
generateItem (DataInfo {}) = return ()
generateItem (CtorInfo {}) = return ()
generateItem (PrimInfo {}) = return ()
generateItem (DefInfo d) = generateDeclItem d

generateDeclItem :: (Gen m) => DefGlobalInfo -> m ()
generateDeclItem d = do
  t <- generateExpr (fromJust d.tm)
  addDecl $ jsConst (jsName d.name) t

generateLets :: (Gen m) => [(Name, STm, STm)] -> STm -> m [JsStat]
generateLets ((n, _, t) : ts) ret = jsLet n (generateExpr t) (generateLets ts ret)
generateLets [] ret = do
  ret' <- generateExpr ret
  return [jsReturn ret']

generateExpr :: (Gen m) => STm -> m JsExpr
generateExpr (SPi {}) = return jsNull
generateExpr SU = return jsNull
generateExpr (SLam _ v t) = jsLam v $ generateExpr t
generateExpr ls@(SLet {}) = do
  let (xs, ret) = sGatherLets ls
  statements <- generateLets xs ret
  return $ jsBlockExpr statements
generateExpr t@((SApp {})) = do
  let (subject, args) = sGatherApps t
  a <- generateExpr subject
  args' <- mapSpineM generateExpr args
  return $ jsApp a args'
generateExpr (SGlobal s _) = return $ jsGlobal (globName s)
generateExpr (SVar v) = jsVar v
generateExpr (SCase c) = do
  sub <- generateExpr c.subject
  cs' <-
    zipWithM
      ( \i cl -> do
          let (p, t) = case cl of
                Possible a b -> (a, b)
                Impossible _ -> error "Impossible case not supported"
          ls <- jsLams p.binds $ generateExpr t
          let tag = intToNat i
          let body =
                jsApp
                  ls
                  ( S.fromList $
                      map
                        (Arg Explicit . jsIndex sub . intToNat)
                        [1 .. length p.binds]
                  )
          return (tag, body)
      )
      [0 ..]
      c.clauses
  let subTag = jsIndex sub (intToNat 0)
  return $ jsSwitch subTag cs'
generateExpr ((SMeta _ _)) = return jsNull
generateExpr ((SLit (StringLit s))) = return $ jsStringLit s
generateExpr ((SLit (NatLit i))) = return $ jsIntLit (fromIntegral i)
generateExpr ((SLit (FinLit i _))) = return $ jsIntLit (fromIntegral i)
generateExpr ((SLit (CharLit c))) = return $ jsCharLit c
generateExpr ((SRepr _ _)) = error "Found rep in generateExpr"

intToNat :: Int -> JsExpr
intToNat = JsExpr . show

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

jsLazy :: JsExpr -> JsExpr
jsLazy (JsExpr e) = JsExpr $ "(() => " ++ e ++ ")"

jsReturn :: JsExpr -> JsStat
jsReturn (JsExpr e) = JsStat $ "return " ++ e ++ ";"

jsApp :: JsExpr -> Spine JsExpr -> JsExpr
jsApp (JsExpr f) as = JsExpr $ "(" ++ f ++ ")" ++ "(" ++ intercalate ", " (map (\(Arg _ (JsExpr a)) -> a) (toList as)) ++ ")"

jsMultiApp :: JsExpr -> [JsExpr] -> JsExpr
jsMultiApp (JsExpr f) as = JsExpr $ "(" ++ f ++ ")" ++ "(" ++ intercalate ", " (map (\(JsExpr a) -> a) as) ++ ")"

jsBlockExpr :: [JsStat] -> JsExpr
jsBlockExpr ss = JsExpr $ "(() => {\n" ++ indentedFst (intercalate "\n" (map (\(JsStat s) -> s) ss)) ++ "\n})()"

jsCommaExpr :: [JsExpr] -> JsExpr
jsCommaExpr ss = JsExpr $ "(" ++ intercalate ", " (map (\(JsExpr s) -> s) ss) ++ ")"

jsStringLit :: String -> JsExpr
jsStringLit s = JsExpr $ "\"" ++ s ++ "\""

jsIntLit :: Integer -> JsExpr
jsIntLit i = JsExpr $ show i

jsCharLit :: Char -> JsExpr
jsCharLit c = JsExpr $ show c

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
