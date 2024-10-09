{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Codegen (Gen (..), generateProgram, renderJsProg, JsStat) where

import Common
  ( Arg (..),
    CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (..),
    Has (..),
    HasNameSupply (uniqueName),
    Idx (..),
    Lit (CharLit, FinLit, NatLit, StringLit),
    Name (Name),
    PiMode (Explicit),
    Param (..),
    PrimGlobal (..),
    Spine,
    mapSpineM,
    pattern Impossible,
    pattern Possible, Qty (..), Tel, mapSpine,
  )
import Control.Monad (zipWithM)
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation (Eval)
import Globals
  ( CtorGlobalInfo (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    mapSigContentsM_,
  )
import Printing (indentedFst)
import Syntax (Case (..), SPat (..), STm (..), sGatherApps, sGatherLets)
import Control.Monad.Extra (when)

newtype JsStat = JsStat String

newtype JsExpr = JsExpr String

newtype JsProg = JsProg String

class (Eval m, Has m [JsStat], Has m [Name]) => Gen m where
  readBootFile :: m String

renderJsProg :: JsProg -> String
renderJsProg (JsProg s) = s

jsProgFromStats :: String -> [JsStat] -> JsProg
jsProgFromStats boot stats = JsProg $ boot ++ "\n" ++ intercalate "\n" (map (\(JsStat s) -> s) stats)

jsConst :: String -> JsExpr -> JsStat
jsConst name (JsExpr e) = JsStat $ "var " ++ name ++ " = " ++ e ++ ";"

jsExprStat :: JsExpr -> JsStat
jsExprStat (JsExpr e) = JsStat e

jsIndex :: JsExpr -> JsExpr -> JsExpr
jsIndex (JsExpr e) (JsExpr i) = JsExpr $ "(" ++ e ++ ")" ++ "[" ++ i ++ "]"

jsName :: Name -> String
jsName (Name "false") = "FALSE"
jsName (Name "true") = "TRUE"
jsName (Name "null") = "NULL"
jsName (Name "undefined") = "UNDEFINED"
jsName (Name "String") = "STRING"
jsName (Name "void") = "VOID"
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

jsLam :: (Gen m) => Name -> Qty -> m JsExpr -> m JsExpr
jsLam v q b = do
  v' <- jsNewBind v
  JsExpr b' <- enter (Name v' :) b
  case q of
    Many -> return . JsExpr $ "(" ++ v' ++ ") => " ++ b'
    Zero -> return $ JsExpr b'

jsLams :: (Gen m) => Spine Name -> m JsExpr -> m JsExpr
jsLams vs b = foldr (\t -> jsLam t.arg t.qty) b (toList vs)

jsLet :: (Gen m) => Name -> Qty -> m JsExpr -> m [JsStat] -> m [JsStat]
jsLet v q t ts = do
  v' <- jsNewBind v
  t' <- t
  ts' <- enter (Name v' :) ts
  case q of
    Many -> return $ jsConst v' t' : ts'
    Zero -> return ts'

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
generateItem (DataInfo d) = generateDataItem d
generateItem (CtorInfo c) = generateCtorItem c
generateItem (PrimInfo {}) = return () -- should be handled by the boot file
generateItem (DefInfo d) = when (d.qty > Zero) $ generateDeclItem d

generateDeclItem :: (Gen m) => DefGlobalInfo -> m ()
generateDeclItem d = do
  t <- generateExpr (fromJust d.tm)
  addDecl $ jsConst (jsName d.name) t

generateDataItem :: (Gen m) => DataGlobalInfo -> m ()
generateDataItem d = do
  indices <- mapSpineM (const uniqueName) d.indexArity
  let params = fmap (\s -> Arg s.mode s.qty s.name) d.params
  body <- jsLams (params S.>< indices) $ return jsNull
  addDecl $ jsConst (jsName d.name) body

generateCtorItem :: (Gen m) => CtorGlobalInfo -> m ()
generateCtorItem c = do
  let total = length c.argArity
  ns <- mapSpineM (const uniqueName) c.argArity
  body <- jsLams ns $ do
    ns' <- mapM (jsVar . Idx) (reverse [0 .. total - 1])
    return $ jsArray (intToNat c.idx : ns')
  addDecl $ jsConst (jsName c.name) body

generateLets :: (Gen m) => [(Qty, Name, STm, STm)] -> STm -> m [JsStat]
generateLets ((q, n, _, t) : ts) ret = jsLet n q (generateExpr t) (generateLets ts ret)
generateLets [] ret = do
  ret' <- generateExpr ret
  return [jsReturn ret']

generateExpr :: (Gen m) => STm -> m JsExpr
generateExpr (SPi {}) = return jsNull
generateExpr SU = return jsNull
generateExpr (SLam _ q v t) = jsLam v q $ generateExpr t
generateExpr ls@(SLet {}) = do
  let (xs, ret) = sGatherLets ls
  statements <- generateLets xs ret
  return $ jsBlockExpr statements
generateExpr t@((SApp {})) = do
  let (subject, args) = sGatherApps t
  a <- generateExpr subject
  args' <- mapSpineM generateExpr (S.filter (\ar -> ar.qty /= Zero) args)
  return $ jsApp a args'
generateExpr (SPrim s) = return $ jsGlobal s.globalName
generateExpr (SCtor (s, _)) = return $ jsGlobal s.globalName
generateExpr (SData s) = return $ jsGlobal s.globalName
generateExpr (SDef s) = return $ jsGlobal s.globalName
generateExpr (SVar v) = jsVar v
generateExpr (SCase c) = do
  sub <- generateExpr c.subject
  cs' <-
    zipWithM
      ( \i cl -> do
          let (p, t) = case cl of
                Possible a b -> (a, b)
                Impossible _ -> error "Impossible case not supported"
          ls <- jsLams (S.fromList $ map (uncurry $ Arg Explicit) p.binds) $ generateExpr t
          let tag = intToNat i
          let body =
                jsApp
                  ls
                  ( S.fromList $
                      map
                        (Arg Explicit Many . jsIndex sub . intToNat)
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
generateExpr ((SRepr _)) = error "Found repr in generateExpr"
generateExpr ((SUnrepr _)) = error "Found unrepr in generateExpr"

intToNat :: Int -> JsExpr
intToNat = JsExpr . show

jsNull :: JsExpr
jsNull = JsExpr "null"

jsReturn :: JsExpr -> JsStat
jsReturn (JsExpr e) = JsStat $ "return " ++ e ++ ";"

jsApp :: JsExpr -> Spine JsExpr -> JsExpr
jsApp e Empty = e
jsApp (JsExpr f) as = JsExpr $ "(" ++ f ++ ")" ++ "(" ++ intercalate ")(" (map (\(Arg _ _ (JsExpr a)) -> a) (toList as)) ++ ")"

jsBlockExpr :: [JsStat] -> JsExpr
jsBlockExpr ss = JsExpr $ "(() => {\n" ++ indentedFst (intercalate "\n" (map (\(JsStat s) -> s) ss)) ++ "\n})()"

jsStringLit :: String -> JsExpr
jsStringLit s = JsExpr $ "\"" ++ s ++ "\""

jsIntLit :: Integer -> JsExpr
jsIntLit i = JsExpr $ show i

jsCharLit :: Char -> JsExpr
jsCharLit c = JsExpr $ show c

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

jsInvoke :: JsExpr -> JsExpr
jsInvoke (JsExpr e) = JsExpr $ "(" ++ e ++ ")()"

jsArray :: [JsExpr] -> JsExpr
jsArray es = JsExpr $ "[" ++ intercalate ", " (map (\(JsExpr e) -> e) es) ++ "]"
