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
    Logger (warnMsg),
    Name (Name),
    Param (..),
    PiMode (Explicit),
    PrimGlobal (..),
    Qty (..),
    Spine,
    Tel,
    mapSpineM,
    spineValues,
    unName,
    uniqueTel,
    pattern Possible,
  )
import Control.Monad.Extra (when)
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as S
import Evaluation (Eval)
import Globals
  ( CtorConstructions (..),
    CtorGlobalInfo (..),
    DataConstructions (..),
    DataGlobalInfo (..),
    DefGlobalInfo (..),
    GlobalInfo (..),
    dataIsIrrelevant,
    getCtorGlobal,
    getDataGlobal,
    mapSigContentsM_,
  )
import Printing (indentedFst)
import Syntax (Case (..), SCase, SPat (..), STm (..), sGatherApps, sGatherLets)

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
jsName (Name "return") = "RETURN"
jsName (Name "class") = "CLASS"
jsName (Name "function") = "FUNCTION"
jsName (Name "const") = "CONST"
jsName (Name "let") = "LET"
jsName (Name "constructor") = "CONSTRUCTOR"
jsName (Name "new") = "NEW"
jsName (Name "String") = "STRING"
jsName (Name "void") = "VOID"
jsName (Name "for") = "FOR"
jsName (Name "while") = "WHILE"
jsName (Name "if") = "IF"
jsName (Name "switch") = "SWITCH"
jsName (Name "throw") = "THROW"
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
    Zero -> return $ JsExpr b'
    _ -> return . JsExpr $ "(" ++ v' ++ ") => " ++ b'

jsLams :: (Gen m) => Tel a -> m JsExpr -> m JsExpr
jsLams vs b = foldr (\t -> jsLam t.name t.qty) b (toList vs)

jsLet :: (Gen m) => Name -> Qty -> m JsExpr -> m [JsStat] -> m [JsStat]
jsLet v q t ts = do
  v' <- jsNewBind v
  t' <- t
  ts' <- enter (Name v' :) ts
  case q of
    Zero -> return ts'
    _ -> return $ jsConst v' t' : ts'

addDecl :: (Gen m) => JsStat -> m ()
addDecl d = modify (++ [d])

generateProgram :: (Gen m) => m JsProg
generateProgram = do
  view >>= mapSigContentsM_ generateItem
  boot <- readBootFile
  addDecl $ jsExprStat (jsApp (jsGlobal (Name "main")) (S.singleton $ Arg Explicit Many jsId))
  ds <- view
  return $ jsProgFromStats boot ds

generateItem :: (Gen m) => GlobalInfo -> m ()
-- generateItem (DataInfo d) = generateDataItem d
generateItem (DataInfo _) = return ()
generateItem (CtorInfo _) = return ()
generateItem (PrimInfo {}) = return () -- should be handled by the boot file
generateItem (DefInfo d) = when (d.qty > Zero) $ generateDeclItem d

onlyRelevantArgs :: Spine a -> Spine a
onlyRelevantArgs = S.filter (\ar -> ar.qty /= Zero)

onlyRelevantBinds :: [(Qty, Name)] -> [(Qty, Name)]
onlyRelevantBinds = filter (\(q, _) -> q /= Zero)

onlyRelevantParams :: Tel a -> Tel a
onlyRelevantParams = S.filter (\ar -> ar.qty /= Zero)

generateDeclItem :: (Gen m) => DefGlobalInfo -> m ()
generateDeclItem d = do
  t <- generateExpr (fromJust d.tm)
  addDecl $ jsConst (jsName d.name) t

jsLamsForTel :: (Gen m) => Tel a -> Spine JsExpr -> ([JsExpr] -> m JsExpr) -> m JsExpr
jsLamsForTel ns sp f = do
  jsLams (S.drop (length sp) ns) $ do
    sp2 <- mapM (jsVar . Idx) [length sp .. length ns - 1]
    f (spineValues sp ++ sp2)

generateData :: (Gen m) => DataGlobal -> Spine JsExpr -> m JsExpr
generateData d sp = do
  di <- access (getDataGlobal d)
  let dc = fromJust di.constructions
  indices <- uniqueTel (onlyRelevantParams dc.indicesArity)
  params <- uniqueTel (onlyRelevantParams dc.paramsArity)
  jsLamsForTel (params S.>< indices) sp $ \_ -> return jsNull

generateCtor :: (Gen m) => CtorGlobal -> Spine JsExpr -> m JsExpr
generateCtor c sp = do
  ci <- access (getCtorGlobal c)
  let cc = fromJust ci.constructions
  di <- access (getDataGlobal ci.dataGlobal)
  ns <- uniqueTel $ onlyRelevantParams cc.argsArity
  jsLamsForTel ns sp $ \ps -> do
    let args = [jsStringLit ci.name.unName | length di.ctors > 1] ++ ps
    case args of
      [a] | length di.ctors == 1 -> return a
      _ -> return $ jsArray args

generateCase :: (Gen m) => SCase -> m JsExpr
generateCase c = do
  di <- access (getDataGlobal c.dat)
  irr <- access (dataIsIrrelevant c.dat)
  if irr
    then case c.clauses of
      [] -> return jsNull -- @@Enhancement: emit a `throw new Error("unreachable")` here
      [Possible _ t] -> generateExpr t
      _ -> error "Found irrelevant data with more than one case"
    else do
      sub' <- generateExpr c.subject
      subName <- jsNewBind (Name "subject")
      let sub = JsExpr subName
      let letSub = jsConst subName sub'
      cs' <-
        mapM
          ( \cl -> do
              (ci, p, t) <- case cl of
                Possible p b -> case fst (sGatherApps p.asTm) of
                  SCtor (ct, _) -> (,p,b) <$> access (getCtorGlobal ct)
                  _ -> error "Case not supported"
                _ -> error "Case not supported"
              let relevantBinds = onlyRelevantBinds p.binds
              ls <- jsLams (S.fromList $ map (\(q, n) -> Param Explicit q n ()) relevantBinds) $ generateExpr t
              let tag = jsStringLit ci.name.unName
              let offset = if length di.ctors <= 1 then 0 else 1

              let clauseArgs =
                    if length relevantBinds == 1 && length c.clauses == 1
                      then S.singleton $ Arg Explicit Many sub
                      else
                        S.fromList $
                          map
                            (Arg Explicit Many . jsIndex sub . intToNat . (+ offset))
                            [0 .. length relevantBinds - 1]

              let body = jsApp ls clauseArgs
              return (tag, body)
          )
          c.clauses
      let subTag = jsIndex sub (intToNat 0)
      return $ jsBlockExpr [letSub, jsReturn (jsSwitch subTag cs')]

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
  args' <- mapSpineM generateExpr (onlyRelevantArgs args)
  case subject of
    SCtor (c, _) -> generateCtor c args'
    SData d -> generateData d args'
    _ -> do
      a <- generateExpr subject
      return $ jsApp a args'
generateExpr (SPrim s) = return $ jsGlobal s.globalName
generateExpr (SCtor (s, _)) = generateCtor s Empty
generateExpr (SData s) = generateData s Empty
generateExpr (SDef s) = return $ jsGlobal s.globalName
generateExpr (SVar v) = jsVar v
generateExpr (SCase c) = generateCase c
generateExpr ((SMeta _ _)) = warnMsg "Found meta in generateExpr" >> return jsNull
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
jsSwitch (JsExpr _) [(JsExpr _, s)] = s
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

jsId :: JsExpr
jsId = JsExpr "(x) => x"

jsArray :: [JsExpr] -> JsExpr
jsArray es = JsExpr $ "[" ++ intercalate ", " (map (\(JsExpr e) -> e) es) ++ "]"
