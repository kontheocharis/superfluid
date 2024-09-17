{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Elaboration
  ( Elab (..),
    elab,
    elabProgram,
    ElabError (..),
  )
where

import Common
  ( Arg (..),
    CtorGlobal (..),
    DataGlobal (..),
    DefGlobal (..),
    Has (..),
    HasNameSupply (uniqueName),
    HasProjectFiles,
    Loc,
    Name,
    PiMode (..),
    Spine,
    Times (..),
    mapSpine,
    unName, Tel,
  )
import Control.Monad (replicateM)
import Control.Monad.Extra (when)
import Data.Bifunctor (bimap)
import qualified Data.Sequence as S
import Debug.Trace (traceM)
import Globals (CtorGlobalInfo (..), DataGlobalInfo (..), GlobalInfo (..), KnownGlobal (..), indexArity, knownCtor, knownData, lookupGlobal)
import Presyntax
  ( PCaseRep (..),
    PCtor (..),
    PCtorRep (..),
    PData (..),
    PDataRep (..),
    PDef (..),
    PDefRep (..),
    PItem (..),
    PPrim (..),
    PProgram (..),
    PTm (..),
    pApp,
    pGatherApps,
    pLams,
    toPSpine,
  )
import Printing (Pretty (..))
import Syntax (STm (..), STy)
import Typechecking
  ( Mode (..),
    Tc (..),
    app,
    caseOf,
    checkByInfer,
    ctorItem,
    dataItem,
    defItem,
    endDataItem,
    ensureAllProblemsSolved,
    enterTel,
    insertLam,
    lam,
    letIn,
    lit,
    meta,
    name,
    piTy,
    primItem,
    repr,
    reprCaseItem,
    reprCtorItem,
    reprDataItem,
    reprDefItem,
    univ,
    wildPat,
  )
import Value (VTm (..), VTy)

-- Presyntax exists below here

data ElabError
  = PatMustBeBind PTm
  | PatMustBeHeadWithBinds PTm
  | ExpectedDataGlobal Name
  | ExpectedCtorGlobal Name
  | PatMustBeFullyApplied Int Int
  deriving (Show)

instance (Tc m, HasProjectFiles m) => Pretty m ElabError where
  pretty e = do
    loc <- (view :: m Loc) >>= pretty
    err' <- err
    return $ loc <> "\n" <> err'
    where
      err = case e of
        PatMustBeHeadWithBinds a' -> do
          e' <- pretty a'
          return $ "Pattern must be a head with binds, but got:" ++ e'
        ExpectedDataGlobal n ->
          return $ "Expected a data type name, but got: `" ++ n.unName ++ "`"
        ExpectedCtorGlobal n ->
          return $ "Expected a constructor name, but got: `" ++ n.unName ++ "`"
        PatMustBeBind a' -> do
          e' <- pretty a'
          return $ "Pattern must be a bind, but got: " ++ e'
        PatMustBeFullyApplied n n' ->
          return $ "Pattern must be fully applied, but got " ++ show n' ++ " arguments instead of " ++ show n

class (Tc m) => Elab m where
  elabError :: ElabError -> m a

pKnownCtor :: KnownGlobal CtorGlobal -> [PTm] -> PTm
pKnownCtor k ts = pApp (PName (knownCtor k).globalName) (map (Arg Explicit) ts)

pKnownData :: KnownGlobal DataGlobal -> [PTm] -> PTm
pKnownData d ts = pApp (PName (knownData d).globalName) (map (Arg Explicit) ts)

elab :: (Elab m) => PTm -> Mode -> m (STm, VTy)
elab p mode = case (p, mode) of
  -- Check/both modes:
  (PLocated l t, md) -> enterLoc l (elab t md)
  (PLam m x t, md) -> lam md m x (elab t)
  -- Lambda insertion
  (t, Check (VPi Implicit x' a b)) -> insertLam x' a b (elab t)
  (PUnit, Check ty@VU) -> elab (pKnownData KnownUnit []) (Check ty)
  (PUnit, md) -> elab (pKnownCtor KnownTt []) md
  (PSigma x a b, md) -> elab (pKnownData KnownSigma [a, PLam Explicit x b]) md
  (PPair t1 t2, md) -> elab (pKnownCtor KnownPair [t1, t2]) md
  (PLet x a t u, md) -> letIn md x (elab a) (elab t) (elab u)
  (PRepr m t, md) -> repr md m (elab t)
  (PHole n, md) -> meta md (Just n)
  (PWild, md) -> ifInPat (wildPat md) (meta md Nothing)
  (PLambdaCase r cs, md) -> do
    n <- uniqueName
    elab (PLam Explicit n (PCase (PName n) r cs)) md
  (PCase s r cs, md) -> caseOf md (elab s) (fmap elab r) (map (bimap elab elab) cs)
  (PLit l, md) -> lit md (fmap elab l)
  (te, Check ty) -> checkByInfer (elab te Infer) ty
  -- Only infer:
  (PName x, Infer) -> name x
  (PApp {}, Infer) -> do
    let (s, sp) = toPSpine p
    app (elab s) (mapSpine elab sp)
  (PU, Infer) -> univ
  (PPi m x a b, Infer) -> piTy m x (elab a) (elab b)
  (PParams _ _, Infer) -> error "impossible"

elabDef :: (Elab m) => PDef -> m ()
elabDef def = defItem def.name def.tags (elab def.ty) (elab def.tm)

elabCtor :: (Elab m) => DataGlobal -> PCtor -> m ()
elabCtor dat ctor = ctorItem dat ctor.name ctor.tags (elab ctor.ty)

elabData :: (Elab m) => PData -> m ()
elabData dat = do
  dataItem dat.name dat.tags (fmap (fmap elab) dat.params) (elab dat.ty)
  let d = DataGlobal dat.name
  mapM_ (elabCtor d) dat.ctors
  endDataItem d

elabPrim :: (Elab m) => PPrim -> m ()
elabPrim prim = primItem prim.name prim.tags (elab prim.ty)

ensurePatIsHeadWithBinds :: (Elab m) => PTm -> m (Name, Spine Name)
ensurePatIsHeadWithBinds p =
  let (h, sp) = pGatherApps p
   in case h of
        PLocated l t -> enterLoc l (ensurePatIsHeadWithBinds t)
        PName n -> (n,) <$> mapM argIsName sp
        _ -> elabError (PatMustBeHeadWithBinds p)
  where
    argIsName = \case
      Arg m (PLocated l t) -> enterLoc l (argIsName (Arg m t))
      Arg m (PName an) -> return $ Arg m an
      _ -> elabError (PatMustBeHeadWithBinds p)

ensurePatIsBind :: (Elab m) => PTm -> m Name
ensurePatIsBind p = case p of
  PLocated l t -> enterLoc l (ensurePatIsBind t)
  PName n -> return n
  _ -> elabError (PatMustBeBind p)

ensurePatIsFullyApplied :: (Elab m) => Int -> Int -> m ()
ensurePatIsFullyApplied n n' = do
  when (n' /= n) $ elabError (PatMustBeFullyApplied n n')

elabDataRep :: (Elab m) => PDataRep -> m ()
elabDataRep r = do
  (h, sp) <- ensurePatIsHeadWithBinds r.src
  g <- access (lookupGlobal h)
  case g of
    Just (DataInfo info) -> do
      let target' = pLams sp (PRepr (Finite (-1)) r.target)
      let dat = DataGlobal h
      te <- reprDataItem dat r.tags (elab target')
      mapM_ (elabCtorRep te) r.ctors
      elabCaseRep te dat info r.caseExpr
    _ -> elabError (ExpectedDataGlobal h)

elabCtorRep :: (Elab m) => Tel STy -> PCtorRep -> m ()
elabCtorRep te r = do
  (h, sp) <- ensurePatIsHeadWithBinds r.src
  g <- access (lookupGlobal h)
  case g of
    Just (CtorInfo _) -> do
      let target' = pLams sp (PRepr (Finite (-1)) r.target)
      reprCtorItem te (CtorGlobal h) r.tags (elab target')
    _ -> elabError (ExpectedCtorGlobal h)

elabCaseRep :: (Elab m) => Tel STy -> DataGlobal -> DataGlobalInfo -> PCaseRep -> m ()
elabCaseRep te dat info r = do
  srcSubject <- Arg Explicit <$> ensurePatIsBind r.srcSubject
  srcBranches <- S.fromList . map (Arg Explicit) <$> mapM (ensurePatIsBind . snd) r.srcBranches
  ensurePatIsFullyApplied (length info.ctors) (length r.srcBranches)
  elimTy <- Arg Explicit <$> maybe uniqueName ensurePatIsBind r.srcElim
  tyIndices <- mapM (traverse (const uniqueName)) info.indexArity
  let target' =
        pLams
          (S.singleton elimTy S.>< srcBranches S.>< tyIndices S.>< S.singleton srcSubject)
          (PRepr (Finite (-1)) r.target)
  reprCaseItem te dat r.tags (elab target')

elabDefRep :: (Elab m) => PDefRep -> m ()
elabDefRep r = do
  x <- ensurePatIsBind r.src
  g <- access (lookupGlobal x)
  case g of
    Just (DefInfo _) -> reprDefItem (DefGlobal x) r.tags (elab r.target)
    _ -> elabError (ExpectedDataGlobal x)

elabItem :: (Elab m) => PItem -> m ()
elabItem i = do
  case i of
    PDef def -> elabDef def
    PData dat -> elabData dat
    PPrim prim -> elabPrim prim
    PDataRep dataRep -> elabDataRep dataRep
    PDefRep defRep -> elabDefRep defRep
    PLocatedItem l i' -> enterLoc l $ elabItem i'
  ensureAllProblemsSolved

elabProgram :: (Elab m) => PProgram -> m ()
elabProgram (PProgram items) = mapM_ elabItem items
