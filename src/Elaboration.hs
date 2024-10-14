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
    Name (..),
    PiMode (..),
    Qty (Many, Zero),
    Spine,
    Tel,
    mapSpine,
    unName,
    pattern Possible,
  )
import Control.Monad.Extra (when)
import Data.Bifunctor (bimap)
import Data.Semiring (Semiring (..))
import qualified Data.Sequence as S
import Globals (DataGlobalInfo (..), GlobalInfo (..), KnownGlobal (..), indexArity, knownCtor, knownData, lookupGlobal)
import Presyntax
  ( PCaseRep (..),
    PCtor (..),
    PCtorRep (..),
    PData (..),
    PDataRep (..),
    PDef (..),
    PDefRep (..),
    PItem (..),
    PPat,
    PPrim (..),
    PProgram (..),
    PTm (..),
    pApp,
    pGatherApps,
    pGatherPis,
    pLams,
    toPSpine,
  )
import Printing (Pretty (..))
import Syntax (STm (..), STy, VNorm (..), VTm (..), VTy)
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
    unrepr,
    wildPat,
  )

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
pKnownCtor k ts = pApp (PName (knownCtor k).globalName) (map (Arg Explicit Many) ts)

pKnownData :: KnownGlobal DataGlobal -> [PTm] -> PTm
pKnownData d ts = pApp (PName (knownData d).globalName) (map (Arg Explicit Many) ts)

patAsVar :: PPat -> Either Name PPat
patAsVar (PName n) = Left n
patAsVar PWild = Left (Name "_")
patAsVar (PLocated _ t) = patAsVar t
patAsVar p = Right p

elab :: (Elab m) => PTm -> Mode -> m (STm, VTy)
elab p mode = case (p, mode) of
  -- Check/both modes:
  (PLocated l t, md) -> enterLoc l (elab t md)
  (PLam m x t, md) -> do
    case patAsVar x of
      Left x' -> lam md m x' (elab t)
      Right p' -> do
        n <- uniqueName
        lam md m n (elab (PCase (PName n) Nothing [Possible p' t]))
  -- Lambda insertion
  (t, Check (VNorm (VPi Implicit q x' a b))) -> insertLam q x' a b (elab t)
  (PUnit, Check ty@(VNorm VU)) -> elab (pKnownData KnownUnit []) (Check ty)
  (PUnit, md) -> elab (pKnownCtor KnownTt []) md
  (PSigma _ x a _ b, md) -> elab (pKnownData KnownSigma [a, PLam Explicit (PName x) b]) md -- @@Todo: sigma
  (PPair t1 t2, md) -> elab (pKnownCtor KnownPair [t1, t2]) md
  (PLet q x a t u, md) -> do
    case patAsVar x of
      Left x' -> letIn md q x' (elab a) (elab t) (elab u)
      Right p' -> do
        n <- uniqueName
        letIn md q n (elab a) (elab t) (elab (PCase (PName n) Nothing [Possible p' u]))
  (PRepr t, md) -> repr md (elab t)
  (PUnrepr t, md) -> unrepr md (elab t)
  (PHole n, md) -> meta md (Just n)
  (PWild, md) -> ifInPat (wildPat md) (meta md Nothing)
  (PLambdaCase r cs, md) -> do
    n <- uniqueName
    elab (PLam Explicit (PName n) (PCase (PName n) r cs)) md
  (PCase s r cs, md) -> caseOf md (elab s) (fmap elab r) (map (bimap elab elab) cs)
  (PLit l, md) -> lit md (fmap elab l)
  (te, Check ty) -> checkByInfer (elab te Infer) ty
  -- Only infer:
  (PName x, Infer) -> name x
  (PApp {}, Infer) -> do
    let (s, sp) = toPSpine p
    app (elab s) (mapSpine elab sp)
  (PU, Infer) -> univ
  (PPi m q x a b, Infer) -> do
    -- If something ends in Type or equals, we use rig zero
    let potentiallyZero a' = case (q, fst . pGatherApps . snd . pGatherPis $ a') of
          (Many, PU) -> Zero
          (Many, PName (Name "Equal")) -> Zero
          (_, PLocated _ t) -> potentiallyZero t
          _ -> q
    let q' = potentiallyZero a `times` potentiallyZero b
    piTy m q' x (elab a) (elab b)
  (PList ts rest, md) -> do
    let end = case rest of
          Just t -> t
          Nothing -> pKnownCtor KnownNil []
    let ts' = foldr (\x xs -> pKnownCtor KnownCons [x, xs]) end ts
    elab ts' md
  (PIf cond a b, md) -> do
    caseOf
      md
      (elab cond)
      Nothing
      [ Possible (elab (pKnownCtor KnownTrue [])) (elab a),
        Possible (elab (pKnownCtor KnownFalse [])) (elab b)
      ]
  (PParams _ _, Infer) -> error "impossible"

elabDef :: (Elab m) => PDef -> m ()
elabDef def = defItem def.qty def.name def.tags (elab def.ty) (elab def.tm)

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
      Arg m q (PLocated l t) -> enterLoc l (argIsName (Arg m q t))
      Arg m q (PName an) -> return $ Arg m q an
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
      let target' = pLams sp r.target
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
      let target' = pLams sp r.target
      reprCtorItem te (CtorGlobal h) r.tags (elab target')
    _ -> elabError (ExpectedCtorGlobal h)

elabCaseRep :: (Elab m) => Tel STy -> DataGlobal -> DataGlobalInfo -> PCaseRep -> m ()
elabCaseRep te dat info r = do
  srcSubject <- Arg Explicit Many <$> ensurePatIsBind r.srcSubject
  srcBranches <- S.fromList . map (Arg Explicit Many) <$> mapM (ensurePatIsBind . snd) r.srcBranches
  ensurePatIsFullyApplied (length info.ctors) (length r.srcBranches)
  elimTy <- Arg Explicit Zero <$> maybe uniqueName ensurePatIsBind r.srcElim
  tyIndices <- mapM (traverse (const uniqueName)) info.indexArity
  let target' =
        pLams
          (S.singleton elimTy S.>< srcBranches S.>< tyIndices S.>< S.singleton srcSubject)
          r.target
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
