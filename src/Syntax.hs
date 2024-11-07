{-# LANGUAGE PatternSynonyms #-}

module Syntax
  ( STm (..),
    STy,
    VHead (..),
    SPat (..),
    BoundState (..),
    Bounds,
    sAppSpine,
    sLams,
    sPis,
    Case (..),
    sGatherApps,
    sGatherPis,
    sGatherLams,
    sGlobWithParams,
    uniqueSLams,
    sGatherLets,
    VPat,
    VPatB (..),
    VTy,
    Env,
    Closure (..),
    VNeu,
    VTm (..),
    VLazy,
    mapHeadM,
    vGatherApps,
    headAsValue,
    sReprTimes,
    VNeuHead (..),
    VLazyHead (..),
    VNorm (..),
    WTm (..),
    PRen (..),
    Sub (..),
    VLazyCase,
    VBlockedCase,
    SCase,
    mapClosureM,
    weakAsValue,
    subbing,
    liftPRen,
    liftPRenN,
    isEmptySub,
    vGetSpine,
    pattern VVar,
    pattern VMeta,
    HTm (..),
    pv,
    HTy,
    HCase,
    embed,
    unembed,
  )
where

import Common
  ( Arg (..),
    Clause (..),
    CtorGlobal,
    DataGlobal,
    DefGlobal,
    Glob (..),
    HasNameSupply (uniqueName),
    Idx (..),
    Lit,
    Lvl (..),
    MetaVar,
    Name,
    Param (..),
    PiMode,
    PrimGlobal,
    Qty,
    Spine,
    Tel,
    idxToLvl,
    lvlToIdx,
    members,
    membersIn,
    nextLvl,
    unLvl,
  )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Sequence (Seq (..), fromList)

data Sub = Sub {lvl :: Lvl, vars :: IntMap (NonEmpty VTm)} deriving (Show)

isEmptySub :: Sub -> Bool
isEmptySub s = IM.null s.vars

emptySub :: Sub
emptySub = Sub (Lvl 0) IM.empty

subbing :: Lvl -> Lvl -> VTm -> Sub
subbing l x v = Sub l (IM.singleton x.unLvl (NE.singleton v))

instance Semigroup Sub where
  Sub l1 v1 <> Sub l2 v2 = Sub (max l1 l2) (IM.unionWith (<>) v1 v2)

instance Monoid Sub where
  mempty = emptySub

data PRen = PRen
  { domSize :: Lvl,
    codSize :: Lvl,
    vars :: IntMap (Lvl, Qty)
  }
  deriving (Show)

liftPRen :: Qty -> PRen -> PRen
liftPRen q (PRen dom cod ren) = PRen (Lvl (dom.unLvl + 1)) (Lvl (cod.unLvl + 1)) (IM.insert cod.unLvl (dom, q) ren)

liftPRenN :: [Qty] -> PRen -> PRen
liftPRenN qs ren = foldl (flip liftPRen) ren qs

type VPat = VTm

data VPatB = VPatB {vPat :: VPat, binds :: [(Qty, Name)]} deriving (Show)

type VTy = VTm

type Env v = [v]

data Closure = Closure {numVars :: Int, env :: Env VTm, body :: STm} deriving (Show)

mapClosureM :: (Monad m) => (STm -> m STm) -> Closure -> m Closure
mapClosureM f (Closure n env t) = Closure n env <$> f t

data Case s t p c = Case
  { dat :: DataGlobal,
    datParams :: Spine t,
    subject :: s,
    subjectIndices :: Spine t,
    elimTy :: t,
    clauses :: [Clause p c]
  }
  deriving (Show)

type SCase = Case STm STm SPat STm

type VSpined t = (t, Spine VTm)

type VNeu = VSpined VNeuHead

type VLazy = VSpined VLazyHead

type VData = VSpined DataGlobal

type VCtor = VSpined (CtorGlobal, Spine VTm)

type VLazyCase = Case VLazy VTm VPatB Closure

type VBlockedCase = Case VNeu VTm VPatB Closure

data VNeuHead
  = VFlex MetaVar
  | VRigid Lvl
  | VBlockedCase VBlockedCase
  | VPrim PrimGlobal
  | VUnrepr VHead
  deriving (Show)

data VLazyHead
  = VDef DefGlobal
  | VLit (Lit VTm)
  | VLazyCase VLazyCase
  | VLet Qty Name VTy VTm Closure
  | VRepr VHead
  deriving (Show)

data VHead
  = VNeuHead VNeuHead
  | VLazyHead VLazyHead
  | VDataHead DataGlobal
  | VCtorHead (CtorGlobal, Spine VTm)
  deriving (Show)

mapHeadM :: (Monad m) => (VTm -> m VTm) -> VHead -> m VHead
mapHeadM f h = do
  h' <- f (headAsValue h)
  case vGatherApps h' of
    Just (h'', Empty) -> return h''
    _ -> error "mapHeadM: got non-head value"

vGatherApps :: VTm -> Maybe (VSpined VHead)
vGatherApps (VNorm (VCtor (c, sp))) = Just (VCtorHead c, sp)
vGatherApps (VNorm (VData (d, sp))) = Just (VDataHead d, sp)
vGatherApps (VNeu (h, sp)) = Just (VNeuHead h, sp)
vGatherApps (VLazy (h, sp)) = Just (VLazyHead h, sp)
vGatherApps _ = Nothing

headAsValue :: VHead -> VTm
headAsValue (VNeuHead h) = VNeu (h, Empty)
headAsValue (VLazyHead h) = VLazy (h, Empty)
headAsValue (VDataHead d) = VNorm (VData (d, Empty))
headAsValue (VCtorHead c) = VNorm (VCtor (c, Empty))

-- Pattern variable
pv :: STm
pv = SVar (Idx 0)

data VNorm
  = VPi PiMode Qty Name VTy Closure
  | VLam PiMode Qty Name Closure
  | VData VData
  | VCtor VCtor
  | VU
  deriving (Show)

data VTm
  = VNorm VNorm
  | VLazy VLazy
  | VNeu VNeu
  deriving (Show)

data WTm
  = WNorm VNorm
  | WNeu VNeu
  deriving (Show)

weakAsValue :: WTm -> VTm
weakAsValue (WNorm n) = VNorm n
weakAsValue (WNeu n) = VNeu n

vGetSpine :: VTm -> Spine VTm
vGetSpine (VNorm (VData (_, sp))) = sp
vGetSpine (VNorm (VCtor (_, sp))) = sp
vGetSpine (VNeu (_, sp)) = sp
vGetSpine (VLazy (_, sp)) = sp
vGetSpine _ = Empty

pattern VVar :: Lvl -> VNeu
pattern VVar l = (VRigid l, Empty)

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = (VFlex m, Empty)

type STy = STm

data SPat = SPat {asTm :: STm, binds :: [(Qty, Name)]} deriving (Show)

data BoundState = Bound Qty | Defined deriving (Eq, Show)

type Bounds = [BoundState]

data STm
  = SPi PiMode Qty Name STm STm
  | SLam PiMode Qty Name STm
  | SLet Qty Name STy STm STm
  | SMeta MetaVar Bounds
  | SApp PiMode Qty STm STm
  | SCase SCase
  | SU
  | SData DataGlobal
  | SCtor (CtorGlobal, Spine STm)
  | SDef DefGlobal
  | SPrim PrimGlobal
  | SVar Idx
  | SLit (Lit STm)
  | SRepr STm
  | SUnrepr STm
  deriving (Show)

sReprTimes :: Int -> STm -> STm
sReprTimes 0 t = t
sReprTimes n t
  | n > 0 = SRepr (sReprTimes (n - 1) t)
  | otherwise = SUnrepr (sReprTimes (n + 1) t)

-- @@Todo: case and constructor params should be (Lvl, [VTm]) instead.
-- Otherwise we are doing lots of unnecessary work.

sAppSpine :: STm -> Spine STm -> STm
sAppSpine t Empty = t
sAppSpine t (Arg m q u :<| sp) = sAppSpine (SApp m q t u) sp

uniqueSLams :: (HasNameSupply m) => [(PiMode, Qty)] -> STm -> m STm
uniqueSLams ms t = do
  sp <- fromList <$> mapM (\(m, q) -> Param m q <$> uniqueName <*> return ()) ms
  return $ sLams sp t

sLams :: Tel () -> STm -> STm
sLams Empty t = t
sLams (Param m q x () :<| sp) t = SLam m q x (sLams sp t)

sGatherApps :: STm -> (STm, Spine STm)
sGatherApps (SApp m q t u) = let (t', sp) = sGatherApps t in (t', sp :|> Arg m q u)
sGatherApps t = (t, Empty)

sPis :: Tel STm -> STm -> STm
sPis Empty b = b
sPis (Param q m n a :<| xs) b = SPi q m n a (sPis xs b)

sGatherPis :: STm -> (Tel STm, STm)
sGatherPis = \case
  SPi m q n a b -> let (xs, b') = sGatherPis b in (Param m q n a :<| xs, b')
  t -> (Empty, t)

sGatherLams :: STm -> (Tel (), STm)
sGatherLams = \case
  SLam m q n t -> let (ns, b) = sGatherLams t in (Param m q n () :<| ns, b)
  t -> (Empty, t)

sGatherLets :: STm -> ([(Qty, Name, STy, STm)], STm)
sGatherLets = \case
  SLet q n ty t u -> let (binds, ret) = sGatherLets u in ((q, n, ty, t) : binds, ret)
  t -> ([], t)

sGlobWithParams :: Glob -> Spine STm -> STm
sGlobWithParams (DataGlob d) _ = SData d
sGlobWithParams (CtorGlob c) xs = SCtor (c, xs)
sGlobWithParams (DefGlob d) _ = SDef d
sGlobWithParams (PrimGlob p) _ = SPrim p

-- HOAS

type HCase = (Case HTm HTm SPat ([HTm] -> HTm))

type HTy = HTm

data HTm
  = HPi PiMode Qty Name HTm (HTm -> HTm)
  | HLam PiMode Qty Name (HTm -> HTm)
  | HLet Qty Name HTy HTm (HTm -> HTm)
  | HMeta MetaVar Bounds
  | HApp PiMode Qty HTm HTm
  | HCase HCase
  | HVar Lvl
  | HU
  | HData DataGlobal
  | HCtor (CtorGlobal, Spine HTm)
  | HDef DefGlobal
  | HPrim PrimGlobal
  | HLit (Lit HTm)
  | HRepr HTm
  | HUnrepr HTm


embedCase :: Lvl -> HCase -> SCase
embedCase l (Case d ps s is t cs) =
  Case
    d
    (fmap (fmap (embed l)) ps)
    (embed l s)
    (fmap (fmap (embed l)) is)
    (embed l t)
    (fmap embedClause cs)
  where
    embedClause :: Clause SPat ([HTm] -> HTm) -> Clause SPat STm
    embedClause (Clause p c) =
      let pvs = map HVar $ membersIn l (Lvl (length p.binds))
       in Clause p (fmap (embed l . ($ pvs)) c)

embed :: Lvl -> HTm -> STm
embed l = \case
  HPi m q n a b -> SPi m q n (embed l a) (embed (nextLvl l) (b (HVar l)))
  HLam m q n f -> SLam m q n (embed (nextLvl l) (f (HVar l)))
  HLet q n ty a b -> SLet q n (embed l ty) (embed l a) (embed (nextLvl l) (b (HVar l)))
  HMeta m bs -> SMeta m bs
  HApp m q t u -> SApp m q (embed l t) (embed l u)
  HCase c -> SCase (embedCase l c)
  HVar l' -> SVar (lvlToIdx l l')
  HU -> SU
  HData d -> SData d
  HCtor (c, sp) -> SCtor (c, fmap (fmap $ embed l) sp)
  HDef d -> SDef d
  HPrim p -> SPrim p
  HLit li -> SLit (fmap (embed l) li)
  HRepr t -> SRepr (embed l t)
  HUnrepr t -> SUnrepr (embed l t)

unembedCase :: Env HTm -> SCase -> HCase
unembedCase env (Case d ps s is t cs) =
  Case
    d
    (fmap (fmap (unembed env)) ps)
    (unembed env s)
    (fmap (fmap (unembed env)) is)
    (unembed env t)
    (fmap unembedClause cs)
  where
    unembedClause :: Clause SPat STm -> Clause SPat ([HTm] -> HTm)
    unembedClause (Clause p c) = Clause p (fmap (\c' bs -> unembed (reverse bs ++ env) c') c)

unembed :: Env HTm -> STm -> HTm
unembed env = \case
  SPi m q n a b -> HPi m q n (unembed env a) (\x -> unembed (x : env) b)
  SLam m q n t -> HLam m q n (\x -> unembed (x : env) t)
  SLet q n ty a b -> HLet q n (unembed env ty) (unembed env a) (\x -> unembed (x : env) b)
  SMeta m bs -> HMeta m bs
  SApp m q t u -> HApp m q (unembed env t) (unembed env u)
  SCase c -> HCase (unembedCase env c)
  SVar (Idx i) -> env !! i
  SU -> HU
  SData d -> HData d
  SCtor (c, sp) -> HCtor (c, fmap (fmap $ unembed env) sp)
  SDef d -> HDef d
  SPrim p -> HPrim p
  SLit li -> HLit (fmap (unembed env) li)
  SRepr t -> HRepr (unembed env t)
  SUnrepr t -> HUnrepr (unembed env t)
