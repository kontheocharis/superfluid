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
    Pat (..),
    Case (..),
    VCtor,
    HCtx (..),
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
    VLazyCase,
    VBlockedCase,
    patBinds,
    embedPat,
    unembedPat,
    SCase,
    mapClosureM,
    weakAsValue,
    vGetSpine,
    pattern VVar,
    pattern VMeta,
    HTm (..),
    pv,
    HTy,
    HTel (..),
    HCase,
    embed,
    unembed,
    unembedTel,
    hPis,
    hApp,
    hSimpleTel,
    hOwnSpine,
    embedClosure,
    embedCase,
    piArgsArity,
    hGatherApps,
    pattern VV,
    HPat,
    embedTel,
    hLams,
    extendTel,
    joinTels,
    removing,
    extendCtxWithTel,
    hoistBindersSp,
    hoistBinders,
    hoistBinders',
    hoistBinder,
    lastVar,
    ctxSize,
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
import Control.Monad (void)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Sequence (Seq (..), fromList)
import qualified Data.Sequence as S

type VPat = VTm

data VPatB = VPatB {vPat :: VPat, binds :: [(Qty, Name)]} deriving (Show, Eq, Ord)

type VTy = VTm

type Env v = [v]

data Closure = Closure {numVars :: Int, env :: Env VTm, body :: STm} deriving (Show, Eq, Ord)

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
  deriving (Show, Eq, Ord)

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
  deriving (Show, Eq, Ord)

data VLazyHead
  = VDef DefGlobal
  | VLit (Lit VTm)
  | VLazyCase VLazyCase
  | VLet Qty Name VTy VTm Closure
  | VRepr VHead
  deriving (Show, Eq, Ord)

data VHead
  = VNeuHead VNeuHead
  | VLazyHead VLazyHead
  | VDataHead DataGlobal
  | VCtorHead (CtorGlobal, Spine VTm)
  deriving (Show, Eq, Ord)

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
  deriving (Show, Eq, Ord)

data VTm
  = VNorm VNorm
  | VLazy VLazy
  | VNeu VNeu
  deriving (Show, Eq, Ord)

data WTm
  = WNorm VNorm
  | WNeu VNeu
  deriving (Show, Eq, Ord)

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

pattern VV :: Lvl -> VTm
pattern VV l = VNeu (VRigid l, Empty)

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = (VFlex m, Empty)

type STy = STm

data SPat = SPat {asTm :: STm, binds :: [(Qty, Name)]} deriving (Show, Eq, Ord)

data BoundState = Bound Qty | Defined deriving (Eq, Show, Ord)

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
  deriving (Show, Eq, Ord)

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

sLams :: Tel a -> STm -> STm
sLams Empty t = t
sLams (Param m q x _ :<| sp) t = SLam m q x (sLams sp t)

sGatherApps :: STm -> (STm, Spine STm)
sGatherApps (SApp m q t u) = let (t', sp) = sGatherApps t in (t', sp :|> Arg m q u)
sGatherApps t = (t, Empty)

removing :: Lvl -> Seq a -> Seq a
removing (Lvl i) = S.deleteAt i

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

piArgsArity :: STm -> Tel ()
piArgsArity ty = do
  let (sArgs, _) = sGatherPis ty
  fmap void sArgs

-- HOAS

type HCase = (Case HTm HTm Pat ([HTm] -> HTm))

type HTy = HTm

type HPat = HTm

data HTm
  = HPi PiMode Qty Name HTy (HTm -> HTy)
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

data HTel = HEmpty | HWithParam PiMode Qty Name HTy (HTm -> HTel)

type HCtx = Tel HTy

lastVar :: HCtx -> Lvl
lastVar ctx = Lvl (length ctx - 1)

ctxSize :: HCtx -> Lvl
ctxSize = Lvl . length

hSimpleTel :: Tel HTy -> HTel
hSimpleTel = foldr (\(Param m q n a) acc -> HWithParam m q n a (const acc)) HEmpty

extendTel :: HTel -> (Spine HTm -> Param HTy) -> HTel
extendTel HEmpty g = let Param m q x ty = g Empty in HWithParam m q x ty (const HEmpty)
extendTel (HWithParam m q n a f) g = HWithParam m q n a (\x -> extendTel (f x) (\xs -> g (Arg m q x :<| xs)))

joinTels :: HTel -> (Spine HTm -> HTel) -> HTel
joinTels HEmpty g = g Empty
joinTels (HWithParam m q n a f) g = HWithParam m q n a (\x -> joinTels (f x) (\xs -> g (Arg m q x :<| xs)))

extendCtxWithTel :: HCtx -> (Spine HTm -> HTel) -> (HCtx, Spine HTm)
extendCtxWithTel = undefined -- a bit subtle @@Todo

unembedTel :: Env HTm -> Tel STy -> HTel
unembedTel _ Empty = HEmpty
unembedTel env (Param m q n a :<| xs) = HWithParam m q n (unembed env a) (\x -> unembedTel (x : env) xs)

embedTel :: Lvl -> HTel -> Tel STy
embedTel l = \case
  HEmpty -> Empty
  HWithParam m q n a f -> Param m q n (embed l a) :<| embedTel (nextLvl l) (f (HVar l))

hApp :: HTm -> Spine HTm -> HTm
hApp = foldl (\f (Arg m q u) -> HApp m q f u)

hPis :: HTel -> (Spine HTm -> HTy) -> HTy
hPis HEmpty b = b Empty
hPis (HWithParam m q n a f) b = HPi m q n a (\x -> hPis (f x) (\xs -> b (Arg m q x :<| xs)))

hLams :: HTel -> (Spine HTm -> HTm) -> HTm
hLams HEmpty b = b Empty
hLams (HWithParam m q n _ f) b = HLam m q n (\x -> hLams (f x) (\xs -> b (Arg m q x :<| xs)))

hGatherApps :: HTm -> (HTm, Spine HTm)
hGatherApps (HApp m q t u) = let (t', sp) = hGatherApps t in (t', sp :|> Arg m q u)
hGatherApps t = (t, Empty)

embedCase :: Lvl -> HCase -> SCase
embedCase l (Case d ps s is t cs) =
  Case
    d
    (fmap (fmap (embed l)) ps)
    (embed l s)
    (fmap (fmap (embed l)) is)
    (embed l t)
    (fmap (embedClause l) cs)
  where
    embedClause :: Lvl -> Clause Pat ([HTm] -> HTm) -> Clause SPat STm
    embedClause _ (Clause p c) =
      let binds = patBinds p
       in let pvs = map HVar $ membersIn l (Lvl (length binds))
           in Clause (embedPat l p) (fmap (embed l . ($ pvs)) c)

hOwnSpine :: Lvl -> Tel () -> Spine HTm
hOwnSpine _ Empty = Empty
hOwnSpine l (Param m q _ () :<| xs) = Arg m q (HVar l) :<| hOwnSpine (nextLvl l) xs

embedClosure :: Env VTm -> Tel () -> (Spine HTm -> HTm) -> Closure
embedClosure env n f =
  let ownSpine = hOwnSpine (Lvl (length env)) n
   in let fHere = f ownSpine
       in Closure (length n) env (embed (Lvl (length n + length env)) fHere)

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
    (fmap (unembedClause env) cs)
  where
    unembedClause :: Env HTm -> Clause SPat STm -> Clause Pat ([HTm] -> HTm)
    unembedClause env (Clause p c) = Clause (unembedPat env p) (fmap (\c' bs -> unembed (reverse bs ++ env) c') c)

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

hoistBindersSp :: Int -> Spine HTm -> (Spine HTm -> HTm)
hoistBindersSp sh t sp = undefined

hoistBinders :: Int -> HTm -> (Spine HTm -> HTm)
hoistBinders sh t sp = undefined

hoistBinder :: HTm -> (HTm -> HTm)
hoistBinder = undefined

hoistBinders' :: Int -> HTm -> ([HTm] -> HTm)
hoistBinders' sh t sp = undefined

data Pat = LvlP Lvl | CtorP (CtorGlobal, Spine HTm) (Spine Pat)

-- @@Todo:
patBinds :: Pat -> [(Qty, Name)]
patBinds = undefined

embedPat :: Lvl -> Pat -> SPat
embedPat = undefined

unembedPat :: Env HTm -> SPat -> Pat
unembedPat = undefined
