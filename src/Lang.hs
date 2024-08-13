{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang
  ( Type,
    GlobalName,
    Var (..),
    Term (..),
    TermValue (..),
    HasTermValue (..),
    TermData (..),
    PatValue,
    TypeValue,
    Loc (..),
    Pos (..),
    Pat,
    Item (..),
    PrimItem (..),
    DataItem (..),
    Lit (..),
    ReprDataItem (..),
    ReprDeclItem (..),
    ReprDataCtorItem (..),
    ReprDataCaseItem (..),
    CtorItem (..),
    DeclItem (..),
    Program (..),
    HasLoc (..),
    TermMappable (..),
    MapResult (..),
    PiMode (..),
    mapTerm,
    mapTermM,
    piTypeToList,
    listToPiType,
    listToApp,
    itemName,
    ItemId (..),
    itemId,
    isValidPat,
    termLoc,
    genTerm,
    termDataAt,
    locatedAt,
    typedAs,
    appToList,
    lamsToList,
    letToList,
    lams,
    startPos,
    endPos,
    isCompound,
    emptyTermData,
  )
where

import Algebra.Lattice (Lattice (..))
import Control.Applicative ((<|>))
import Control.Exception (assert)
import Control.Monad (foldM, join)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Extra (firstJustM)
import Control.Monad.Identity (runIdentity)
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Generics (Data)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.List.Extra (firstJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..), ViewL (..), ViewR (..), (><))
import qualified Data.Sequence as S
import Data.Traversable (for)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Natural (Natural)
import GHC.TypeNats (Nat)

-- | Whether a pi type is implicit or explicit.
data PiMode = Implicit | Explicit | Instance deriving (Eq, Generic, Data, Typeable, Show)

data ElabError
  = Mismatch PTm PTm
  | UnresolvedVariable Name
  | ImplicitMismatch PiMode PiMode
  | InvalidPattern PTm
  | InvalidCaseSubject PTm

data Sub = Sub {vars :: IntMap VTm}

instance Semigroup Sub where
  Sub v1 <> Sub v2 = Sub (IM.union v1 v2)

instance Monoid Sub where
  mempty = Sub IM.empty

data CanUnify = Yes | No | Maybe Sub

instance Lattice CanUnify where
  Yes \/ _ = Yes
  _ \/ Yes = Yes
  No \/ a = a
  a \/ No = a
  Maybe x \/ Maybe _ = Maybe x

  Yes /\ a = a
  a /\ Yes = a
  No /\ _ = No
  _ /\ No = No
  Maybe x /\ Maybe y = Maybe (x <> y)

-- | A literal
data Lit t
  = StringLit String
  | CharLit Char
  | NatLit Natural
  | FinLit Natural t
  deriving (Generic, Data, Typeable, Show, Functor, Traversable, Foldable)

instance (Eq t) => Eq (Lit t) where
  (StringLit s1) == (StringLit s2) = s1 == s2
  (CharLit c1) == (CharLit c2) = c1 == c2
  (NatLit n1) == (NatLit n2) = n1 == n2
  (FinLit n1 _) == (FinLit n2 _) = n1 == n2
  _ == _ = False

newtype Idx = Idx {unIdx :: Int} deriving (Eq, Generic, Data, Typeable, Show)

newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Generic, Data, Typeable, Show)

nextLvl :: Lvl -> Lvl
nextLvl (Lvl l) = Lvl (l + 1)

nextLvls :: Lvl -> Int -> Lvl
nextLvls (Lvl l) n = Lvl (l + n)

lvlToIdx :: Lvl -> Lvl -> Idx
lvlToIdx (Lvl l) (Lvl i) = Idx (l - i - 1)

data Arg t = Arg PiMode t deriving (Eq, Generic, Data, Typeable, Show, Functor, Traversable, Foldable)

argVal :: Arg t -> t
argVal (Arg _ t) = t

type Spine t = Seq (Arg t) -- IN REVERSE ORDER

mapSpine :: (t -> t') -> Spine t -> Spine t'
mapSpine f = fmap (fmap f)

mapSpineM :: (Monad m) => (t -> m t') -> Spine t -> m (Spine t')
mapSpineM f = traverse (traverse f)

data MetaVar = MetaVar Int deriving (Eq, Generic, Data, Typeable, Show)

type VPat = VTm

type SPat = STm

numBinds :: SPat -> Int
numBinds (SVar _) = 1
numBinds (SGlobal _) = 0
numBinds (SLit _) = 0
numBinds (SApp _ t u) = numBinds t + numBinds u
numBinds _ = error "impossible"

type STy = STm

data Clause p t = Possible p t | Impossible p deriving (Eq, Generic, Data, Typeable, Show, Functor, Foldable, Traversable)

instance Bifunctor Clause where
  bimap f g (Possible p t) = Possible (f p) (g t)
  bimap f _ (Impossible p) = Impossible (f p)

instance Bifoldable Clause where
  bifoldMap f g (Possible p t) = f p <> g t
  bifoldMap f _ (Impossible p) = f p

instance Bitraversable Clause where
  bitraverse f g (Possible p t) = Possible <$> f p <*> g t
  bitraverse f _ (Impossible p) = Impossible <$> f p

newtype CtorGlobal = CtorGlobal Name deriving (Eq, Generic, Data, Typeable, Show)

newtype DataGlobal = DataGlobal Name deriving (Eq, Generic, Data, Typeable, Show)

newtype DefGlobal = DefGlobal Name deriving (Eq, Generic, Data, Typeable, Show)

data Glob = CtorGlob CtorGlobal | DataGlob DataGlobal | DefGlob DefGlobal deriving (Eq, Generic, Data, Typeable, Show)

clausePat :: Clause p t -> p
clausePat (Possible p _) = p
clausePat (Impossible p) = p

data VPatB = VPatB {pat :: VPat, numBinds :: Int}

data ReprTarget
  = ReprTy DataGlobal -- Represent a data type
  | ReprInh DataGlobal -- Represent an inhabitant of a data type
  | ReprDef DefGlobal -- Represent a definition
  | ReprCase DataGlobal -- Represent a case expression
  deriving (Eq, Generic, Data, Typeable, Show)

data STm
  = SPi PiMode Name STm STm
  | SLam PiMode Name STm
  | SLet Name STy STm STm
  | SMeta MetaVar
  | SApp PiMode STm STm
  | SCase STm [Clause SPat STm]
  | SU
  | SGlobal Glob
  | SVar Idx
  | SLit (Lit ())
  | SRepr Times STm
  deriving (Generic, Typeable)

type VTy = VTm

type Env v = [v]

data Closure = Closure {numVars :: Int, env :: Env VTm, body :: STm}

data VHead = VFlex MetaVar | VRigid Lvl deriving (Eq)

data Times = Finite Int | NegInf | PosInf deriving (Eq, Generic, Data, Typeable, Show)

inc :: Times -> Times
inc (Finite n) = Finite (n + 1)
inc NegInf = NegInf
inc PosInf = PosInf

dec :: Times -> Times
dec (Finite n) = Finite (n - 1)
dec NegInf = NegInf
dec PosInf = PosInf

inv :: Times -> Times
inv (Finite n) = Finite (-n)
inv NegInf = PosInf
inv PosInf = NegInf

instance Semigroup Times where
  Finite n <> Finite m = Finite (n + m)
  NegInf <> PosInf = Finite 0
  PosInf <> NegInf = Finite 0
  PosInf <> _ = PosInf
  _ <> PosInf = PosInf
  NegInf <> _ = NegInf
  _ <> NegInf = NegInf

instance Monoid Times where
  mempty = Finite 0

instance Bounded Times where
  minBound = NegInf
  maxBound = PosInf

instance Ord Times where
  compare (Finite n) (Finite m) = compare n m
  compare NegInf NegInf = EQ
  compare PosInf PosInf = EQ
  compare NegInf _ = LT
  compare _ NegInf = GT
  compare PosInf _ = GT
  compare _ PosInf = LT

data VNeu
  = VApp VHead (Spine VTm)
  | VCase VNeu [Clause VPatB Closure]
  | VReprApp Times VHead (Spine VTm)

data VTm
  = VPi PiMode Name VTy Closure
  | VLam PiMode Name Closure
  | VU
  | VGlobal Glob (Spine VTm)
  | VLit (Lit ())
  | VNeu VNeu

infixl 8 $$

pattern VVar :: Lvl -> VNeu
pattern VVar l = VApp (VRigid l) Empty

pattern VMeta :: MetaVar -> VNeu
pattern VMeta m = VApp (VFlex m) Empty

pattern VHead :: VHead -> VNeu
pattern VHead m = VApp m Empty

pattern VRepr :: Times -> VHead -> VNeu
pattern VRepr m t = VReprApp m t Empty

($$) :: (Eval m) => Closure -> [VTm] -> m VTm
Closure _ env t $$ us = eval (us ++ env) t

vAppNeu :: (Eval m) => Lvl -> VNeu -> Spine VTm -> m VTm
vAppNeu _ (VApp h us) u = return $ VNeu (VApp h (us >< u))
vAppNeu _ (VReprApp m h us) u = return $ VNeu (VReprApp m h (us >< u))
vAppNeu l (VCase c cls) u =
  (VNeu . VCase c)
    <$> mapM
      ( \cl -> do
          u' <- traverse (traverse (quote (nextLvls l (clausePat cl).numBinds))) u
          bitraverse return (postCompose (`sAppSpine` u')) cl
      )
      cls

vApp :: (Eval m) => Lvl -> VTm -> Spine VTm -> m VTm
vApp l (VLam _ _ c) (Arg _ u :<| us) = do
  c' <- c $$ [u]
  vApp l c' us
vApp _ (VGlobal g us) u = return $ VGlobal g (us >< u)
vApp l (VNeu n) u = vAppNeu l n u
vApp _ _ _ = error "impossible"

vMatch :: VPat -> VTm -> Maybe (Env VTm)
vMatch (VNeu (VVar _)) u = Just [u]
vMatch (VGlobal (CtorGlob (CtorGlobal c)) ps) (VGlobal (CtorGlob (CtorGlobal c')) xs)
  | c == c' && length ps == length xs =
      foldM
        ( \acc (Arg _ p, Arg _ x) -> do
            env <- vMatch p x
            return $ env ++ acc
        )
        []
        (S.zip ps xs)
vMatch _ _ = Nothing

vCase :: (Eval m) => VNeu -> [Clause VPatB Closure] -> m VTm
vCase v cs =
  fromMaybe
    (return $ VNeu (VCase v cs))
    ( firstJust
        ( \clause -> do
            case clause of
              Possible p t -> case vMatch p.pat (VNeu v) of
                Just env -> Just $ t $$ env
                Nothing -> Nothing
              Impossible _ -> Nothing
        )
        cs
    )

evalToNeu :: (Eval m) => Env VTm -> STm -> m VNeu
evalToNeu env t = do
  t' <- eval env t
  case t' of
    VNeu n -> return n
    _ -> error "impossible"

postCompose :: (Eval m) => (STm -> STm) -> Closure -> m Closure
postCompose f (Closure n env t) = return $ Closure n env (f t)

preCompose :: (Eval m) => Closure -> (STm -> STm) -> m Closure
preCompose (Closure n env t) f = do
  v <- uniqueName
  return $ Closure n env (SApp Explicit (SLam Explicit v t) (f (SVar (Idx 0))))

reprClosure :: (Eval m) => Times -> Closure -> m Closure
reprClosure m t = do
  a <- postCompose (SRepr m) t
  preCompose a (SRepr (inv m))

vRepr :: (Eval m) => Times -> VTm -> m VTm
vRepr (Finite 0) t = return t
vRepr m (VPi e v ty t) = do
  ty' <- vRepr m ty
  t' <- reprClosure m t
  return $ VPi e v ty' t'
vRepr m (VLam e v t) = do
  t' <- reprClosure m t
  return $ VLam e v t'
vRepr _ VU = return VU
vRepr _ (VLit l) = return $ VLit l
vRepr m (VGlobal g sp) = return undefined -- @@TODO
vRepr m (VNeu (VCase (VCase v cs) sp)) = return undefined -- @@TODO
vRepr m (VNeu (VApp h sp)) = do
  sp' <- mapSpineM (vRepr m) sp
  return $ VNeu (VReprApp m h sp')
vRepr m (VNeu (VReprApp m' v sp)) = do
  sp' <- mapSpineM (vRepr m) sp
  let mm' = m <> m'
  if mm' == mempty
    then
      return $ VNeu (VApp v sp')
    else
      return $ VNeu (VReprApp mm' v sp')

close :: (Eval m) => Int -> Env VTm -> STm -> m Closure
close n env t = do
  b <- reduceUnderBinders
  if b
    then do
      t' <- nf (extendEnvByNVars n env) t
      return $ Closure n env t'
    else return $ Closure n env t

extendEnvByNVars :: Int -> Env VTm -> Env VTm
extendEnvByNVars n env = map (VNeu . VVar . Lvl . (+ length env)) [0 .. n - 1] ++ env

eval :: (Eval m) => Env VTm -> STm -> m VTm
eval env (SPi m v ty1 ty2) = do
  ty1' <- eval env ty1
  c <- close 1 env ty2
  return $ VPi m v ty1' c
eval env (SLam m v t) = do
  c <- close 1 env t
  return $ VLam m v c
eval env (SLet _ _ t1 t2) = do
  t1' <- eval env t1
  eval (t1' : env) t2
eval env (SApp m t1 t2) = do
  t1' <- eval env t1
  t2' <- eval env t2
  vApp (envQuoteLvl env) t1' (S.singleton (Arg m t2'))
eval env (SCase t cs) = do
  t' <- evalToNeu env t
  cs' <-
    mapM
      ( \p -> do
          let pat = clausePat p
          let n = numBinds pat
          pat' <- eval (extendEnvByNVars n env) pat
          bitraverse (const $ return (VPatB pat' n)) (close n env) p
      )
      cs
  vCase t' cs'
eval _ SU = return VU
eval _ (SLit l) = return $ VLit l
eval _ (SMeta m) = return $ VNeu (VMeta m)
eval _ (SGlobal g) = return $ VGlobal g Empty
eval env (SVar (Idx i)) = return $ env !! i
eval env (SRepr m t) = do
  t' <- eval env t
  vRepr m t'

newtype SolvedMetas = SolvedMetas (IntMap VTm)

emptySolvedMetas :: SolvedMetas
emptySolvedMetas = SolvedMetas IM.empty

class (Monad m) => HasSolvedMetas m where
  solvedMetas :: m SolvedMetas
  modifySolvedMetas :: (SolvedMetas -> SolvedMetas) -> m ()

  lookupMeta :: MetaVar -> m (Maybe VTm)
  lookupMeta (MetaVar m) = do
    SolvedMetas ms <- solvedMetas
    return $ IM.lookup m ms

  resetSolvedMetas :: m ()
  resetSolvedMetas = modifySolvedMetas (const emptySolvedMetas)

class (HasSolvedMetas m) => Eval m where
  reduceUnderBinders :: m Bool
  setReduceUnderBinders :: Bool -> m ()

  reduceUnfoldDefs :: m Bool
  setReduceUnfoldDefs :: Bool -> m ()

  uniqueName :: m Name

force :: (Eval m) => Lvl -> VTm -> m VTm
force l v@(VNeu (VApp (VFlex m) sp)) = do
  mt <- lookupMeta m
  case mt of
    Just t -> do
      t' <- vApp l t sp
      force l t'
    Nothing -> return v
force _ v = return v

quoteSpine :: (Eval m) => Lvl -> STm -> Spine VTm -> m STm
quoteSpine l t Empty = return t
quoteSpine l t (sp :|> Arg m u) = do
  t' <- quoteSpine l t sp
  u' <- quote l u
  return $ SApp m t' u'

quoteHead :: Lvl -> VHead -> STm
quoteHead _ (VFlex m) = SMeta m
quoteHead l (VRigid l') = SVar (lvlToIdx l l')

quote :: (Eval m) => Lvl -> VTm -> m STm
quote l vt = do
  vt' <- force l vt
  case vt' of
    VLam m x t -> do
      a <- t $$ [VNeu (VVar l)]
      t' <- quote (nextLvl l) a
      return $ SLam m x t'
    VPi m x ty t -> do
      ty' <- quote l ty
      a <- t $$ [VNeu (VVar l)]
      t' <- quote (nextLvl l) a
      return $ SPi m x ty' t'
    VU -> return SU
    VLit lit -> return $ SLit lit
    VGlobal g sp -> quoteSpine l (SGlobal g) sp
    VNeu (VApp h sp) -> quoteSpine l (quoteHead l h) sp
    VNeu (VReprApp m v sp) -> quoteSpine l (SRepr m (quoteHead l v)) sp
    VNeu (VCase v cs) -> do
      v' <- quote l (VNeu v)
      cs' <-
        mapM
          ( \pt -> do
              let n = (clausePat pt).numBinds
              bitraverse
                (\p -> quote (nextLvls l n) p.pat)
                ( \t -> do
                    a <- t $$ extendEnvByNVars n []
                    quote (nextLvls l n) a
                )
                pt
          )
          cs
      return $ (SCase v' cs')

nf :: (Eval m) => Env VTm -> STm -> m STm
nf env t = do
  t' <- eval env t
  quote (envQuoteLvl env) t'

envQuoteLvl :: Env VTm -> Lvl
envQuoteLvl env = Lvl (length env)

newtype Name = Name String deriving (Eq, Generic, Data, Typeable, Show, Ord)

type PTy = PTm

type PPat = PTm

data PDef = MkPDef
  { name :: Name,
    ty :: PTy,
    tm :: PTm,
    unfold :: Bool,
    recursive :: Bool
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data PCtor = MkPCtor
  { name :: Name,
    ty :: PTy
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data PData = MkPData
  { name :: Name,
    ty :: PTy,
    ctors :: [PCtor]
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data PCtorRep = MkPCtorRep
  { src :: PPat,
    target :: PTm
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data PCaseRep = MkPCaseRep
  { srcSubject :: PPat,
    srcBranches :: [Clause Name PPat],
    target :: PTm
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data PDataRep = MkPRep
  { src :: PPat,
    target :: PTy,
    ctors :: [PCtorRep],
    caseExpr :: PCaseRep
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data PDefRep = MkPDefRep
  { src :: PPat,
    target :: PTm
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data PItem
  = PDef PDef
  | PData PData
  | PDataRep PDataRep
  | PDefRep PDefRep
  deriving (Eq, Generic, Data, Typeable, Show)

data PTm
  = PPi PiMode Name PTy PTy
  | PLam PiMode Name PTm
  | PLet Name PTy PTm PTm
  | PApp PiMode PTm PTm
  | PCase PTm [Clause PPat PTm]
  | PU
  | PName Name
  | PLit (Lit PTm)
  | PHole Name
  | PRepr Times PTm
  | PWild
  | PLocated Loc PTm
  deriving (Eq, Generic, Data, Typeable, Show)

newtype Sig = Sig {members :: [Glob]}

class (Eval m) => Unify m where
  inPat :: m Bool
  setInPat :: Bool -> m ()

  enterPat :: m a -> m a
  enterPat a = do
    b <- inPat
    setInPat True
    a' <- a
    setInPat b
    return a'

  ifInPat :: m a -> m a -> m a
  ifInPat a b = do
    b' <- inPat
    if b' then a else b

class (Eval m, Unify m, MonadError ElabError m) => Elab m where
  getCtx :: m Ctx
  setCtx :: Ctx -> m ()

  accessCtx :: (Ctx -> a) -> m a
  accessCtx f = f <$> getCtx

  modifyCtx :: (Ctx -> Ctx) -> m ()
  modifyCtx f = do
    ctx <- getCtx
    setCtx (f ctx)

  enterCtx :: (Ctx -> Ctx) -> m a -> m a
  enterCtx f a = do
    ctx <- getCtx
    setCtx (f ctx)
    a' <- a
    setCtx ctx
    return a'

unifySpines :: (Unify m) => Lvl -> Spine VTm -> Spine VTm -> m CanUnify
unifySpines _ Empty Empty = return Yes
unifySpines l (sp :|> Arg _ u) (sp' :|> Arg _ u') = do
  x <- unifySpines l sp sp'
  (x /\) <$> unify l u u'
unifySpines _ _ _ = return No

unifyClauses :: (Unify m) => Lvl -> [Clause VPatB Closure] -> [Clause VPatB Closure] -> m CanUnify
unifyClauses l [] [] = return Yes
unifyClauses l (c : cs) (c' : cs') = do
  a <- unifyClause l c c'
  (a /\) <$> unifyClauses l cs cs'
unifyClauses _ _ _ = return No

unifyClause :: (Unify m) => Lvl -> Clause VPatB Closure -> Clause VPatB Closure -> m CanUnify
unifyClause l (Possible p t) (Possible p' t') = do
  let n = p.numBinds
  let n' = p'.numBinds
  assert (n == n') (return ())
  a <- unify (nextLvls l n) p.pat p'.pat
  x <- t $$ extendEnvByNVars n []
  x' <- t' $$ extendEnvByNVars n []
  (a /\) <$> unify (nextLvls l n) x x'
unifyClause l (Impossible p) (Impossible p') = do
  let n = p.numBinds
  let n' = p'.numBinds
  assert (n == n') (return ())
  unify (nextLvls l n) p.pat p'.pat
unifyClause _ _ _ = return No

unifyMeta :: (Unify m) => Lvl -> MetaVar -> Spine VTm -> VTm -> m CanUnify
unifyMeta = undefined

unifyRigid :: (Unify m) => Lvl -> Lvl -> Spine VTm -> VTm -> m CanUnify
unifyRigid = undefined

unifyReprApp :: (Unify m) => Lvl -> Times -> VHead -> Spine VTm -> VTm -> m CanUnify
unifyReprApp = undefined

unfoldAndUnify :: (Unify m) => Lvl -> DefGlobal -> Spine VTm -> VTm -> m CanUnify
unfoldAndUnify = undefined

unify :: (Unify m) => Lvl -> VTm -> VTm -> m CanUnify
unify l t1 t2 = do
  t1' <- force l t1
  t2' <- force l t2
  case (t1', t2') of
    (VPi m _ t c, VPi m' _ t' c') | m == m' -> do
      a <- unify l t t'
      x <- c $$ [VNeu (VVar l)]
      x' <- c' $$ [VNeu (VVar l)]
      (a /\) <$> unify (nextLvl l) x x'
    (VLam m _ c, VLam m' _ c') | m == m' -> do
      x <- c $$ [VNeu (VVar l)]
      x' <- c' $$ [VNeu (VVar l)]
      unify (nextLvl l) x x'
    (t, VLam m' _ c') -> do
      x <- vApp l t (S.singleton (Arg m' (VNeu (VVar l))))
      x' <- c' $$ [VNeu (VVar l)]
      unify (nextLvl l) x x'
    (VLam m _ c, t) -> do
      x <- c $$ [VNeu (VVar l)]
      x' <- vApp l t (S.singleton (Arg m (VNeu (VVar l))))
      unify (nextLvl l) x x'
    (VU, VU) -> return Yes
    (VLit a, VLit a') | a == a' -> return Yes
    (VGlobal (CtorGlob c) sp, VGlobal (CtorGlob c') sp') -> if c == c' then unifySpines l sp sp' else return No
    (VGlobal (DataGlob d) sp, VGlobal (DataGlob d') sp') -> if d == d' then unifySpines l sp sp' else return No
    (VGlobal (DefGlob f) sp, VGlobal (DefGlob f') sp') ->
      if f == f'
        then do
          a <- unifySpines l sp sp'
          b <- unfoldAndUnify l f sp t2'
          return $ a \/ b
        else unfoldAndUnify l f sp t2'
    (VGlobal (DefGlob f) sp, t') -> unfoldAndUnify l f sp t'
    (t, VGlobal (DefGlob f') sp') -> unfoldAndUnify l f' sp' t
    (VNeu (VCase s bs), VNeu (VCase s' bs')) -> do
      a <- unify l (VNeu s) (VNeu s')
      b <- unifyClauses l bs bs'
      return $ (a /\ b) \/ Maybe mempty
    (VNeu (VReprApp m v sp), VNeu (VReprApp m' v' sp')) | m == m' && v == v' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VRigid x) sp), VNeu (VApp (VRigid x') sp')) | x == x' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VFlex x) sp), VNeu (VApp (VFlex x') sp')) | x == x' -> do
      a <- unifySpines l sp sp'
      return $ a \/ Maybe mempty
    (VNeu (VApp (VFlex x) sp), t') -> unifyMeta l x sp t'
    (t, VNeu (VApp (VFlex x') sp')) -> unifyMeta l x' sp' t
    (VNeu (VApp (VRigid x) sp), t') -> unifyRigid l x sp t'
    (t, VNeu (VApp (VRigid x') sp')) -> unifyRigid l x' sp' t
    (VNeu (VReprApp m v sp), t') -> unifyReprApp l m v sp t'
    (t, VNeu (VReprApp m' v' sp')) -> unifyReprApp l m' v' sp' t
    (VNeu (VCase _ _), _) -> return $ Maybe mempty
    (_, VNeu (VCase _ _)) -> return $ Maybe mempty
    _ -> return No

data Ctx = Ctx {env :: Env VTm, lvl :: Lvl, types :: [VTy], names :: Map Name Lvl, currentLoc :: Maybe Loc}

bind :: Name -> VTy -> Ctx -> Ctx
bind x ty ctx = define x (VNeu (VVar ctx.lvl)) ty ctx

insertedBind :: Name -> VTy -> Ctx -> Ctx
insertedBind = bind

define :: Name -> VTm -> VTy -> Ctx -> Ctx
define x t ty ctx =
  ctx
    { env = t : ctx.env,
      lvl = nextLvl ctx.lvl,
      types = ty : ctx.types,
      names = M.insert x ctx.lvl ctx.names
    }

lookupName :: Name -> Ctx -> Maybe (Idx, VTy)
lookupName n ctx = case M.lookup n ctx.names of
  Just l -> let idx = lvlToIdx ctx.lvl l in Just (idx, ctx.types !! idx.unIdx)
  Nothing -> Nothing

definedValue :: Idx -> Ctx -> VTm
definedValue i ctx = ctx.env !! i.unIdx

located :: Loc -> Ctx -> Ctx
located l ctx = ctx {currentLoc = Just l}

freshUserMeta :: (Elab m) => Maybe Name -> m (STm, VTy)
freshUserMeta n = do
  m <- freshMeta >>= evalHere
  return undefined

freshMeta :: (Elab m) => m STy
freshMeta = undefined

insert :: (Elab m) => (STm, VTy) -> m (STm, VTy)
insert = undefined

evalHere :: (Elab m) => STm -> m VTm
evalHere t = do
  e <- accessCtx (\c -> c.env)
  eval e t

unifyHere :: (Elab m) => VTm -> VTm -> m ()
unifyHere t1 t2 = do
  l <- accessCtx (\c -> c.lvl)
  _ <- unify l t1 t2
  return ()

closeValHere :: (Elab m) => Int -> VTm -> m Closure
closeValHere n t = do
  (l, e) <- accessCtx (\c -> (c.lvl, c.env))
  t' <- quote (nextLvls l n) t
  close n e t'

closeHere :: (Elab m) => Int -> STm -> m Closure
closeHere n t = do
  e <- accessCtx (\c -> c.env)
  close n e t

forceHere :: (Elab m) => VTm -> m VTm
forceHere t = do
  l <- accessCtx (\c -> c.lvl)
  force l t

forcePiType :: (Elab m) => PiMode -> VTy -> m (VTy, Closure)
forcePiType m ty = do
  ty' <- forceHere ty
  case ty' of
    VPi m' _ a b -> do
      if m == m'
        then return (a, b)
        else throwError $ ImplicitMismatch m m'
    _ -> do
      a <- freshMeta >>= evalHere
      v <- uniqueName
      b <- closeHere 1 =<< enterCtx (bind v a) freshMeta
      unifyHere ty (VPi m v a b)
      return (a, b)

toPSpine :: PTm -> (PTm, Spine PTm)
toPSpine (PApp m t u) = let (t', sp) = toPSpine t in (t', sp :|> Arg m u)
toPSpine t = (t, Empty)

sAppSpine :: STm -> Spine STm -> STm
sAppSpine t Empty = t
sAppSpine t (Arg m u :<| sp) = sAppSpine (SApp m t u) sp

inferSpine :: (Elab m) => (STm, VTy) -> Spine PTm -> m (STm, VTy)
inferSpine (t, ty) Empty = return (t, ty)
inferSpine (t, ty) (Arg m u :<| sp) = do
  (t', ty') <- case m of
    Implicit -> return (t, ty)
    Explicit -> insert (t, ty)
    Instance -> error "unimplemented"
  (a, b) <- forcePiType m ty'
  u' <- check u a
  uv <- evalHere u'
  b' <- b $$ [uv]
  inferSpine (SApp m t' u', b') sp

lastIdx :: STm
lastIdx = SVar (Idx 0)

symbolicArgsForClosure :: Lvl -> Closure -> [VTm]
symbolicArgsForClosure l (Closure n _ t) = map (VNeu . VVar . Lvl . (+ l.unLvl)) [0 .. n - 1]

evalInOwnCtx :: (Elab m) => Closure -> m VTm
evalInOwnCtx cl = do
  let vars = extendEnvByNVars cl.numVars []
  cl $$ vars

forbidPat :: (Elab m) => PTm -> m ()
forbidPat p = ifInPat (throwError $ InvalidPattern p) (return ())

newPatBind :: (Elab m) => Name -> m (STm, VTy)
newPatBind x = do
  ty <- evalHere =<< freshMeta
  modifyCtx (bind x ty)
  return (lastIdx, ty)

ifIsCtorName :: (Elab m) => Idx -> Name -> (CtorGlobal -> m a) -> m a -> m a
ifIsCtorName i n a b = do
  v <- accessCtx (definedValue i) >>= forceHere
  case v of
    VGlobal (CtorGlob g@(CtorGlobal s)) Empty | s == n -> a g
    _ -> b

ifIsData :: (Elab m) => VTy -> (DataGlobal -> m a) -> m a -> m a
ifIsData v a b = do
  v' <- forceHere v
  case v' of
    VGlobal (DataGlob g@(DataGlobal s)) _ -> a g
    _ -> b

infer :: (Elab m) => PTm -> m (STm, VTy)
infer term = case term of
  PLocated l t -> enterCtx (located l) $ infer t
  PName x -> do
    n <- accessCtx (lookupName x)
    case n of
      Just (i, t) ->
        ifInPat
          (ifIsCtorName i x (\g -> return (SGlobal (CtorGlob g), t)) (newPatBind x))
          (return (SVar i, t))
      Nothing -> ifInPat (newPatBind x) (throwError $ UnresolvedVariable x)
  PLam m x t -> do
    forbidPat term
    a <- freshMeta >>= evalHere
    (t', b) <- enterCtx (bind x a) $ infer t >>= insert
    b' <- closeValHere 1 b
    return (SLam m x t', VPi m x a b')
  PApp {} -> do
    let (subject, sp) = toPSpine term
    (s, sTy) <- infer subject
    inferSpine (s, sTy) sp
  PU -> forbidPat term >> return (SU, VU)
  PPi m x a b -> do
    forbidPat term
    a' <- check a VU
    av <- evalHere a'
    b' <- enterCtx (bind x av) $ check b VU
    return (SPi m x a' b', VU)
  PLet x a t u -> do
    forbidPat term
    a' <- check a VU
    va <- evalHere a'
    t' <- check t va
    vt <- evalHere t'
    (u', b) <- enterCtx (define x vt va) $ infer u
    pure (SLet x a' t' u', b)
  PRepr m x -> do
    forbidPat term
    (x', ty) <- infer x
    reprTy <- vRepr m ty
    return (SRepr m x', reprTy)
  PHole n -> do
    forbidPat term
    freshUserMeta (Just n)
  PWild ->
    ifInPat
      (uniqueName >>= newPatBind)
      (freshUserMeta Nothing)
  PCase s cs -> do
    forbidPat term
    (s', sTy) <- infer s
    vs <- evalHere s'
    d <- ifIsData sTy return (throwError $ InvalidCaseSubject s)

    return undefined
  PLit l -> return undefined

check :: (Elab m) => PTm -> VTy -> m STm
check term typ = do
  typ' <- forceHere typ
  case (term, typ') of
    (PLocated l t, ty) -> enterCtx (located l) $ check t ty
    (PLam m x t, VPi m' _ a b) | m == m' -> do
      forbidPat term
      vb <- evalInOwnCtx b
      SLam m x <$> enterCtx (bind x a) (check t vb)
    (t, VPi Implicit x' a b) -> do
      vb <- evalInOwnCtx b
      SLam Implicit x' <$> enterCtx (insertedBind x' a) (check t vb)
    (PLet x a t u, ty) -> do
      forbidPat term
      a' <- check a VU
      va <- evalHere a'
      t' <- check t va
      vt <- evalHere t'
      u' <- enterCtx (define x vt va) $ check u ty
      return (SLet x a' t' u')
    (PRepr m t, VNeu (VRepr m' t')) | m == m' -> do
      forbidPat term
      tc <- check t (VNeu (VHead t'))
      return $ SRepr m tc
    (PRepr m t, ty) | m < mempty -> do
      forbidPat term
      (t', ty') <- infer t >>= insert
      reprTy <- vRepr (inv m) ty
      unifyHere reprTy ty'
      return $ SRepr m t'
    (te, ty) -> do
      (te', ty') <- infer te >>= insert
      unifyHere ty ty'
      return te'

-- | A term
data TermValue
  = -- Dependently-typed lambda calculus with Pi and Sigma:
    PiT PiMode Var Type Term
  | Lam PiMode Var Term
  | Let Var Type Term Term
  | App PiMode Term Term
  | SigmaT Var Type Term
  | Pair Term Term
  | Case (Maybe Term) Term [(Pat, Maybe Term)] -- if the branch is Nothing, it is "impossible"
  | -- | Type of types (no universe polymorphism)
    TyT
  | -- | Variable
    V Var
  | -- | Wildcard pattern
    Wild
  | -- | Global variable (declaration)
    Global String
  | -- | Hole identified by an integer
    Hole Var
  | -- | A literal
    Lit (Lit Term)
  | -- | Metavar identified by an integer
    Meta Var
  | -- | Represent a term
    Rep Term
  | -- | Unrepresent a term of the given named type
    Unrep String Term
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A term with associated data.
data Term = Term {value :: TermValue, dat :: TermData} deriving (Eq, Generic, Data, Typeable, Show)

-- | Alias for type values (just for documentation purposes)
type TypeValue = TermValue

-- | Alias for pattern values (just for documentation purposes)
type PatValue = TermValue

-- | An optional location in the source code, represented by a start (inclusive) and
-- end (exclusive) position.
data Loc = NoLoc | Loc Pos Pos deriving (Eq, Generic, Data, Typeable, Show)

-- | A monoid instance for locations, that gets the maximum span.
instance Monoid Loc where
  mempty = NoLoc

instance Semigroup Loc where
  NoLoc <> NoLoc = NoLoc
  NoLoc <> Loc s e = Loc s e
  Loc s e <> NoLoc = Loc s e
  Loc s1 e1 <> Loc s2 e2 = Loc (min s1 s2) (max e1 e2)

instance Ord Loc where
  NoLoc <= _ = True
  _ <= NoLoc = False
  Loc s1 e1 <= Loc s2 e2 = s1 <= s2 && e1 <= e2

-- | A position in the source code, represented by a line and column number.
data Pos = Pos Int Int deriving (Eq, Generic, Data, Typeable, Show)

-- | An ordering for positions, that gets the minimum position.
instance Ord Pos where
  Pos l1 c1 <= Pos l2 c2 = l1 < l2 || (l1 == l2 && c1 <= c2)

-- | Get the starting position of a location.
startPos :: Loc -> Maybe Pos
startPos NoLoc = Nothing
startPos (Loc start _) = Just start

-- | Get the ending position of a location.
endPos :: Loc -> Maybe Pos
endPos NoLoc = Nothing
endPos (Loc _ end) = Just end

-- | Auxiliary data contained alongside a term.
--
-- For now stores only the location in the source code, but will
-- be extended to store type information too.
data TermData = TermData {loc :: Loc, annotTy :: Maybe Type} deriving (Eq, Generic, Data, Typeable, Show)

-- | Empty term data.
emptyTermData :: TermData
emptyTermData = TermData NoLoc Nothing

-- | Class of types that have a location.
class HasLoc a where
  getLoc :: a -> Loc

instance HasLoc Term where
  getLoc = termLoc

instance HasLoc TermData where
  getLoc x = x.loc

instance HasLoc Loc where
  getLoc = id

-- | Create a term with the given value and location.
locatedAt :: (HasLoc a) => a -> TermValue -> Term
locatedAt a t = Term t (termDataAt (getLoc a))

-- | Create term data with the given location.
termDataAt :: (HasLoc a) => a -> TermData
termDataAt x = TermData (getLoc x) Nothing

-- | Get the term data from a term.
termLoc :: Term -> Loc
termLoc x = x.dat.loc

-- | Set the type annotation of a term.
typedAs :: Type -> Term -> Term
typedAs ty (Term t d) = Term t (d {annotTy = Just ty})

-- | Generated term, no data
genTerm :: TermValue -> Term
genTerm t = Term t emptyTermData

-- | Convert a pi type to a list of types and the return type.
piTypeToList :: Type -> ([(PiMode, Var, Type)], Type)
piTypeToList (Term (PiT m v ty1 ty2) _) = let (tys, ty) = piTypeToList ty2 in ((m, v, ty1) : tys, ty)
piTypeToList t = ([], t)

-- | Convert a list of types and the return type to a pi type.
listToPiType :: ([(PiMode, Var, Type)], Type) -> Type
listToPiType ([], ty) = ty
listToPiType ((m, v, ty1) : tys, ty2) = Term (PiT m v ty1 (listToPiType (tys, ty2))) emptyTermData

-- | Convert a *non-empty* list of terms to an application term
listToApp :: (Term, [(PiMode, Term)]) -> Term
listToApp (t, ts) = foldl (\acc (m, x) -> Term (App m acc x) (termDataAt (termLoc acc <> termLoc x))) t ts

-- | Convert an application term to a *non-empty* list of terms
appToList :: Term -> (Term, [(PiMode, Term)])
appToList (Term (App m t1 t2) _) = let (t, ts) = appToList t1 in (t, ts ++ [(m, t2)])
appToList t = (t, [])

-- | Convert a let term to a list of bindings and the body term.
letToList :: Term -> ([(Var, Type, Term)], Term)
letToList (Term (Let v ty t1 t2) _) = let (bs, t) = letToList t2 in ((v, ty, t1) : bs, t)
letToList t = ([], t)

-- | Convert a lambda term to a list of variables and the body term.
lamsToList :: Term -> ([(PiMode, Var)], Term)
lamsToList (Term (Lam m v t) _) = let (vs, t') = lamsToList t in ((m, v) : vs, t')
lamsToList t = ([], t)

-- | Wrap a term in `n` lambdas.
lams :: [(PiMode, Var)] -> Term -> Term
lams [] t = t
lams ((m, v) : vs) t = Term (Lam m v (lams vs t)) (termDataAt t)

-- | An item is either a declaration or a data item.
data Item
  = Decl DeclItem
  | Data DataItem
  | ReprData ReprDataItem
  | ReprDecl ReprDeclItem
  | Prim PrimItem
  deriving (Eq, Generic, Data, Typeable, Show)

-- | An identifier for an item in a signature.
data ItemId
  = DataId String
  | DeclId String
  | ReprDataId String
  | ReprDeclId String
  | PrimId String
  deriving (Eq, Generic, Data, Typeable, Show)

-- | Get the identifier of an item.
itemId :: Item -> ItemId
itemId (Decl (DeclItem name _ _ _ _ _)) = DeclId name
itemId (Data (DataItem name _ _)) = DataId name
itemId (ReprData (ReprDataItem src _ _ _)) = ReprDataId (show src)
itemId (ReprDecl (ReprDeclItem name _)) = ReprDeclId name
itemId (Prim (PrimItem name _)) = PrimId name

-- | Get the name of an item.
itemName :: Item -> Maybe String
itemName (Decl d) = Just d.name
itemName (Data d) = Just d.name
itemName (ReprData _) = Nothing
itemName (ReprDecl _) = Nothing
itemName (Prim p) = Just p.name

data ReprDataCaseItem = ReprDataCaseItem
  { binds :: (Pat, Var, [(String, Pat)]), -- subjectBind, elimBind, [(ctorName, elimBind)]
    target :: Term
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprDataCtorItem = ReprDataCtorItem
  { src :: Pat,
    target :: Term
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprDataItem = ReprDataItem
  { src :: Pat,
    target :: Term,
    ctors :: [ReprDataCtorItem],
    cse :: Maybe ReprDataCaseItem
  }
  deriving (Eq, Generic, Data, Typeable, Show)

data ReprDeclItem = ReprDeclItem
  { src :: String,
    target :: Term
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A declaration is a sequence of clauses, defining the equations for a function.
data DeclItem = DeclItem
  { name :: String,
    ty :: Type,
    value :: Term,
    loc :: Loc,
    isRecursive :: Bool,
    unfold :: Bool
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A data item is an indexed inductive data type declaration, with a sequence
-- of constructors.
data DataItem = DataItem
  { name :: String,
    ty :: Type,
    ctors :: [CtorItem]
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A constructor item is a constructor name and type.
data CtorItem = CtorItem
  { name :: String,
    ty :: Type,
    idx :: Int,
    dataName :: String
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A primitive item is a primitive name and type.
data PrimItem = PrimItem
  { name :: String,
    ty :: Type
  }
  deriving (Eq, Generic, Data, Typeable, Show)

-- | A program is a sequence of items.
newtype Program = Program [Item]
  deriving (Eq, Generic, Data, Typeable, Show)

instance Semigroup Program where
  Program a <> Program b = Program (a <> b)

instance Monoid Program where
  mempty = Program []

-- | Result of a term map.
data MapResult a = Continue | Replace a | ReplaceAndContinue a

-- | Apply a function to a term, if it is a Just, otherwise return the term.
mapTerm :: (Term -> MapResult Term) -> Term -> Term
mapTerm f term = runIdentity $ mapTermM (return . f) term

-- | Apply a function to a term, if it is a Just, otherwise return the term (monadic).
mapTermM :: (Monad m) => (Term -> m (MapResult Term)) -> Term -> m Term
mapTermM f term = do
  term' <- f term
  case term' of
    Continue -> do
      mappedTerm <- mapTermRec term.value
      return (Term mappedTerm term.dat)
    ReplaceAndContinue t' -> do
      mappedTerm <- mapTermRec t'.value
      return (Term mappedTerm t'.dat)
    Replace t' -> return t'
  where
    mapTermRec t' = case t' of
      (PiT m v t1 t2) -> PiT m v <$> mapTermM f t1 <*> mapTermM f t2
      (Lam m v t) -> Lam m v <$> mapTermM f t
      (Let v t1 t2 t3) -> Let v <$> mapTermM f t1 <*> mapTermM f t2 <*> mapTermM f t3
      (App m t1 t2) -> App m <$> mapTermM f t1 <*> mapTermM f t2
      (SigmaT v t1 t2) -> SigmaT v <$> mapTermM f t1 <*> mapTermM f t2
      (Pair t1 t2) -> Pair <$> mapTermM f t1 <*> mapTermM f t2
      (Case elim t cs) -> Case <$> traverse (mapTermM f) elim <*> mapTermM f t <*> mapM (\(p, c) -> (,) <$> mapTermM f p <*> traverse (mapTermM f) c) cs
      TyT -> return TyT
      Wild -> return Wild
      (V v) -> return $ V v
      (Global s) -> return $ Global s
      (Hole i) -> return $ Hole i
      (Meta i) -> return $ Meta i
      (Lit (FinLit n i)) -> Lit . FinLit n <$> mapTermM f i
      (Lit l) -> return $ Lit l
      (Rep t) -> Rep <$> mapTermM f t
      (Unrep s t) -> Unrep s <$> mapTermM f t

class TermMappable t where
  -- | Apply a term function to an item.
  mapTermMappableM :: (Monad m) => (Term -> m (MapResult Term)) -> t -> m t

  -- | Apply a term function to an item (non-monadic)
  mapTermMappable :: (Term -> MapResult Term) -> t -> t
  mapTermMappable f = runIdentity . mapTermMappableM (return . f)

-- | Apply a term function to a constructor item.
mapCtorItemM :: (Monad m) => (Term -> m (MapResult Term)) -> CtorItem -> m CtorItem
mapCtorItemM f (CtorItem name ty idx d) = CtorItem name <$> mapTermM f ty <*> pure idx <*> pure d

-- | Apply a term function to a declaration item.
mapItemM :: (Monad m) => (Term -> m (MapResult Term)) -> Item -> m Item
mapItemM f (Decl (DeclItem name ty term pos recu unf)) = Decl <$> (DeclItem name <$> mapTermM f ty <*> mapTermM f term <*> pure pos <*> pure recu <*> pure unf)
mapItemM f (Data (DataItem name ty ctors)) = Data <$> (DataItem name <$> mapTermM f ty <*> mapM (mapCtorItemM f) ctors)
mapItemM f (ReprData d) = ReprData <$> mapReprDataItemM f d
mapItemM f (ReprDecl d) = ReprDecl <$> mapReprDeclItemM f d
mapItemM f (Prim (PrimItem name ty)) = Prim . PrimItem name <$> mapTermM f ty

mapReprDataItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDataItem -> m ReprDataItem
mapReprDataItemM f (ReprDataItem src target ctors caseItem) =
  ReprDataItem <$> mapTermM f src <*> mapTermM f target <*> mapM (mapReprDataCtorItemM f) ctors <*> traverse (mapReprDataCaseItemM f) caseItem

mapReprDeclItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDeclItem -> m ReprDeclItem
mapReprDeclItemM f (ReprDeclItem name target) = ReprDeclItem name <$> mapTermM f target

mapReprDataCtorItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDataCtorItem -> m ReprDataCtorItem
mapReprDataCtorItemM f (ReprDataCtorItem src target) = ReprDataCtorItem <$> mapTermM f src <*> mapTermM f target

mapReprDataCaseItemM :: (Monad m) => (Term -> m (MapResult Term)) -> ReprDataCaseItem -> m ReprDataCaseItem
mapReprDataCaseItemM f (ReprDataCaseItem binds target) = ReprDataCaseItem binds <$> mapTermM f target

-- | Apply a term function to a program.
mapProgramM :: (Monad m) => (Term -> m (MapResult Term)) -> Program -> m Program
mapProgramM f (Program items) = Program <$> mapM (mapItemM f) items

instance TermMappable Term where
  mapTermMappableM = mapTermM

instance TermMappable CtorItem where
  mapTermMappableM = mapCtorItemM

instance TermMappable Item where
  mapTermMappableM = mapItemM

instance TermMappable Program where
  mapTermMappableM = mapProgramM

instance TermMappable () where
  mapTermMappableM _ = return

-- Show instances for pretty printing:

class HasTermValue a where
  getTermValue :: a -> TermValue

instance HasTermValue Term where
  getTermValue t = t.value

instance HasTermValue TermValue where
  getTermValue = id

-- | Check if a term is compound (i.e. contains spaces), for formatting purposes.
isCompound :: (HasTermValue a) => a -> Bool
isCompound x =
  let x' = getTermValue x
   in case x' of
        (PiT {}) -> True
        (Lam {}) -> True
        (Let {}) -> True
        (Case {}) -> True
        (App {}) -> True
        (SigmaT {}) -> True
        (Rep {}) -> True
        (Unrep {}) -> True
        _ -> False

-- | Check if a given term is a valid pattern (no typechecking).
isValidPat :: Term -> Bool
isValidPat (Term (App _ a b) _) = isValidPat a && isValidPat b
isValidPat (Term (V _) _) = True
isValidPat (Term Wild _) = True
isValidPat (Term (Pair p1 p2) _) = isValidPat p1 && isValidPat p2
isValidPat _ = False

-- | Type alias for terms that are expected to be types (just for documentation purposes).
type Type = Term

-- | Type alias for terms that are expected to be patterns (just for documentation purposes).
type Pat = Term

-- | A global name is a string.
type GlobalName = String

-- | A variable
-- Represented by a string name and a unique integer identifier (no shadowing).
data Var = Var {name :: String, idx :: Int} deriving (Eq, Ord, Generic, Data, Typeable, Show)
