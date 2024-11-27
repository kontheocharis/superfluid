{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Context
  ( Ctx,
    emptyCtx,
    Goal (..),
    bind,
    coindexCtx,
    indexCtx,
    insertedBind,
    CtxEntry (..),
    assertIsNeeded,
    define,
    getCtx,
    ctxEntries,
    typelessBind,
    typelessBinds,
    quoteHere,
    lookupName,
    need,
    expect,
    qty,
    enterCtx,
    accessCtx,
    modifyCtx,
    setCtx,
    evalHere,
    evalPatHere,
    enterTel,
    evalInOwnCtxHere,
    setCtxEntryQty,
    here,
    localInstances,
    getLvl,
    enterTypelessClosure,
    unfoldHere,
    unfoldLazyHere,
    closeHere,
    closeValHere,
    resolveHere,
    reprHere,
    getNames,
    modifyNames,
    bounds,
    embedHere,
    unembedHere,
    binder,
    embedEvalHere,
    quoteUnembedHere,
  )
where

import Common
  ( Has (..),
    HasNameSupply (..),
    Idx (..),
    Lvl (..),
    Name,
    Param (..),
    PiMode (..),
    Qty (..),
    Tel,
    idxToLvl,
    lvlToIdx,
    members,
    nextLvl,
    nextLvls,
  )
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Semiring (Semiring (times))
import Data.Sequence (Seq (..))
import Evaluation (Eval, close, eval, evalInOwnCtx, evalPat, quote, resolve, vUnfold, vUnfoldLazy, vRepr, quoteUnembed)
import Printing (Pretty (..))
import Syntax
  ( BoundState (Bound, Defined),
    Bounds,
    Closure (..),
    Env,
    SPat,
    STm (..),
    STy,
    VLazy,
    VPatB,
    VTm (..),
    VTy,
    pattern VVar, HTm (..), unembed, embed,
  )

data CtxTy = CtxTy VTy | TyUnneeded deriving (Show)

data Ctx = Ctx
  { env :: Env VTm,
    lvl :: Lvl,
    types :: [CtxTy],
    qtys :: [Qty],
    bounds :: Bounds,
    nameList :: [Name],
    instances :: [Bool],
    names :: Map Name Lvl
  }
  deriving (Show)

instance (Monad m, Pretty m VTm) => Pretty m CtxTy where
  pretty (CtxTy t) = pretty t
  pretty TyUnneeded = return "_"

instance (Monad m, Pretty m Name, Pretty m VTy) => Pretty m CtxEntry where
  pretty (CtxEntry name ty tm _ q i bound) = do
    name' <- pretty name
    ty' <- pretty ty
    tm' <- case bound of
      Defined -> (" = " ++) <$> pretty tm
      Bound _ -> return ""
    return $ (if i then "#instance " else "") ++ (if q /= Many then show q else "") ++ name' ++ " : " ++ ty' ++ tm'

instance (Monad m, Pretty m Name, Pretty m VTy) => Pretty m Ctx where
  pretty c =
    intercalate "\n" <$> mapM pretty (ctxEntries c)

assertIsNeeded :: CtxTy -> VTy
assertIsNeeded (CtxTy t) = t
assertIsNeeded TyUnneeded = error "assertIsNeeded: TyUnneeded"

emptyCtx :: Ctx
emptyCtx =
  Ctx
    { env = [],
      lvl = Lvl 0,
      types = [],
      bounds = [],
      nameList = [],
      instances = [],
      qtys = [],
      names = M.empty
    }

data CtxEntry = CtxEntry
  { name :: Name,
    ty :: CtxTy,
    tm :: VTm,
    lvl :: Lvl,
    qty :: Qty,
    inst :: Bool,
    bound :: BoundState
  }

getNames :: Ctx -> [Name]
getNames c = c.nameList

modifyNames :: ([Name] -> [Name]) -> Ctx -> Ctx
modifyNames f c = c {nameList = f c.nameList}

bind :: PiMode -> Name -> Qty -> VTy -> Ctx -> Ctx
bind m x q ty ctx =
  addCtxEntry
    ( CtxEntry
        { name = x,
          ty = CtxTy ty,
          tm = VNeu (VVar ctx.lvl),
          lvl = ctx.lvl,
          qty = q,
          inst = m == Instance,
          bound = Bound q
        }
    )
    ctx

insertedBind :: PiMode -> Name -> Qty -> VTy -> Ctx -> Ctx
insertedBind = bind

localInstances :: Ctx -> [(Idx, VTy)]
localInstances ctx =
  [ (Idx i, assertIsNeeded ty)
    | (i, (ty, inst)) <- zip [0 ..] (zip ctx.types ctx.instances),
      inst
  ]

define :: Name -> Qty -> VTm -> VTy -> Ctx -> Ctx
define x q t ty ctx =
  addCtxEntry
    ( CtxEntry
        { tm = t,
          ty = CtxTy ty,
          bound = Defined,
          lvl = ctx.lvl,
          qty = q,
          inst = False,
          name = x
        }
    )
    ctx

typelessBind :: Name -> Qty -> Ctx -> Ctx
typelessBind x q ctx =
  addCtxEntry
    ( CtxEntry
        { tm = VNeu (VVar ctx.lvl),
          ty = TyUnneeded,
          lvl = ctx.lvl,
          bound = Bound q,
          qty = q,
          inst = False,
          name = x
        }
    )
    ctx

addCtxEntry :: CtxEntry -> Ctx -> Ctx
addCtxEntry e ctx =
  ctx
    { env = e.tm : ctx.env,
      lvl = nextLvl ctx.lvl,
      types = e.ty : ctx.types,
      bounds = e.bound : ctx.bounds,
      names = M.insert e.name ctx.lvl ctx.names,
      qtys = e.qty : ctx.qtys,
      instances = e.inst : ctx.instances,
      nameList = e.name : ctx.nameList
    }

setCtxEntryQty :: Lvl -> Qty -> Ctx -> Ctx
setCtxEntryQty l q ctx =
  ctx
    { qtys = replaceAt (lvlToIdx ctx.lvl l) q ctx.qtys
    }
  where
    -- How does haskell not have this function?
    replaceAt :: Idx -> a -> [a] -> [a]
    replaceAt (Idx i) x xs = take i xs ++ [x] ++ drop (i + 1) xs

typelessBinds :: [(Qty, Name)] -> Ctx -> Ctx
typelessBinds ns ctx = foldr (uncurry . flip $ typelessBind) ctx (reverse ns)

ctxEntries :: Ctx -> [CtxEntry]
ctxEntries ctx = map (coindexCtx ctx) (members ctx.lvl)

indexCtx :: Ctx -> Idx -> CtxEntry
indexCtx ctx idx@(Idx i) = do
  CtxEntry
    { name = ctx.nameList !! i,
      ty = ctx.types !! i,
      tm = ctx.env !! i,
      lvl = idxToLvl ctx.lvl idx,
      qty = ctx.qtys !! i,
      inst = ctx.instances !! i,
      bound = ctx.bounds !! i
    }

coindexCtx :: Ctx -> Lvl -> CtxEntry
coindexCtx ctx l = indexCtx ctx (lvlToIdx ctx.lvl l)

lookupName :: Name -> Ctx -> Maybe CtxEntry
lookupName n ctx = case M.lookup n ctx.names of
  Just l -> Just $ coindexCtx ctx l
  Nothing -> Nothing

data Goal = Goal
  { ctx :: Ctx,
    name :: Maybe Name,
    tm :: STm,
    qty :: Qty,
    ty :: VTy
  }

getCtx :: (Has m Ctx) => m Ctx
getCtx = view

setCtx :: (Has m Ctx) => Ctx -> m ()
setCtx = modify . const

bounds :: Ctx -> Bounds
bounds ctx = ctx.bounds

modifyCtx :: (Has m Ctx) => (Ctx -> Ctx) -> m ()
modifyCtx = modify

accessCtx :: (Has m Ctx) => (Ctx -> a) -> m a
accessCtx f = f <$> getCtx

enterCtx :: (Has m Ctx) => (Ctx -> Ctx) -> m a -> m a
enterCtx = enter

enterTypelessClosure :: (Has m Ctx, HasNameSupply m) => [Qty] -> Closure -> m a -> m a
enterTypelessClosure qs c m = do
  ns <- uniqueNames c.numVars
  enterCtx (typelessBinds (zip qs ns)) m

getLvl :: (Has m Ctx) => m Lvl
getLvl = accessCtx (\c -> c.lvl)

qty :: (Has m Qty) => m Qty
qty = view

need :: (Has m Qty) => Qty -> m a -> m a
need q = enter (`times` q)

expect :: (Has m Qty) => Qty -> m a -> m a
expect q = enter (const q)

here :: (Has m Ctx) => (Lvl -> a) -> m a
here f = f <$> accessCtx (\c -> c.lvl)

evalHere :: (Eval m, Has m Ctx) => STm -> m VTm
evalHere t = do
  e <- accessCtx (\c -> c.env)
  eval e t

evalPatHere :: (Eval m, Has m Ctx) => SPat -> m VPatB
evalPatHere t = do
  e <- accessCtx (\c -> c.env)
  evalPat e t

enterTel :: (Eval m, Has m Ctx) => Tel STy -> m a -> m a
enterTel Empty f = f
enterTel (t :<| ts) f = do
  t' <- evalHere t.ty
  enterCtx (bind t.mode t.name t.qty t') (enterTel ts f)

binder :: (Has m Ctx) => PiMode -> Qty -> Name -> VTy -> (Lvl -> m a) -> m a
binder m q x a f = do
  l <- getLvl
  enterCtx (bind m x q a) $ f l

quoteHere :: (Eval m, Has m Ctx) => VTm -> m STm
quoteHere t = do
  l <- accessCtx (\c -> c.lvl)
  quote l t

evalInOwnCtxHere :: (Eval m, Has m Ctx) => Closure -> m VTm
evalInOwnCtxHere t = do
  l <- accessCtx (\c -> c.lvl)
  evalInOwnCtx l t

closeValHere :: (Eval m, Has m Ctx) => Int -> VTm -> m Closure
closeValHere n t = do
  (l, e) <- accessCtx (\c -> (c.lvl, c.env))
  t' <- quote (nextLvls l n) t
  close n e t'

closeHere :: (Eval m, Has m Ctx) => Int -> STm -> m Closure
closeHere n t = do
  e <- accessCtx (\c -> c.env)
  close n e t

unfoldLazyHere :: (Eval m, Has m Ctx) => VLazy -> m (Maybe VTm)
unfoldLazyHere (n, sp) = do
  lvl <- getLvl
  vUnfoldLazy lvl (n, sp)

unfoldHere :: (Eval m, Has m Ctx) => VTm -> m VTm
unfoldHere t = do
  l <- accessCtx (\c -> c.lvl)
  vUnfold l t

resolveHere :: (Eval m, Has m Ctx) => VTm -> m VTm
resolveHere t = do
  e <- accessCtx (\c -> c.env)
  resolve e t

reprHere :: (Eval m, Has m Ctx) => Int -> VTm -> m VTm
reprHere m t = do
  l <- accessCtx (\c -> c.lvl)
  vRepr l m t

getHoasEnv :: (Has m Ctx) => m (Env HTm)
getHoasEnv = do
  es <- access ctxEntries
  return $ map (\e -> HVar e.lvl) es

unembedHere :: (Has m Ctx) => STm -> m HTm
unembedHere t = do
  h <- getHoasEnv
  return $ unembed h t

quoteUnembedHere :: (Eval m, Has m Ctx) => VTm -> m HTm
quoteUnembedHere t = do
  l <- getLvl
  quoteUnembed l t

embedEvalHere :: (Eval m, Has m Ctx) => HTm -> m VTm
embedEvalHere t = do
  t' <- embedHere t
  evalHere t'

embedHere :: (Has m Ctx) => HTm -> m STm
embedHere t = do
  l <- getLvl
  return $ embed l t

instance Has m Ctx => Has m [Name] where
  view = do
    ctx <- accessCtx id
    return (getNames ctx)

  modify f = do
    ctx <- accessCtx id
    modifyCtx (modifyNames f)

instance Has m Ctx => Has m (Env VTm) where
  view = accessCtx (\c -> c.env)
  modify f = modifyCtx (\c -> c {env = f c.env})

instance Has m Ctx => Has m Lvl where
  view = accessCtx (\c -> c.lvl)
  modify f = modifyCtx (\c -> c {lvl = f c.lvl})

