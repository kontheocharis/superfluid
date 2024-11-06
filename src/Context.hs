{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Context
  ( Ctx (..),
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
    binder,
  )
where

import Interfaces.General (Has (..))
import Common (Idx (..), Lvl (..), Name, Param (..), Qty, Tel, idxToLvl, lvlToIdx, members, nextLvl)
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Semiring (Semiring (times))
import Data.Sequence (Seq (..))
import Evaluation (Eval, eval, evalInOwnCtx, evalPat, quote)
import Printing (Pretty (..))
import Syntax
  ( BoundState (Bound, Defined),
    Bounds,
    Closure,
    Env,
    SPat,
    STm (..),
    STy,
    VPatB,
    VTm (..),
    VTy,
    pattern VVar,
  )

data CtxTy = CtxTy VTy | TyUnneeded deriving (Show)

data Ctx = Ctx
  { env :: Env VTm,
    lvl :: Lvl,
    types :: [CtxTy],
    qtys :: [Qty],
    bounds :: Bounds,
    nameList :: [Name],
    names :: Map Name Lvl
  }
  deriving (Show)

instance (Monad m, Pretty m VTm) => Pretty m CtxTy where
  pretty (CtxTy t) = pretty t
  pretty TyUnneeded = return "_"

instance (Monad m, Pretty m Name, Pretty m VTy) => Pretty m CtxEntry where
  pretty (CtxEntry name ty tm _ q bound) = do
    name' <- pretty name
    ty' <- pretty ty
    tm' <- case bound of
      Defined -> (" = " ++) <$> pretty tm
      Bound _ -> return ""
    return $ show q ++ name' ++ " : " ++ ty' ++ tm'

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
      qtys = [],
      names = M.empty
    }

data CtxEntry = CtxEntry
  { name :: Name,
    ty :: CtxTy,
    tm :: VTm,
    lvl :: Lvl,
    qty :: Qty,
    bound :: BoundState
  }

bind :: Name -> Qty -> VTy -> Ctx -> Ctx
bind x q ty ctx =
  addCtxEntry
    ( CtxEntry
        { name = x,
          ty = CtxTy ty,
          tm = VNeu (VVar ctx.lvl),
          lvl = ctx.lvl,
          qty = q,
          bound = Bound q
        }
    )
    ctx

insertedBind :: Name -> Qty -> VTy -> Ctx -> Ctx
insertedBind = bind

define :: Name -> Qty -> VTm -> VTy -> Ctx -> Ctx
define x q t ty ctx =
  addCtxEntry
    ( CtxEntry
        { tm = t,
          ty = CtxTy ty,
          bound = Defined,
          lvl = ctx.lvl,
          qty = q,
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

modifyCtx :: (Has m Ctx) => (Ctx -> Ctx) -> m ()
modifyCtx = modify

accessCtx :: (Has m Ctx) => (Ctx -> a) -> m a
accessCtx f = f <$> getCtx

enterCtx :: (Has m Ctx) => (Ctx -> Ctx) -> m a -> m a
enterCtx = enter

qty :: (Has m Qty) => m Qty
qty = view

need :: (Has m Qty) => Qty -> m a -> m a
need q = enter (`times` q)

expect :: (Has m Qty) => Qty -> m a -> m a
expect q = enter (const q)

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
  enterCtx (bind t.name t.qty t') (enterTel ts f)

quoteHere :: (Eval m, Has m Ctx) => VTm -> m STm
quoteHere t = do
  l <- accessCtx (\c -> c.lvl)
  quote l t

evalInOwnCtxHere :: (Eval m, Has m Ctx) => Closure -> m VTm
evalInOwnCtxHere t = do
  l <- accessCtx (\c -> c.lvl)
  evalInOwnCtx l t

binder :: (Has m Ctx) => Name -> Qty -> VTy -> (Lvl -> m a) -> m a
binder x q t f = do
  l <- accessCtx (\c -> c.lvl)
  enterCtx (bind x q t) $ f l
