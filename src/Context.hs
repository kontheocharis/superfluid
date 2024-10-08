{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Context
  ( Ctx (..),
    emptyCtx,
    Goal (..),
    bind,
    insertedBind,
    CtxEntry (..),
    assertIsNeeded,
    define,
    typelessBind,
    typelessBinds,
    lookupName,
  )
where

import Common (Lvl (..), Name, Qty, nextLvl, members, lvlToIdx, Idx (unIdx))
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as M
import Evaluation ()
import Printing (Pretty (..))
import Syntax
  ( BoundState (Bound, Defined),
    Bounds,
    Env,
    STm (..),
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
  pretty (CtxEntry name ty tm _ qty bound) = do
    name' <- pretty name
    ty' <- pretty ty
    tm' <- case bound of
      Defined -> (" = " ++) <$> pretty tm
      Bound -> return ""
    return $ name' ++ " : " ++ show qty ++ " " ++ ty' ++ tm'

instance (Monad m, Pretty m Name, Pretty m VTy) => Pretty m Ctx where
  pretty c =
    intercalate "\n" <$> mapM pretty (reverse (ctxEntries c))

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
          bound = Bound
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
          bound = Bound,
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

typelessBinds :: [(Name, Qty)] -> Ctx -> Ctx
typelessBinds ns ctx = foldr (uncurry typelessBind) ctx (reverse ns)

ctxEntries :: Ctx -> [CtxEntry]
ctxEntries ctx = map (indexCtx ctx) (members ctx.lvl )

indexCtx :: Ctx -> Lvl -> CtxEntry
indexCtx ctx l = do
  let i = (lvlToIdx ctx.lvl l).unIdx
  CtxEntry
    { name = ctx.nameList !! i,
      ty = ctx.types !! i,
      tm = ctx.env !! i,
      lvl = l,
      qty = ctx.qtys !! i,
      bound = ctx.bounds !! i
    }

lookupName :: Name -> Ctx -> Maybe CtxEntry
lookupName n ctx = case M.lookup n ctx.names of
  Just l -> Just $ indexCtx ctx l
  Nothing -> Nothing

data Goal = Goal
  { ctx :: Ctx,
    tm :: STm,
    ty :: VTy
  }
