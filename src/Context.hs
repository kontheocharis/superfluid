{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
module Context
  ( Ctx (..),
    emptyCtx,
    Goal (..),
    bind,
    insertedBind,
    define,
    typelessBind,
    typelessBinds,
    CtxTy (..),
    lookupName,
  )
where

import Common (Idx (..), Lvl (..), lvlToIdx, nextLvl, Name)
import Data.List (intercalate, zipWith4)
import Data.Map (Map)
import qualified Data.Map as M
import Evaluation ()
import Printing (Pretty (..))
import Syntax (BoundState (Bound, Defined), Bounds, STm (..))
import Value
  ( Env,
    VTm (..),
    VTy,
    pattern VVar,
  )

data CtxTy = CtxTy VTy | TyUnneeded deriving (Show)

data Ctx = Ctx
  { env :: Env VTm,
    lvl :: Lvl,
    types :: [CtxTy],
    bounds :: Bounds,
    nameList :: [Name],
    names :: Map Name Lvl
  }
  deriving (Show)

instance (Monad m, Pretty m VTm) => Pretty m CtxTy where
  pretty (CtxTy t) = pretty t
  pretty TyUnneeded = return "_"

instance (Monad m, Pretty m Name, Pretty m VTy) => Pretty m Ctx where
  pretty c =
    intercalate "\n"
      <$> mapM
        ( \(n, ty, tm) -> do
            n' <- pretty n
            ty' <- pretty ty
            tm' <- case tm of
              Just t -> (" = " ++) <$> pretty t
              Nothing -> return ""
            return $ n' ++ " : " ++ ty' ++ tm'
        )
        (reverse con)
    where
      con :: [(Name, CtxTy, Maybe VTm)]
      con =
        zipWith4
          ( \i n t e ->
              ( n,
                t,
                case e of
                  VNeu (VVar x) | x == Lvl i -> Nothing
                  _ -> Just e
              )
          )
          [c.lvl.unLvl - 1, c.lvl.unLvl - 2 .. 0]
          c.nameList
          c.types
          c.env

emptyCtx :: Ctx
emptyCtx =
  Ctx
    { env = [],
      lvl = Lvl 0,
      types = [],
      bounds = [],
      nameList = [],
      names = M.empty
    }

data CtxEntry = CtxEntry
  { name :: Name,
    ty :: CtxTy,
    tm :: VTm,
    lvl :: Lvl,
    bound :: BoundState
  }

bind :: Name -> VTy -> Ctx -> Ctx
bind x ty ctx =
  addCtxEntry
    ( CtxEntry
        { name = x,
          ty = CtxTy ty,
          tm = VNeu (VVar ctx.lvl),
          lvl = ctx.lvl,
          bound = Bound
        }
    )
    ctx

insertedBind :: Name -> VTy -> Ctx -> Ctx
insertedBind = bind

define :: Name -> VTm -> VTy -> Ctx -> Ctx
define x t ty ctx =
  addCtxEntry
    ( CtxEntry
        { tm = t,
          ty = CtxTy ty,
          bound = Defined,
          lvl = ctx.lvl,
          name = x
        }
    )
    ctx

typelessBind :: Name -> Ctx -> Ctx
typelessBind x ctx =
  addCtxEntry
    ( CtxEntry
        { tm = VNeu (VVar ctx.lvl),
          ty = TyUnneeded,
          lvl = ctx.lvl,
          bound = Bound,
          name = x
        }
    )
    ctx

addCtxEntry :: CtxEntry -> Ctx -> Ctx
addCtxEntry e ctx =
  ctx
    { env = e.tm : ctx.env,
      lvl = nextLvl e.lvl,
      types = e.ty : ctx.types,
      bounds = e.bound : ctx.bounds,
      names = M.insert e.name e.lvl ctx.names,
      nameList = e.name : ctx.nameList
    }

typelessBinds :: [Name] -> Ctx -> Ctx
typelessBinds ns ctx = foldr typelessBind ctx (reverse ns)

ensureNeeded :: CtxTy -> VTm
ensureNeeded (CtxTy t) = t
ensureNeeded TyUnneeded = error "Type is unneeded"

lookupName :: Name -> Ctx -> Maybe (Idx, VTy)
lookupName n ctx = case M.lookup n ctx.names of
  Just l -> let idx = lvlToIdx ctx.lvl l in Just (idx, ensureNeeded (ctx.types !! idx.unIdx))
  Nothing -> Nothing

data Goal = Goal
  { ctx :: Ctx,
    tm :: STm,
    ty :: VTy
  }
