module Interfaces.General
  ( Parent (..),
    HasNameSupply (..),
    Has (..),
    Try (..),
    enterLoc,
  )
where

import Common (Name, Loc)
import Control.Monad.Trans (MonadTrans (..))
import Data.Kind (Type)

class (Monad m) => HasNameSupply m where
  uniqueName :: m Name

class (Monad m) => Has m a where
  view :: m a

  access :: (a -> b) -> m b
  access f = f <$> view

  modify :: (a -> a) -> m ()

  enter :: (a -> a) -> m c -> m c
  enter f m = do
    c <- view
    modify f
    a <- m
    modify (\(_ :: a) -> c)
    return a

  enterLifted :: (MonadTrans t) => (a -> a) -> t m c -> t m c
  enterLifted f m = do
    c <- lift view
    lift $ modify f
    a <- m
    lift $ modify (\(_ :: a) -> c)
    return a

-- | A typeclass for backtracking try
class Try m where
  type E m :: Type
  try :: m a -> m (Either (E m) a)
  giveUp :: E m -> m a

class Parent m where
  -- Run a child computation, don't remember any state changes
  child :: m a -> m a

enterLoc :: (Has m Loc) => Loc -> m a -> m a
enterLoc = enter . const
