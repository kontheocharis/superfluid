module Checking.Utils (runTc, showSolvedMetas, showHole, showContext) where

import Checking.Context (Tc, TcState, emptyTcState, inCtx, metaValues)
import Checking.Errors (TcError)
import Checking.Normalisation (fillAllMetasAndNormalise)
import Control.Monad.Error.Class (MonadError (catchError), throwError)
import Control.Monad.State (gets, runStateT)
import Data.List (intercalate)
import Data.Map (toList)
import Debug.Trace (traceM)
import Interface.Pretty (Print (..), indentedFst)
import Lang (Term, Type)

-- | Run a typechecking computation.
runTc :: Tc a -> Either TcError (a, TcState)
runTc tc = do
  runStateT
    ( catchError
        tc
        ( \e -> do
            e' <- fillAllMetasAndNormalise e
            throwError e'
        )
    )
    emptyTcState

showSolvedMetas :: Tc ()
showSolvedMetas = do
  m <- gets (\s -> s.metaValues)
  traceM $ "Solved metas:\n" ++ intercalate "\n" (map (\(m', t) -> printVal m' ++ " := " ++ printVal t) (toList m))

showContext :: Tc ()
showContext = do
  c <- inCtx id
  cNorm <- fillAllMetasAndNormalise c
  traceM $ "Context:\n" ++ indentedFst (show cNorm)

showHole :: Term -> Maybe Type -> Tc ()
showHole h ty = do
  ty'' <- case ty of
    Just ty' -> Just <$> fillAllMetasAndNormalise ty'
    Nothing -> return Nothing
  traceM $
    "Hole: " ++ printVal h ++ case ty'' of
      Just ty' -> do
        " : " ++ printVal ty'
      Nothing -> ""
  showContext
