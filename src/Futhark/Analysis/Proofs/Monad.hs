{-# OPTIONS_GHC -Wno-orphans #-}

module Futhark.Analysis.Proofs.Monad
  ( VEnv,
    IndexFnM (..),
    runIndexFnM,
    insertIndexFn,
    insertTopLevel,
    clearAlgEnv,
    whenDebug,
    debugM,
    debugT,
    debugT',
    debugPrettyM,
    debugPrintAlgEnv,
    debugOn,
    withDebug,
    withoutDebug,
    rollbackAlgEnv,
    getIndexFns,
    getTopLevelIndexFns,
    modifyMem,
    getMem,
    remember,
    forget,
    prettyStr,
    -- withPreludeEffects,
    -- getUsePreludeEffects,
    warningString,
  )
where

import Control.Monad (when)
import Control.Monad.RWS.Strict
import Data.Map qualified as M
import Debug.Trace (traceM)
import Futhark.Analysis.Proofs.AlgebraPC.Algebra qualified as Algebra
import Futhark.Analysis.Proofs.IndexFn
import Futhark.Analysis.Proofs.Symbol
import Futhark.MonadFreshNames
import Futhark.SoP.Expression (Expression (..))
import Futhark.SoP.Monad (AlgEnv (..), MonadSoP (..))
import Futhark.Util.Pretty (Pretty, docStringW, pretty, prettyString)
import Language.Futhark (VName)
import Language.Futhark qualified as E

data IndexFnProperty
  = Blah
  deriving (Show, Eq, Ord)

data VEnv = VEnv
  { vnamesource :: VNameSource,
    algenv :: AlgEnv Algebra.Symbol Symbol Algebra.Property,
    indexfns :: M.Map VName [IndexFn],
    toplevel :: M.Map VName ([E.Pat E.ParamType], [IndexFn]),
    mem :: M.Map Symbol VName,
    -- usePreludeEffects :: Bool,
    debug :: Bool
  }

newtype IndexFnM a = IndexFnM (RWS () () VEnv a)
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadFreshNames,
      MonadState VEnv
    )

instance (Monoid w) => MonadFreshNames (RWS r w VEnv) where
  getNameSource = gets vnamesource
  putNameSource vns = modify $ \senv -> senv {vnamesource = vns}

-- TODO Remove Expression constraint from MonadSoP, if these are unused.
-- See, for example, RefineEquivs.
instance Expression Symbol where
  moduloIsh _ = Nothing
  divInsteadOfMod = undefined
  processExp = undefined

instance MonadSoP Algebra.Symbol Symbol Algebra.Property IndexFnM where
  getUntrans = gets (untrans . algenv)
  getRanges = gets (ranges . algenv)
  getEquivs = gets (equivs . algenv)
  getProperties = gets (properties . algenv)
  modifyEnv f = modify $ \env -> env {algenv = f $ algenv env}
  findSymLEq0 = Algebra.findSymbolLEq0

getIndexFns :: IndexFnM (M.Map VName [IndexFn])
getIndexFns = gets indexfns

getTopLevelIndexFns :: IndexFnM (M.Map VName ([E.Pat E.ParamType], [IndexFn]))
getTopLevelIndexFns = gets toplevel

-- getUsePreludeEffects :: IndexFnM Bool
-- getUsePreludeEffects =
--   gets usePreludeEffects

-- -- Enables checks on special prelude functions
-- -- that behave differently during refinement checking.
-- withPreludeEffects :: MonadState VEnv m => m b -> m b
-- withPreludeEffects m = do
--   b <- gets usePreludeEffects
--   modify (\s -> s {usePreludeEffects = True})
--   res <- m
--   modify (\s -> s {usePreludeEffects = b})
--   pure res

runIndexFnM :: IndexFnM a -> VNameSource -> (a, M.Map VName [IndexFn])
runIndexFnM (IndexFnM m) vns = getRes $ runRWS m () s
  where
    getRes (x, env, _) = (x, indexfns env)
    s = VEnv vns mempty mempty mempty mempty False

modifyMem :: (MonadState VEnv m) => Symbol -> VName -> m ()
modifyMem vn x = do
  modify $
    \env -> env {mem = M.insert vn x (mem env)}

remember :: (MonadState VEnv m, MonadFreshNames m) => Symbol -> m VName
remember x = do
  m <- gets mem
  case m M.!? x of
    Nothing -> do
      vn <- newVName ("<" <> prettyString x <> ">")
      modifyMem x vn
      pure vn
    Just vn -> pure vn

getMem :: IndexFnM (M.Map Symbol VName)
getMem = gets mem

forget :: IndexFnM a -> IndexFnM a
forget computation = do
  m <- getMem
  res <- computation
  modify (\env -> env {mem = m})
  pure res

insertIndexFn :: E.VName -> [IndexFn] -> IndexFnM ()
insertIndexFn x v =
  modify $ \env -> env {indexfns = M.insert x v $ indexfns env}

insertTopLevel :: E.VName -> ([E.Pat E.ParamType], [IndexFn]) -> IndexFnM ()
insertTopLevel vn (args, fns) =
  modify $
    \env -> env {toplevel = M.insert vn (args, fns) $ toplevel env}

clearAlgEnv :: IndexFnM ()
clearAlgEnv =
  modify $ \env -> env {algenv = mempty}

rollbackAlgEnv :: IndexFnM a -> IndexFnM a
rollbackAlgEnv computation = do
  alg <- gets algenv
  res <- computation
  modify (\env -> env {algenv = alg})
  pure res

--------------------------------------------------------------
-- Utilities
--------------------------------------------------------------
whenDebug :: IndexFnM () -> IndexFnM ()
whenDebug x = do
  debug <- gets debug
  when debug x

debugM :: String -> IndexFnM ()
debugM x = do
  whenDebug $ traceM x

debugT :: (Show a) => String -> IndexFnM a -> IndexFnM a
debugT msg m = do
  a <- m
  debugM (msg <> ": " <> show a)
  pure a

debugT' :: (Pretty a) => String -> IndexFnM a -> IndexFnM a
debugT' msg m = do
  a <- m
  debugM (msg <> ": " <> prettyString a)
  pure a

debugPrettyM :: (Pretty a) => String -> a -> IndexFnM ()
debugPrettyM msg x = do
  whenDebug $ traceM $ docStringW 110 $ "🪲 " <> pretty msg <> " " <> pretty x

prettyStr :: Pretty a => a -> String
prettyStr x = docStringW 110 (pretty x)

debugPrintAlgEnv :: IndexFnM ()
debugPrintAlgEnv = do
  algenv <- gets algenv
  debugPrettyM "" algenv

debugOn :: IndexFnM ()
debugOn = do
  modify (\s -> s {debug = True})

withDebug :: IndexFnM b -> IndexFnM b
withDebug f = do
  debugOn
  f

withoutDebug :: IndexFnM b -> IndexFnM b
withoutDebug f = do
  toggle <- gets debug
  modify (\s -> s {debug = False})
  x <- f
  modify (\s -> s {debug = toggle})
  pure x

warningString :: String -> String
warningString s = "\ESC[93m" <> s <> "\ESC[0m"
