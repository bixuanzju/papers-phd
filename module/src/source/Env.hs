{-# LANGUAGE OverloadedStrings, TemplateHaskell, FlexibleContexts #-}

-- | Environment

module Source.Env (lookupTy, runTcMonad, TcMonad, extendCtx) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Unbound.Generics.LocallyNameless

import           Source.Syntax

data Context = Ctx {env :: [(TmName, Type)]}

emptyCtx :: Context
emptyCtx = Ctx []

type TcMonad = FreshMT (ReaderT Context (Except T.Text))


runTcMonad :: TcMonad a -> Either T.Text a
runTcMonad m = runExcept $ runReaderT (runFreshMT m) emptyCtx


lookupTy :: (MonadReader Context m, MonadError T.Text m) => TmName -> m Expr
lookupTy v = do
  x <- lookupTyMaybe v
  case x of
    Nothing  -> throwError $ T.concat ["Not in scope: ", T.pack . show $ v]
    Just res -> return res

lookupTyMaybe :: (MonadReader Context m, MonadError T.Text m) => TmName -> m (Maybe Expr)
lookupTyMaybe v = do
  ctx <- asks env
  return (lookup v ctx)

extendCtx :: (MonadReader Context m) => (TmName, Type) -> m a -> m a
extendCtx d = local (\ctx -> ctx { env = d : env ctx })
