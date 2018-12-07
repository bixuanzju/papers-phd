{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

-- | Typechecker

module Source.TypeCheck where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Unbound.Generics.LocallyNameless

import           Source.Syntax
import           Source.Env
import           Common


done :: MonadPlus m => m a
done = mzero


-- | Small step, call-by-value operational semantics
step :: Expr -> MaybeT FreshM Expr
step Var{} = done
step Star = done
step Lam{} = done
step Pi{} = done
step Lit{} = done
step Nat = done

step (Anno e t) = do
  e' <- step e
  return $ Anno e' t

-- HACK
step (App (Anno (Lam bnd) _) t2) = step (App (Lam bnd) t2)
step (App (Lam bnd) t2) = do
  (x, b) <- unbind bnd
  return $ subst x t2 b
step (App t1 t2) =
  App <$> step t1 <*> pure t2
  <|> App <$> pure t1 <*> step t2

step e@(Mu bnd) = do
  (n, b) <- unbind bnd
  return $ subst n e b

step (PrimOp op (Lit n) (Lit m)) = do
  let x = evalOp op
  return (Lit (n `x` m))
step (PrimOp op e1 e2) =
  PrimOp <$> pure op <*> step e1 <*> pure e2
  <|> PrimOp <$> pure op <*> pure e1 <*> step e2

step (CastUp _) = done
step (CastDown e) = CastDown <$> step e

step (Merge e1 e2) =
  Merge <$> step e1 <*> return e2
  <|> Merge <$> return e1 <*> step e2
step (Inter t1 t2) =
  Inter <$> step t1 <*> return t2
  <|> Inter <$> return t1 <*> step t2

evalOp :: Operation -> Int -> Int -> Int
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mult = (*)


-- | transitive closure of `step`
tc :: (Monad m, Functor m) => (a -> MaybeT m a) -> a -> m a
tc f a = do
  ma' <- runMaybeT (f a)
  case ma' of
    Nothing -> return a
    Just a' -> tc f a'


eval :: Expr -> Expr
eval x = runFreshM (tc step x)


-- | type checker with positivity and contractiveness test
typecheck :: Expr -> Either T.Text Type
typecheck = runTcMonad . infer


check :: Expr -> Type -> TcMonad ()
check (Lam bnd) t = do
  (x, body) <- unbind bnd
  tbnd <- unPi t
  ((y, Embed t1), t2) <- unbind tbnd
  extendCtx (x, t1) (check body (subst y (Var x) t2))
check (Mu bnd) t = do
  (x, body) <- unbind bnd
  extendCtx (x, t) (check body t)
check (CastUp e) t =
  check e =<< oneStep t
check e t = do
  t' <- infer e
  checkEq t t'


infer :: Expr -> TcMonad Type
infer (Anno e t) = do
  check t Star
  check e t
  return t
infer (Var x) = lookupTy x
infer Star = return Star
infer (App f a) = do
  bnd <- unPi =<< infer f
  ((x, Embed t), body) <- unbind bnd
  check a t
  return (subst x a body)
infer (Pi bnd) = do
  ((x, Embed t), body) <- unbind bnd
  check t Star
  extendCtx (x, t) (check body Star)
  return Star
infer Nat = return Star
infer (Lit _) = return Nat
infer (PrimOp _ e1 e2) = do
  check e1 Nat
  check e2 Nat
  return Nat
infer (CastDown e) = oneStep =<< infer e
infer (Merge e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  return $ Inter t1 t2
infer (Inter t1 t2) = do
  check t1 Star
  check t2 Star
  return Star
infer e = throwError $ T.concat ["Type checking ", showExpr e, " failed"]


oneStep :: (MonadError T.Text m) => Expr -> m Expr
oneStep e =
  case runFreshM . runMaybeT $ step e of
    Nothing -> throwError $ T.concat ["Cannot reduce ", showExpr e]
    Just e' -> return e'


-- | alpha equality
checkEq :: Expr -> Expr -> TcMonad ()
checkEq e1 e2 =
  unless (aeq e1 e2) $ throwError $
    T.concat ["Couldn't match: ", showExpr e1, " with ", showExpr e2]


unPi :: MonadError T.Text m => Expr -> m (Bind (TmName, Embed Type) Expr)
unPi (Pi bnd) = return bnd
unPi e = throwError $ T.concat ["Expected pi type, got ", showExpr e, " instead"]
