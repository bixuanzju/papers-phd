{-# LANGUAGE OverloadedStrings, FlexibleContexts #-}

-- | Typechecker

module Target.TypeCheck where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Trans.Maybe
import qualified Data.Text as T
import           Unbound.Generics.LocallyNameless

import           Target.Syntax
import           Target.Env
import           Common


done :: MonadPlus m => m a
done = mzero


removeAnno :: Expr -> Expr
removeAnno (Anno e _) = removeAnno e
removeAnno e = e


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

step (App f a) =
  case removeAnno f of
    (Lam bnd) -> do
      (x, b) <- unbind bnd
      return $ subst x a b
    _ -> App <$> step f <*> pure a <|> App <$> pure f <*> step a

step e@(Mu bnd) = do
  (n, b) <- unbind bnd
  return $ subst n e b

step (PrimOp op e1 e2) =
  case (removeAnno e1, removeAnno e2) of
    (Lit n, Lit m) -> do
      let x = evalOp op
      return (Lit (n `x` m))
    _ -> PrimOp <$> pure op <*> step e1 <*> pure e2 <|> PrimOp <$> pure op <*> pure e1 <*> step e2

step (CastUp _) = done
step (CastDown e) = CastDown <$> step e

step (Pair e1 e2) =
  Pair <$> step e1 <*> return e2
  <|> Pair <$> return e1 <*> step e2
step (PairTy t1 t2) =
  PairTy <$> step t1 <*> return t2
  <|> PairTy <$> return t1 <*> step t2
step (Proj i e) =
  case removeAnno e of
    (Pair e1 e2) -> return $ if i == 0 then e1 else e2
    _ -> Proj <$> pure i <*> step e


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
infer (Pair e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  return $ PairTy t1 t2
infer (PairTy t1 t2) = do
  check t1 Star
  check t2 Star
  return Star
infer (Proj i e) = do
  t <- infer e
  case t of
    (PairTy t1 t2) -> return $ if i == 0 then t1 else t2
    _ -> throwError $ T.concat [showExpr e, " is not a pair"]
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
