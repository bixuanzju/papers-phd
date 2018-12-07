{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Translation where

import           Control.Monad.Except
import           Control.Monad.Trans.Maybe
import           Control.Applicative ((<|>))
import qualified Data.Text
import           Source.Env
import           Source.Syntax                    as S
import           Source.TypeCheck                 (checkEq, oneStep, unPi)
import           Target.Syntax                    as T
import           Unbound.Generics.LocallyNameless


idFunc :: T.Expr
idFunc = T.elam "x" (T.evar "x")


subtyping :: S.Expr -> S.Expr -> MaybeT TcMonad T.Expr
subtyping a b = do
  (_, ta) <- lift $ trans a
  (_, tb) <- lift $ trans b
  let t = T.earr ta tb
  f <- subty a b
  MaybeT $ return $ Just $
    case f of (T.Anno e _) -> T.Anno e t
              e -> T.Anno e t
  where
    subty :: S.Expr -> S.Expr -> MaybeT TcMonad T.Expr

    subty (S.Anno e1 _) e2 = subty e1 e2
    subty e1 (S.Anno e2 _) = subty e1 e2

    subty (S.Var x) (S.Var y) =
      if x == y then return idFunc else MaybeT $ return Nothing

    subty S.Star S.Star = return idFunc

    subty (S.Pi b1) (S.Pi b2) = do
      ((x1, Embed t1), body1) <- unbind b1
      ((x2, Embed t2), body2) <- unbind b2
      c1 <- subtyping t2 t1
      c2 <- subtyping body1 (subst x2 (S.Var x1) body2)
      return $ T.elam "f" (T.elam "x" (T.App c2 (T.App (T.evar "f") (T.App c1 (T.evar "x")))))

    subty (S.Lam b1) (S.Lam b2) = do
      (x1, body1) <- unbind b1
      (x2, body2) <- unbind b2
      c <- subtyping body1 (subst x2 (S.Var x1) body2)
      return $ T.elam "x" (T.CastUp $ T.App c (T.CastDown $ T.evar "x"))

    subty (S.Mu _) (S.Mu _) = undefined

    subty (S.App f1 e1) (S.App f2 e2) =
      if aeq e1 e2
        then subty f1 f2
        else MaybeT $ return Nothing

    subty (S.CastUp e1) (S.CastUp e2) = subty e1 e2
    subty (S.CastDown e1) (S.CastDown e2) = subty e1 e2

    subty S.Nat S.Nat = return idFunc

    subty (S.Inter t1 t2) t =
      let
        f1 = do c1 <- subtyping t1 t
                return $ T.elam "x" (T.App c1 (T.Proj 0 (T.evar "x")))
        f2 = do c2 <- subtyping t2 t
                return $ T.elam "x" (T.App c2 (T.Proj 1 (T.evar "x")))
      in
      f1 <|> f2

    subty t (S.Inter t1 t2) = do
       c1 <- subtyping t1 t
       c2 <- subtyping t2 t
       let app e v = T.App e (T.evar v)
       return $ T.elam "x" (T.Pair (app c1 "x") (app c2 "x"))

    subty _ _ = MaybeT $ return Nothing



translate :: S.Expr -> Either Data.Text.Text (S.Type, T.Expr)
translate = runTcMonad . trans


trans :: S.Expr -> TcMonad (S.Type, T.Expr)
trans expr = case expr of
  (S.Anno e t) -> do
    t' <- check t S.Star
    e' <- check e t
    return (t, T.Anno e' t')
  (S.Var x) -> do
    t <- lookupTy x
    return (t, T.evar $ show x)
  S.Star -> return (S.Star, T.Star)
  (S.App f a) -> do
    (ft, f') <- trans f
    bnd <- unPi ft
    ((x, Embed t), body) <- unbind bnd
    a' <- check a t
    return (subst x a body, T.App f' a')
  (S.Pi bnd) -> do
    ((x, Embed t), body) <- unbind bnd
    t' <- check t S.Star
    body' <- extendCtx (x, t) (check body S.Star)
    return (S.Star, T.epi (show x, t') body')
  S.Nat -> return (S.Star, T.Nat)
  (S.Lit l) -> return (S.Nat, T.Lit l)
  (S.PrimOp op e1 e2) -> do
    e1' <- check e1 S.Nat
    e2' <- check e2 S.Nat
    return (S.Nat, T.PrimOp op e1' e2')
  (S.CastDown e) -> do
    (t, e') <- trans e
    t' <- oneStep t
    return (t', T.CastDown e')
  (S.Merge e1 e2) -> do
    (t1, e1') <- trans e1
    (t2, e2') <- trans e2
    return (Inter t1 t2, T.Pair e1' e2')
  (S.Inter t1 t2) -> do
    t1' <- check t1 S.Star
    t2' <- check t2 S.Star
    return (S.Star, T.PairTy t1' t2')
  _ -> throwError $ Data.Text.concat ["Type checking ", S.showExpr expr, " failed"]
  where
    check :: S.Expr -> S.Type -> TcMonad T.Expr
    check (S.Lam bnd) t = do
      (x, body) <- unbind bnd
      tbnd <- unPi t
      ((y, Embed t1), t2) <- unbind tbnd
      body' <- extendCtx (x, t1) (check body (subst y (S.Var x) t2))
      return $ T.elam (show x) body'
    check (S.Mu bnd) t = do
      (x, body) <- unbind bnd
      body' <- extendCtx (x, t) (check body t)
      return $ T.emu (show x) body'
    check (S.CastUp e) t = do
      e' <- check e =<< oneStep t
      return $ T.CastUp e'
    check e t = do
      (t2, e') <- trans e
      do {checkEq t t2; return e'}
        `catchError`
        (\err -> do cf <- runMaybeT $ subtyping t2 t
                    case cf of
                      Just c -> return $ T.App c e'
                      Nothing -> throwError err)
