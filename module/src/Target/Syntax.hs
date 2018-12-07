{-# LANGUAGE
    DeriveGeneric
  , DeriveDataTypeable
  , FlexibleInstances
  , FlexibleContexts
  , MultiParamTypeClasses
  , ScopedTypeVariables
  , OverloadedStrings #-}

module Target.Syntax where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless
import qualified Data.Text as T
import           Text.PrettyPrint.ANSI.Leijen (Doc, (<+>), text, dot, colon, comma)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Common

type TmName = Name Expr


-- | Syntax of the source language
data Expr = Anno Expr Type
          | Var TmName
          | App Expr Expr
          | Lam (Bind TmName Expr)
          | Pi (Bind (TmName, Embed Type) Expr)
          | Mu (Bind TmName Expr)
          | Star
          | CastUp Expr
          | CastDown Expr
          | Pair Expr Expr
          | PairTy Type Type
          | Proj Int Expr

          | Nat
          | Lit Int
          | PrimOp Operation Expr Expr
  deriving (Show, Generic, Typeable)

type Type = Expr


addExpr :: Expr -> Expr -> Expr
addExpr = PrimOp Add

subExpr :: Expr -> Expr -> Expr
subExpr = PrimOp Sub

multExpr :: Expr -> Expr -> Expr
multExpr = PrimOp Mult


instance Alpha Expr
instance Alpha Operation

instance Subst Expr Operation

instance Subst Expr Expr where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing


-- Examples
{-

-- \ x : ⋆ . \ y : x . y
polyid :: Expr
polyid = elam ("x", estar) (elam ("y", evar "x") (evar "y"))


-- pi x : ⋆ . x -> x
polyidty :: Expr
polyidty = epi ("x", estar) (earr (evar "x") (evar "x"))

-}

-- smart constructors

evar :: String -> Expr
evar = Var . s2n

ebindt :: (String, Type) -> Expr -> Bind (TmName, Embed Type) Expr
ebindt (n, e1) = bind (s2n n, embed e1)

ebind :: String -> Expr -> Bind TmName Expr
ebind n = bind (s2n n)

elam :: String -> Expr -> Expr
elam x e = Lam (ebind x e)

emu :: String -> Expr -> Expr
emu x e = Mu (ebind x e)

epi :: (String, Expr) -> Expr -> Expr
epi b e = Pi (ebindt b e)

earr :: Expr -> Expr -> Expr
earr t1 = epi ("_", t1)

eapp :: Expr -> Expr -> Expr
eapp = App


-- | Pretty printer

class Pretty p where
  ppr :: (Applicative m, LFresh m) => p -> m Doc

instance Pretty Expr where
  ppr (Anno e t) =
    do e' <- ppr e
       t' <- ppr t
       return $ e' <+> colon <+> t'

  ppr (Var x) = return . text . show $ x

  ppr (App e es) = PP.parens <$> ((<+>) <$> ppr e <*> ppr es)

  ppr (Lam bnd) =
    lunbind bnd $
    \(x, b) ->
      do b' <- ppr b
         return (PP.parens $ text "λ" <+> (text . show $ x) <+> dot <+> b')

  ppr Star = return $ PP.char '★'

  ppr (Pi bnd) =
    lunbind bnd $
    \((x,Embed t),b) ->
      do b' <- ppr b
         t' <- ppr t
         if show x == "_"
            then return (PP.parens $ t' <+> text "→" <+> b')
            else return (PP.parens $
                         text "Π" <+>
                         (text . show $ x) <+> colon <+> t' <+> dot <+> b')

  ppr (Mu b) =
    lunbind b $
    \(x, e) ->
      do e' <- ppr e
         return (PP.parens $ text "μ" <+> (text . show $ x) <+> dot <+> e')

  ppr (CastUp e) = (text "cast↑" <+>) <$> ppr e
  ppr (CastDown e) = (text "cast↓" <+>) <$> ppr e

  ppr Nat = return $ text "nat"

  ppr (Lit n) = return . text . show $ n

  ppr (PrimOp op e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       op' <- ppr op
       return $ PP.parens (e1' <+> op' <+> e2')

  ppr (Pair e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       return $ PP.parens (e1' <+> comma <+> e2')

  ppr (PairTy e1 e2) =
    do e1' <- ppr e1
       e2' <- ppr e2
       return $ PP.parens (e1' <+> text "×" <+> e2')

  ppr (Proj i e) =
    do e' <- ppr e
       return $ PP.parens e' <+> text "._" <+> text (show i)

instance Pretty Operation where
  ppr Add = return . text $ "+"
  ppr Mult = return . text $ "*"
  ppr Sub = return . text $ "-"

showExpr :: Expr -> T.Text
showExpr = T.pack . show . runLFreshM . ppr
