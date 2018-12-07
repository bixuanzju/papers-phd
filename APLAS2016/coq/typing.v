Require Import definitions.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module Typing
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.

  (* Static semantics (call-by-name) *)

  Inductive plain_value : TExp -> Prop :=
  | pvalue_tstar : plain_value TStar
  | pvalue_tlam : forall t1 t2,
      term_target (TLam t1 t2) -> plain_value (TLam t1 t2)
  | pvalue_tpi : forall t1 t2,
      term_target (TPi t1 t2) -> plain_value (TPi t1 t2).
    
  Inductive value_target : TExp -> Prop :=
  | value_pvalue : forall u, plain_value u -> value_target u
  | value_tcastup : forall t u,
      plain_value u -> value_target (TCastup t u)
  | value_tcastdn : forall t u,
      plain_value u -> value_target (TCastdn t u).

  Hint Constructors value_target plain_value.

  (* weak-head reduction call-by-name for the target *)
  
  Inductive whred : TExp -> TExp -> Prop :=
  | whred_beta : forall t t1 t2,
                 term_target (TLam t t1) -> whred (TApp (TLam t t1) t2) (open_target t1 t2)
  | whred_app : forall t1 t1' t2,
                 term_target t2 ->
                 whred t1 t1' ->
                 whred (TApp t1 t2) (TApp t1' t2)
  | whred_castdn : forall t e e',
                   whred e e' ->
                   whred (TCastdn t e) (TCastdn t e')
  | whred_castup : forall t e e',
                   whred e e' ->
                   whred (TCastup t e) (TCastup t e')
  | whred_castupbeta : forall t1 e1 e2 t1' t2',
      term_target (TCastup (TPi t1' t2') (TLam t1 e1)) ->
      whred (TApp (TCastup (TPi t1' t2') (TLam t1 e1)) e2)
            (TApp (TLam t1' (TCastup t2' e1)) (TCastdn t1' e2))
  | whred_castdnbeta : forall t1 e1 e2 t1' t2',
      term_target (TCastdn (TPi t1' t2') (TLam t1 e1)) ->
      whred (TApp (TCastdn (TPi t1' t2') (TLam t1 e1)) e2)
            (TApp (TLam t1' (TCastdn t2' e1)) (TCastup t1' e2))
  | whred_mu : forall t e,
      whred (TMu t e) (open_target e (TMu t e)).

  (* Parallel reduction *)

  Inductive pared : TExp -> TExp -> Prop :=
  | pared_refl : forall e, pared e e
  | pared_lam : forall t t' e e',
      pared t t' -> pared e e' ->
      pared (TLam t e) (TLam t' e')
  | pared_pi : forall t1 t1' t2 t2',
      pared t1 t1' -> pared t2 t2' ->
      pared (TPi t1 t2) (TPi t1' t2')
  | pared_app : forall e1 e1' e2 e2',
      pared e1 e1' -> pared e2 e2' ->
      pared (TApp e1 e2) (TApp e1' e2')
  | pared_appbeta : forall t e1 e1' e2 e2',
      term_target (TLam t e1) -> pared e1 e1' -> pared e2 e2' ->
      pared (TApp (TLam t e1) e2) (open_target e1' e2')
  | pared_mu : forall t t' e e',
      pared t t' -> pared e e' -> pared (TMu t e) (TMu t' e')
  | pared_mubeta : forall t t' e e',
      pared t t' -> pared e e' -> pared (TMu t e) (open_target e' (TMu t' e'))
  | pared_castup : forall t e e',
      pared e e' -> pared (TCastup t e) e'
  | pared_castdn : forall t e e',
      pared e e' -> pared (TCastdn t e) e'.

  Hint Constructors whred.

  Notation "t ~~> t'" := (pared t t') (at level 68).

  Hint Constructors value_target.
  
  Definition pared_equiv (e1 : TExp) (e2 : TExp) : Prop := pared e1 e2 \/ pared e2 e1.

  (* =======================
     Typing: T |- A : B
     =======================
  *)

  Inductive has_type_target : context TExp -> TExp -> TExp -> Prop :=
  | Ty2Star : forall Gamma,
      wfs2 Gamma ->
      has_type_target Gamma TStar TStar
  | Ty2Var : forall Gamma x ty,
      wfs2 Gamma ->
      List.In (x, ty) Gamma ->
      has_type_target Gamma (TFVar x) ty
  | Ty2Lam : forall L Gamma A B t,
      (forall x, not (In x L) ->
                 has_type_target (extend x A Gamma)
                                 (open_target t (TFVar x))
                                 (open_target B (TFVar x))) ->
      has_type_target Gamma (TLam A t) (TPi A B)
  | Ty2Mu : forall L Gamma A t,
      has_type_target Gamma A TStar ->
      (forall x, not (In x L) ->
                 has_type_target (extend x A Gamma)
                                 (open_target t (TFVar x))
                                 (open_target A (TFVar x))) ->
      has_type_target Gamma (TMu A t) A                      
  | Ty2App : forall Gamma E1 E2 A B,
      has_type_target Gamma E1 (TPi A B) ->
      has_type_target Gamma E2 A ->
      has_type_target Gamma (TApp E1 E2) (open_target B E2) 
  | Ty2Pi : forall Gamma L A B,
      has_type_target Gamma A TStar ->
      (forall x, not (In x L) ->
                 has_type_target (extend x A Gamma)
                                 (open_target B (TFVar x))
                                 TStar) ->
      has_type_target Gamma (TPi A B) TStar
  | Ty2CastDown : forall Gamma A B C,
      has_type_target Gamma C TStar ->
      has_type_target Gamma A B ->
      B ~~> C ->
      has_type_target Gamma (TCastdn C A) C
  | Ty2CastUp : forall Gamma A B C,
      has_type_target Gamma B TStar ->
      has_type_target Gamma A C ->
      B ~~> C ->
      has_type_target Gamma (TCastup B A) B
  with wfs2 : context TExp -> Prop :=
  | wfs2_nil : wfs2 nil
  | wfs2_cons : forall E x U ,
      not (In x (dom E)) ->
      has_type_target E U TStar ->
      wfs2 (extend x U E).

End Typing.
