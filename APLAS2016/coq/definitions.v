Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module ExprDefs
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Definition var : Type := VarTyp.t.

  Module M := MSetWeakList.Make(VarTyp).
  Export M.

  Definition vars := M.t.

  Module EqFacts := BoolEqualityFacts(VarTyp).

  Definition context (A : Type) := list (var * A).

  Definition extend {A} (x : var) (a : A) (c : context A) : context A :=
    ((x,a) :: nil) ++ c.

  Fixpoint dom {A} (c : context A) : vars :=
    match c with
    | nil => empty
    | el :: cs => add (fst el) (dom cs)
    end.

  (* Core language: Calculus of constructions with explicit casts *)

  Inductive TExp :=
  | TStar : TExp
  | TBVar : nat -> TExp
  | TFVar : var -> TExp
  | TLam : TExp -> TExp -> TExp
  | TMu : TExp -> TExp -> TExp
  | TApp : TExp -> TExp -> TExp
  | TCastdn : TExp -> TExp -> TExp
  | TCastup : TExp -> TExp -> TExp
  | TPi : TExp -> TExp -> TExp.

  Hint Constructors TExp.

  Fixpoint open_rec_target (k : nat) (u : TExp) (t : TExp) {struct t} : TExp :=
    match t with
      | TStar =>  TStar
      | TBVar i => if Nat.eqb k i then u else (TBVar i)
      | TFVar x => TFVar x
      | TLam t1 t2 => TLam (open_rec_target (S k) u t1) (open_rec_target k u t2)
      | TMu t1 t2 => TMu (open_rec_target (S k) u t1) (open_rec_target k u t2)
      | TApp t1 t2 => TApp (open_rec_target k u t1) (open_rec_target k u t2)
      | TCastdn t1 t2 => TCastdn (open_rec_target k u t1) (open_rec_target k u t2)
      | TCastup t1 t2 => TCastup (open_rec_target k u t1) (open_rec_target k u t2)
      | TPi t1 t2 => TPi (open_rec_target k u t1) (open_rec_target k u t2)
    end.

  Definition open_target t u := open_rec_target 0 u t.

  Fixpoint close_var_rec (k : nat) (z : var) (t : TExp) {struct t} : TExp :=
    match t with
      | TStar => TStar
      | TBVar i => TBVar i
      | TFVar x => if VarTyp.eqb x z then (TBVar k) else (TFVar x)
      | TLam t1 t2 => TLam (close_var_rec k z t1) (close_var_rec (S k) z t2)
      | TMu t1 t2 => TMu (close_var_rec k z t1) (close_var_rec (S k) z t2)
      | TApp t1 t2 => TApp (close_var_rec k z t1) (close_var_rec k z t2)
      | TCastup t1 t2 => TCastup (close_var_rec k z t1) (close_var_rec k z t2)
      | TCastdn t1 t2 => TCastdn (close_var_rec k z t1) (close_var_rec k z t2)
      | TPi t1 t2 => TPi (close_var_rec k z t1) (close_var_rec (S k) z t1)
    end.

  Definition close_var z t := close_var_rec 0 z t.

(* Local closure *)

  Inductive term_target : TExp -> Prop :=
  | term_tstar : term_target TStar
  | term_tfvar : forall x, term_target (TFVar x)
  | term_tlam : forall L t1 t2,
      term_target t1 ->
      (forall x, not (In x L) -> term_target (open_target t1 (TFVar x))) ->
      term_target (TLam t1 t2)
  | term_tmu : forall L t1 t2,
      term_target t1 ->
      (forall x, not (In x L) -> term_target (open_target t1 (TFVar x))) ->
      term_target (TMu t1 t2)
  | term_tapp : forall t1 t2,
      term_target t1 -> term_target t2 -> term_target (TApp t1 t2)
  | term_tcastdn : forall t1 t2,
      term_target t1 -> term_target t2 -> term_target (TCastdn t1 t2)
  | term_tcastup : forall t1 t2,
      term_target t1 -> term_target t2 -> term_target (TCastup t1 t2)
  | term_tpi : forall L t1 t2,
      term_target t1 ->
      (forall x, not (In x L) -> term_target (open_target t2 (TFVar x))) ->
      term_target (TPi t1 t2).

  Hint Constructors term_target.
  
   Fixpoint subst_target (z : var) (u : TExp) (t : TExp) {struct t} : TExp :=
    match t with
      | TStar => TStar
      | TBVar i => TBVar i
      | TFVar x => if VarTyp.eqb x z then u else (TFVar x)
      | TLam t1 t2 => TLam (subst_target z u t1) (subst_target z u t2)
      | TMu t1 t2 => TMu (subst_target z u t1) (subst_target z u t2)
      | TApp t1 t2 => TApp (subst_target z u t1) (subst_target z u t2)
      | TCastup t1 t2 => TCastup (subst_target z u t1) (subst_target z u t2)
      | TCastdn t1 t2 => TCastdn (subst_target z u t1) (subst_target z u t2)
      | TPi t1 t2 => TPi (subst_target z u t1) (subst_target z u t2)
    end.

  (* Target language *)
  Fixpoint fv (tExp : TExp) : vars :=
    match tExp with
      | TStar => empty
      | TBVar _ => empty
      | TFVar x => singleton x
      | TLam t1 t2 => union (fv t1) (fv t2)
      | TMu t1 t2 => union (fv t1) (fv t2)
      | TApp t1 t2 => union (fv t1) (fv t2)
      | TCastup t1 t2 => union (fv t1) (fv t2)
      | TCastdn t1 t2 => union (fv t1) (fv t2)
      | TPi t1 t2 => union (fv t1) (fv t2)
    end.

End ExprDefs.
