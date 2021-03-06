(***************************************************************************
* FullCast - Infrastructure                                                *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN FullCast_Definitions.


(* ********************************************************************** *)
(** ** Additional Definitions Used in the Proofs *)

(* ********************************************************************** *)
(** Computing free variables of a term *)

Fixpoint fv (t : src) {struct t} : vars :=
  match t with
  | src_bvar i     => \{}
  | src_fvar x     => \{x}
  | src_star       => \{}
  | src_app t1 t2  => (fv t1) \u (fv t2)
  | src_abs t1 t2  => (fv t1) \u (fv t2)
  | src_prod t1 t2 => (fv t1) \u (fv t2)
  | src_mu t1 t2  => (fv t1) \u (fv t2)
  | src_castup t1 t2  => (fv t1) \u (fv t2)
  | src_castdn t1 t2 => (fv t1) \u (fv t2)
  end.

(* ********************************************************************** *)
(** Substitution for a name *)

Fixpoint subst (z : var) (u : src) (t : src) {struct t} : src :=
  match t with
  | src_bvar i     => src_bvar i 
  | src_fvar x     => If x = z then u else (src_fvar x)
  | src_star     => src_star
  | src_app t1 t2  => src_app (subst z u t1) (subst z u t2)
  | src_abs t1 t2  => src_abs (subst z u t1) (subst z u t2)
  | src_prod t1 t2 => src_prod (subst z u t1) (subst z u t2)
  | src_mu t1 t2  => src_mu (subst z u t1) (subst z u t2)
  | src_castup t1 t2  => src_castup (subst z u t1) (subst z u t2)
  | src_castdn t1 t2 => src_castdn (subst z u t1) (subst z u t2)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

(* ********************************************************************** *)
(** Abstracting a name out of a term *)

Fixpoint close_var_rec (k : nat) (z : var) (t : src) {struct t} : src :=
  match t with
  | src_bvar i     => src_bvar i 
  | src_fvar x     => If x = z then (src_bvar k) else (src_fvar x)
  | src_star       => src_star
  | src_app t1 t2  => src_app (close_var_rec k z t1) (close_var_rec k z t2)
  | src_abs t1 t2  => src_abs (close_var_rec k z t1) (close_var_rec (S k) z t2) 
  | src_prod t1 t2 => src_prod (close_var_rec k z t1) (close_var_rec (S k) z t2)
  | src_mu t1 t2 => src_mu (close_var_rec k z t1) (close_var_rec (S k) z t2)                               
  | src_castup t1 t2  => src_castup (close_var_rec k z t1) (close_var_rec k z t2)
  | src_castdn t1 t2 => src_castdn (close_var_rec k z t1) (close_var_rec k z t2)
  end.

Definition close_var z t := close_var_rec 0 z t.

(* ********************************************************************** *)
(** An environment contains only terms *)

Definition contains_terms E :=
  forall x U, binds x U E -> termsrc U.

(* ********************************************************************** *)
(** Inclusion between relations (simulation or a relation by another) *)

Definition simulated (R1 R2 : relsrc) := 
  forall (t t' : src), R1 t t' -> R2 t t'.
 
Infix "simulated_by" := simulated (at level 69).

(* ********************************************************************** *)
(** Properties of relations *)

Definition red_regular (R : relsrc) :=
  forall t t', R t t' -> termsrc t /\ termsrc t'.

Definition red_refl (R : relsrc) :=
  forall t, termsrc t -> R t t.

Definition red_in (R : relsrc) :=
  forall t x u u', termsrc t -> R u u' ->
  R ([x ~> u]t) ([x ~> u']t).
  
Definition red_all (R : relsrc) :=
  forall x t t', R t t' -> 
  forall u u', R u u' -> 
  R ([x~>u]t) ([x~>u']t').

Definition red_out (R : relsrc) :=
  forall x u t t', termsrc u -> R t t' -> 
  R ([x~>u]t) ([x~>u]t').

Definition red_rename (R : relsrc) :=
  forall x t t' y,
  R (t ^ x) (t' ^ x) -> 
  x \notin (fv t) -> x \notin (fv t') ->
  R (t ^ y) (t' ^ y).

Definition red_through (R : relsrc) :=
  forall x t1 t2 u1 u2, 
  x \notin (fv t1) -> x \notin (fv u1) ->
  R (t1 ^ x) (u1 ^ x) -> R t2 u2 ->
  R (t1 ^^ t2) (u1 ^^ u2).


(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : src => fv x) in
  let D := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

Ltac exists_fresh := 
  let L := gather_vars_with (fun x : vars => x) in exists L.

Scheme typsrc_induct := Induction for typsrc Sort Prop
  with wf_induct := Induction for wf Sort Prop.

Hint Constructors typsrc wf.

(* ********************************************************************** *)
(** ** Lemmas *)

(* ********************************************************************** *)
(** Properties of substitutions *)

Section SubstProperties.

Hint Constructors termsrc.

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_termsrc_core :forall e j v i u, i <> j ->
  {j ~> v}e = {i ~> u}({j ~> v}e) -> e = {i ~> u}e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  termsrc t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open. pick_fresh x.
   apply* (@open_rec_termsrc_core t2 0 (src_fvar x)).
  unfolds open. pick_fresh x. 
   apply* (@open_rec_termsrc_core t2 0 (src_fvar x)).
  unfolds open. pick_fresh x. 
   apply* (@open_rec_termsrc_core t2 0 (src_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> [x ~> u] t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. 
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, termsrc u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u e, y <> x -> termsrc u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> termsrc u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.

End SubstProperties.

(** Tactic to permute subst and open var *)

Ltac cross := 
  rewrite subst_open_var; try cross.

Tactic Notation "cross" "*" := 
  cross; autos*.


(* ********************************************************************** *)
(** Lifting operations to terms *)

Hint Constructors termsrc.

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  termsrc u -> termsrc t -> termsrc ([z ~> u]t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* termsrc_abs as y. rewrite* subst_open_var.
  apply_fresh* termsrc_prod as y. rewrite* subst_open_var.
  apply_fresh* termsrc_mu as y. rewrite* subst_open_var.
Qed.

(** Terms are stable by open *)

Lemma open_term : forall t u,
  bodysrc t -> termsrc u -> termsrc (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@subst_intro y). apply* subst_term.
Qed.

Hint Resolve subst_term open_term.


(* ********************************************************************** *)
(** Properties of body *)

Lemma termsrc_abs1 : forall t2 t1,
  termsrc (src_abs t1 t2) -> termsrc t1.
Proof.
  intros. inversion* H.
Qed.

Lemma bodysrc_abs2 : forall t1 t2,  
  termsrc (src_abs t1 t2) -> bodysrc t2.
Proof.
  intros. unfold bodysrc. inversion* H.
Qed.

Lemma termsrc_prod1 : forall t2 t1,
  termsrc (src_prod t1 t2) -> termsrc t1.
Proof.
  intros. inversion* H.
Qed.

Lemma bodysrc_prod2 : forall t1 t2,  
  termsrc (src_prod t1 t2) -> bodysrc t2.
Proof.
  intros. unfold bodysrc. inversion* H.
Qed.

Lemma termsrc_mu1 : forall t2 t1,
  termsrc (src_mu t1 t2) -> termsrc t1.
Proof.
  intros. inversion* H.
Qed.

Lemma bodysrc_mu2 : forall t1 t2,  
  termsrc (src_mu t1 t2) -> bodysrc t2.
Proof.
  intros. unfold bodysrc. inversion* H.
Qed.

Hint Extern 1 (termsrc ?t) =>
match goal with
  | H: termsrc (src_abs t ?t2) |- _ => apply (@termsrc_abs1 t2)
  | H: termsrc (src_prod t ?t2) |- _ => apply (@termsrc_prod1 t2)
  | H: termsrc (src_mu t ?t2) |- _ => apply (@termsrc_mu1 t2)
end.

Hint Extern 3 (bodysrc ?t) =>
  match goal with 
  | H: context [src_abs ?t1 t] |- _ => apply (@bodysrc_abs2 t1)
  | H: context [src_prod ?t1 t] |- _ => apply (@bodysrc_prod2 t1)
  | H: context [src_mu ?t1 t] |- _ => apply (@bodysrc_mu2 t1)
  end.

Hint Extern 1 (bodysrc ?t) =>
  match goal with 
  | H: context [t ^ _] |- _ =>
      let x := fresh in let Fr := fresh in
      let P := fresh in
      let L := gather_vars in exists L; intros x Fr; 
      lets P: H x __; [ notin_solve 
                      | try destructs P ]
  end.

Lemma termsrc_abs_prove : forall t1 t2,
  termsrc t1 -> bodysrc t2 -> termsrc (src_abs t1 t2).
Proof.
  intros. apply_fresh* termsrc_abs as x.
Qed.

Lemma termsrc_prod_prove : forall t1 t2,
  termsrc t1 -> bodysrc t2 -> termsrc (src_prod t1 t2).
Proof.
  intros. apply_fresh* termsrc_prod as x.
Qed.

Lemma termsrc_mu_prove : forall t1 t2,
  termsrc t1 -> bodysrc t2 -> termsrc (src_mu t1 t2).
Proof.
  intros. apply_fresh* termsrc_mu as x.
Qed.

Hint Resolve termsrc_abs_prove termsrc_prod_prove termsrc_mu_prove.

Lemma bodysrc_prove : forall L t,
  (forall x, x \notin L -> termsrc (t ^ x)) -> bodysrc t.
Proof.
  intros. exists* L.
Qed.

Hint Extern 1 (bodysrc ?t) =>
  match goal with 
  | H: forall _, _ \notin ?L -> termsrc (t ^ _)  |- _ =>
    apply (@bodysrc_prove L)
  end. 

Lemma bodysrc_subst : forall x t u,
  termsrc u -> bodysrc t -> bodysrc ([x ~> u]t).
Proof.
  introv. intros Wu [L Bt].
  exists (\{x} \u L). intros y Fr. cross*.
Qed.

Hint Resolve bodysrc_subst.


(* ********************************************************************** *)
(** ** Additional results on primitive operations *)

Section PrimProperties.

Hint Constructors termsrc.

(** Open_var with fresh names is an injective operation *)

Lemma open_var_inj : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_var_body] and [close_var_open] *)

Lemma close_var_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (fv t1) ->
    {i ~> src_fvar y} ({j ~> src_fvar z} (close_var_rec j x t1) )
  = {j ~> src_fvar z} (close_var_rec j x ({i ~> src_fvar y}t1) ).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ]. 
  case_var*. simpl. case_nat*. 
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_fresh : forall x t,
  x \notin fv (close_var x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple*.
Qed.

(** Close var is an operation returning a body of an abstraction *)

Lemma close_var_body : forall x t,
  termsrc t -> bodysrc (close_var x t).
Proof.
  introv W. exists \{x}. intros y Fr.
  unfold open, close_var. generalize 0. gen y.
  induction W; intros y Fr k; simpls.
  case_var; simple*. case_nat*.
  autos*.
  autos*.
  apply_fresh* termsrc_abs as z.
   unfolds open. rewrite* close_var_rec_open.
  apply_fresh* termsrc_prod as z.
   unfolds open. rewrite* close_var_rec_open.
   apply_fresh* termsrc_mu as z.
   unfolds open. rewrite* close_var_rec_open.
  autos*.
  autos*.
Qed.

(** Close var is the right inverse of open_var *)

Lemma close_var_open : forall x t,
  termsrc t -> t = (close_var x t) ^ x.
Proof.
  introv W. unfold close_var, open. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
Qed. 
 
(** An abstract specification of close_var, which packages the
  result of the operation and all the properties about it. *)

Lemma close_var_spec : forall t x, termsrc t -> 
  exists u, t = u ^ x /\ bodysrc u /\ x \notin (fv u).
Proof.
  intros. exists (close_var x t). splits 3.
  apply* close_var_open.
  apply* close_var_body.
  apply* close_var_fresh.
Qed. 

End PrimProperties.


(* ********************************************************************** *)
(** ** Regularity: relations are restricted to terms *)

Hint Extern 1 (termsrc (src_abs ([?x ~> ?u]?t1) ([?x ~> ?u]?t2))) =>
  match goal with H: termsrc (src_abs t1 t2) |- _ => 
  unsimpl ([x ~> u](src_abs t1 t2)) end.

Hint Extern 1 (termsrc (src_mu ([?x ~> ?u]?t1) ([?x ~> ?u]?t2))) =>
  match goal with H: termsrc (src_mu t1 t2) |- _ => 
  unsimpl ([x ~> u](src_mu t1 t2)) end.

Lemma regular_typing : forall E t T, typsrc E t T ->
  (wf E /\ ok E /\ contains_terms E /\ termsrc t /\ termsrc T). 
Proof.
  apply typsrc_induct with
   (P0 := fun E (_ : wf E) => ok E /\ contains_terms E); 
   unfolds contains_terms; intros; splits*.
  intros. false* binds_empty_inv.
  intros. destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst*.
Qed.

Hint Extern 1 (termsrc ?t) => match goal with
  | H: typsrc _ t _ |- _ => apply (proj32 (proj33 (regular_typing H)))
  | H: typsrc _ _ t |- _ => apply (proj33 (proj33 (regular_typing H)))
  end.

Lemma ok_from_wf : forall E, wf E -> ok E.
Proof.
  induction 1. auto. autos* (regular_typing H0).
Qed.

Hint Extern 1 (ok ?E) => match goal with
  | H: wf E |- _ => apply (ok_from_wf H)
  end.

Hint Extern 1 (wf ?E) => match goal with
  | H: typsrc E _ _ |- _ => apply (proj1 (regular_typing H))
  end.

Lemma wf_push_inv : forall E x U,
  wf (E & x ~ U) -> wf E /\ termsrc U.
Proof.
  introv W. inversions W. 
  false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. subst~.
Qed.
(*todo: as hints ?*)

Lemma termsrc_from_binds_in_wf : forall x E U,
  wf E -> binds x U E -> termsrc U.
Proof.
  introv W Has. gen E. induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct (wf_push_inv W). binds_push~ Has.
Qed.

Hint Extern 1 (termsrc ?t) => match goal with
  H: binds ?x t ?E |- _ => apply (@termsrc_from_binds_in_wf x E)
  end.

Lemma wf_left : forall E F : env,
  wf (E & F) -> wf E.
Proof.
  intros. induction F using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   inversions H. false (empty_push_inv H1).
   destruct (eq_push_inv H0) as [? [? ?]]. subst~. 
Qed.

Implicit Arguments wf_left [E F].


(* ********************************************************************** *)
(** ** Some freshness results *)

Lemma fv_open_var : forall y x t,
  x <> y -> x \notin fv (t ^ y) -> x \notin fv t.
Proof.
  introv Neq. unfold open. generalize 0. 
  induction t; simpl; intros; try notin_solve.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
Qed.

Lemma typsrc_fresh : forall E T x,
  typsrc E T src_star -> x # E -> x \notin fv T.
Proof.
  introv Typ.
  induction Typ; simpls; intros.
  auto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1.
  pick_fresh y. notin_simpl. auto. apply* (@fv_open_var y).
  pick_fresh y. lets: (IHTyp H1). notin_simpl. auto. apply* (@fv_open_var y).
  lets: (IHTyp1 H). lets: (IHTyp2 H). auto.
  pick_fresh y. lets: (IHTyp H1). notin_simpl. auto. apply* (@fv_open_var y).
  lets: (IHTyp1 H0). lets: (IHTyp2 H0). auto.
  lets: (IHTyp1 H0). lets: (IHTyp2 H0). auto.
Qed.

Lemma notin_fv_from_wf : forall E F x V,
  wf (E & x ~ V & F) -> x \notin fv V.
Proof.
  intros.
  lets W: (wf_left H). inversions W.
  false (empty_push_inv H1). 
  destruct (eq_push_inv H0) as [? [? ?]]. subst~.
    (*todo: factorize the above pattern *) 
  apply* typsrc_fresh.
Qed.

Lemma notin_fv_from_binds : forall x y U E,
  wf E -> binds y U E -> x # E -> x \notin fv U.
Proof.
  induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct (wf_push_inv H). binds_push H0.
    inversions H. false* (empty_push_inv H5).
     destruct (eq_push_inv H4) as [? [? ?]]. subst~. 
     apply* typsrc_fresh.
    autos*.
Qed.

Lemma notin_fv_from_binds' : forall E F x V y U,
  wf (E & x ~ V & F) -> binds y U E -> x \notin fv U.
Proof.
  intros. lets W: (wf_left H). inversions keep W.
  false (empty_push_inv H2). 
  destruct (eq_push_inv H1) as [? [? ?]]. subst~. 
  lets W': (wf_left W). apply* notin_fv_from_binds.
Qed.

Hint Extern 1 (?x \notin fv ?V) => 
  match goal with H: wf (?E & x ~ V & ?F) |- _ =>
    apply (@notin_fv_from_wf E F) end.

Hint Extern 1 (?x \notin fv ?U) => 
  match goal with H: wf (?E & x ~ ?V & ?F), B: binds ?y U ?E |- _ =>
    apply (@notin_fv_from_binds' E F x V y) end.


