(***************************************************************************
* WeakCast - Type Soundness                                                *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN WeakCast_Definitions WeakCast_Infrastructure.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Inversion Lemmas for Typing *)

Lemma typing_prod_inv : forall E U T,
  typing E (trm_prod U T) trm_star -> 
  typing E U trm_star
  /\ exists L, forall x, x \notin L ->
                         typing (E & x ~ U) (T ^ x) trm_star.
Proof.
  introv Typ. gen_eq P1: (trm_prod U T).
  induction Typ; intros; subst; tryfalse.
  inversions H1. exists*.
Qed.

Lemma typing_abs_inv : forall E V t P,
  typing E (trm_abs V t) P -> exists T,
      typing E (trm_prod V T) trm_star
      /\ P = trm_prod V T
      /\ exists L, forall x, x \notin L ->
                             typing (E & x ~ V) (t ^ x) (T ^ x).
Proof.
  introv Typ. gen_eq u: (trm_abs V t).
  induction Typ; intros; subst; tryfalse.
  inversions H1. exists* T.
Qed.

Lemma typing_prod_type_inv : forall E U T,
  typing E (trm_prod U T) trm_star ->
  exists L, forall x, x \notin L ->
      typing (E & x ~ U) (T ^ x) trm_star.
Proof.
  introv Typ.
  destruct (typing_prod_inv Typ) as [TypU [L TypT]].
  exists (L \u dom E). intros. auto.
Qed.

Lemma typing_castup_inv : forall E t U V,
    typing E (trm_castup U t) V -> exists T,
      typing E U trm_star /\ typing E t T
      /\ U = V /\ U ~~> T.
Proof.
  introv Typ. gen_eq u: (trm_castup U t).
  induction Typ; intros; subst; tryfalse.
  inversion H0. exists* T. split.
  rewrite <- H2. apply Typ1.
  split. rewrite <- H3. apply Typ2.
  split. reflexivity. rewrite <- H2. auto.
Qed.

(* ********************************************************************** *)
(** Typing preserved by Weakening *)

Lemma typing_weaken : forall G E F t T,
  typing (E & G) t T ->
  wf (E & F & G) -> 
  typing (E & F & G) t T.
Proof.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; eauto.
  (* case: var *)
  apply* typing_var. apply* binds_weaken.
  (* case: trm_prod *)
  apply_fresh* (@typing_prod) as y. apply_ih_bind* H0.
  (* case: trm_abs *)
  apply_fresh* (@typing_abs) as y.
  forwards TypP: (IHTyp G); auto.
  destruct (typing_prod_inv TypP) as [TypU _].
  apply_ih_bind* H0.
  (* case: trm_mu *)
  apply_fresh* (@typing_mu) as y. apply_ih_bind* H0.
Qed.


(* ********************************************************************** *)
(** Typing preserved by Reduction *)

Lemma value_red_out : forall x u t,
    term u -> value t -> value ([x ~> u] t).
Proof.
  intros_all. induction H0; simpl.
  auto. apply* value_lam. apply* value_pi.
  apply* value_castup.
Qed.

Lemma reduct_red_out : red_out reduct.
Proof.
  intros_all. induction H0; simpl.
  rewrite* subst_open.
  apply* reduct_app.
  rewrite* subst_open.
  apply* reduct_mu.
  apply* reduct_castup.
  apply* reduct_castdn.
  apply* reduct_castelim.
  apply* value_red_out.
Qed.

(* ********************************************************************** *)
(** Typing preserved by Substitution *)

Lemma typing_substitution : forall V (F:env) v (E:env) x t T,
  typing E v V ->
  typing (E & x ~ V & F) t T ->
  typing (E & (map (subst x v) F)) (subst x v t) (subst x v T).
Proof.
  introv Typv Typt.
  gen_eq G: (E & x ~ V & F). gen F. 
  apply typing_induct with
   (P := fun (G:env) t T (Typt : typing G t T) => 
      forall (F:env), G = E & x ~ V & F -> 
      typing (E & map (subst x v) F) ([x ~> v]t) ([x ~> v]T))
   (P0 := fun (G:env) (W:wf G) => 
      forall F, G = E & x ~ V & F -> 
      wf (E & (map (subst x v) F))); 
   intros; subst; simpls subst. 
  (* case: trm_star *)
  autos*.
  (* case: var *)
  case_var.
    binds_mid~. rewrite* subst_fresh. apply_empty* typing_weaken.
    apply~ typing_var. destruct~ (binds_not_middle_inv b) as [K|[Fr K]].
      rewrite* subst_fresh.
  (* case: trm_prod *)
  apply_fresh* (@typing_prod) as y.
   cross; auto. apply_ih_map_bind* H0. 
  (* case: trm_abs *)
  apply_fresh* (@typing_abs) as y.
   cross; auto. apply_ih_map_bind* H0.
  (* case: trm_app *)
  rewrite* subst_open.
  (* case: trm_mu *)
  apply_fresh* (@typing_mu) as y.
  cross; auto. apply_ih_map_bind* H0.
  (* case: trm_castup *)
  apply* (@typing_castup). apply* reduct_red_out.
  (* case: trm_castdn *)
  apply* (@typing_castdn). apply* reduct_red_out.
  (* case: wf nil *)
  false (empty_middle_inv H).
  (* case: wf cons *)
  change LibEnv.env with LibEnv.env in *.
  induction F using env_ind.
    rewrite concat_empty_r in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_empty. rewrite~ concat_empty_r.
    clear IHF. rewrite concat_assoc in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_push. rewrite concat_assoc. apply* (@wf_cons). 
  (* case: conclusion *)
  auto.
Qed.

(* ********************************************************************** *)
(** Value cannot be reduced *)

Lemma value_cannot_red : forall t t',
    value t -> t ~~> t' -> False.
Proof.
  introv H1. gen t'.
  induction H1; introv H2; inversions H2.
  apply (IHvalue e' H6).
Qed.

(* ********************************************************************** *)
(** One-step reduction is deterministic *)

Lemma reduct_determ : forall t t1 t2,
    t ~~> t1 -> t ~~> t2 -> t1 = t2.
Proof.
  introv H1. gen t2. induction H1; introv H2; inversions H2.
  auto. inversion H6.
  inversion H1. pose (IHreduct e1'0 H6). rewrite e. auto.
  auto. pose (IHreduct e'0 H6). rewrite e0. auto.
  pose (IHreduct e'0 H0). rewrite e0. auto.
  assert (value (trm_castup t t2)). auto.
  elimtype False. apply (value_cannot_red H H1).
  assert (value (trm_castup t v)). auto.
  elimtype False. apply (value_cannot_red H1 H3).
  auto.
Qed.

(* ********************************************************************** *)
(** Types are Themselves Well-typed *)

Lemma typing_wf_from_context : forall x U (E:env),
  binds x U E -> 
  wf E -> 
  typing E U trm_star.
Proof.
  introv B W. induction E using env_ind. 
  false* binds_empty_inv. 
  destruct (binds_push_inv B) as [[? ?]|[? ?]]. 
    subst. inversions W. false (empty_push_inv H0).
     destruct (eq_push_inv H) as [? [? ?]]. subst.
     apply_empty* typing_weaken.
    destruct (wf_push_inv W).
     apply_empty* typing_weaken.
Qed.

Lemma typing_wf_from_reduct : forall E T U,
  typing E T trm_star -> reduct T U ->
  typing E U trm_star.
Proof.
  introv Typ. gen U.
  induction Typ; introv Red; inversions Red.
  
  (* case: reduct_beta *)
  destruct (typing_abs_inv Typ1) as [T' [Typt0 [Eq1 [L1 Type1]]]].
  pick_fresh x.
  rewrite* (@subst_intro x e1).
  rewrite* (@subst_intro x T).
  apply_empty* (@typing_substitution t0).
  injection Eq1. intros. subst. auto.
  injection Eq1. intros. subst. auto.

  (* case: reduct_app *)
  assert (typing E e1' (trm_prod U T)).
  apply IHTyp1. auto.
  apply typing_app with (U := U).
  auto. auto.

  (* case: reduct_mu *)
  pick_fresh x.
  assert ([x ~> trm_mu T t] T = T).
  apply subst_fresh. auto.
  rewrite <- H1 at 2.
  rewrite* (@subst_intro x t).
  apply_empty* (@typing_substitution ([x ~> trm_mu T t] T)).
  rewrite H1.
  apply typing_mu with (L := L).
  apply Typ. apply H.
  rewrite H1. apply H. auto.

  (* case: reduct_castup *)
  autos*.

  (* case: reduct_castdn *)
  autos*.
  
  (* case: reduct_castelim *)
  destruct (typing_castup_inv Typ) as [T' [TypU [Typt [Eq1 Red1]]]].
  subst. pose (reduct_determ H Red1).
  rewrite e. auto.
Qed.

Lemma typing_wf_from_typing : forall E t T,
  typing E t T ->
  typing E T trm_star.
Proof.
  induction 1.
  auto.
  destruct* (typing_wf_from_context H0).
  auto.
  auto.
  destruct (typing_prod_inv IHtyping1) as [TypU [L TypT]].
  pick_fresh x. rewrite~ (@subst_intro x).
  unsimpl ([x ~> u](trm_star)).
  apply_empty* (@typing_substitution U).
  auto. auto. auto.
  apply typing_wf_from_reduct with (T := T).
  auto. auto.
Qed.

(* ********************************************************************** *)
(** Main results *)

(** Subject Reduction *)

Lemma subject_reduction_result : forall E t t' T,
  typing E t T -> t ~~> t' -> typing E t' T.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red; inversions Red.

  (* case: reduct_beta *)
  destruct (typing_abs_inv Typ1) as [T' [TypP [LeP [L1 Typt2]]]].
  destruct (typing_prod_inv TypP) as [Typt1 [L2 TypT']].
  pose (TypUT := typing_wf_from_typing Typ1).
  destruct (typing_prod_type_inv TypUT) as [L4 TypT].
  pick_fresh x.
  rewrite* (@subst_intro x e1).
  rewrite* (@subst_intro x T).
  apply_empty* (@typing_substitution t0).
  injection LeP. intros. rewrite <- H0. auto.
  injection LeP. intros. rewrite H. apply* Typt2.

  (* case: reduct_app *)
  autos*.

  (* case: reduct_mu *)
  pick_fresh x.
  assert ([x ~> trm_mu T t] T = T).
  apply subst_fresh. auto.
  rewrite <- H1 at 2.
  rewrite* (@subst_intro x t).
  apply_empty* (@typing_substitution ([x ~> trm_mu T t] T)).
  rewrite H1.
  apply typing_mu with (L := L).
  apply Typ. apply H.
  rewrite H1. apply H. auto.

  (* case: reduct_castup *)
  autos*.

  (* case: reduct_castdn *)
  autos*.

  (* case: reduct_castelim *)
  destruct (typing_castup_inv Typ) as [T' [TypU [Typt [Eq1 Red1]]]].
  subst. pose (reduct_determ H Red1).
  rewrite e. auto.
Qed.

(** Progress *)

Lemma progress_result : forall t T, 
  typing empty t T ->
     value t 
  \/ exists t', t ~~> t'.
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  left*.
  false* binds_empty_inv. 
  left*.
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ u).
      inversions H1. exists* (trm_app t1' u).
  right. exists* (t ^^ trm_mu T t).
  destruct~ IHTyp2 as [Val2 | [t2' Red2]].
  right. exists* (trm_castup U t2').
  right. destruct~ IHTyp as [Val1 | [t1' Red1]].
      inversions Typ; inversions Val1. 
      inversion H. inversion H. inversion H. exists* t0.
      exists* (trm_castdn t1').
Qed.

