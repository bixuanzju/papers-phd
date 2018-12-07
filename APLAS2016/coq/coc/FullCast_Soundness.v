(***************************************************************************
* FullCast - Type Soundness                                                *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoCMu_Definitions CoCMu_Soundness CoCMu_ParaReduction FullCast_Definitions FullCast_Infrastructure.
Require CoCMu_Infrastructure.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Inversion Lemmas for typing *)

Lemma typsrc_prod_inv : forall E U T,
  typsrc E (src_prod U T) src_star -> 
  typsrc E U src_star
  /\ exists L, forall x, x \notin L ->
                         typsrc (E & x ~ U) (T ^ x) src_star.
Proof.
  introv Typ. gen_eq P1: (src_prod U T).
  induction Typ; intros; subst; tryfalse.
  inversions H1. exists*.
Qed.

Lemma typsrc_abs_inv : forall E V t P,
  typsrc E (src_abs V t) P -> exists T,
      typsrc E (src_prod V T) src_star
      /\ P = src_prod V T
      /\ exists L, forall x, x \notin L ->
                             typsrc (E & x ~ V) (t ^ x) (T ^ x).
Proof.
  introv Typ. gen_eq u: (src_abs V t).
  induction Typ; intros; subst; tryfalse.
  inversions H1. exists* T.
Qed.

Lemma typsrc_prod_type_inv : forall E U T,
  typsrc E (src_prod U T) src_star ->
  exists L, forall x, x \notin L ->
      typsrc (E & x ~ U) (T ^ x) src_star.
Proof.
  introv Typ.
  destruct (typsrc_prod_inv Typ) as [TypU [L TypT]].
  exists (L \u dom E). intros. auto.
Qed.

Lemma typsrc_castup_inv : forall E t U V,
    typsrc E (src_castup U t) V -> exists T,
      typsrc E U src_star /\ typsrc E t T
      /\ U = V /\ |U| ~p> |T|.
Proof.
  introv Typ. gen_eq u: (src_castup U t).
  induction Typ; intros; subst; tryfalse.
  inversion H0. exists* T. split.
  rewrite <- H2. apply Typ1.
  split. rewrite <- H3. apply Typ2.
  split. reflexivity. rewrite <- H2. auto.
Qed.

Lemma typsrc_castdn_inv : forall E t U V,
    typsrc E (src_castdn U t) V -> exists T,
      typsrc E U src_star /\ typsrc E t T
      /\ U = V /\ |T| ~p> |U|.
Proof.
  introv Typ. gen_eq u: (src_castdn U t).
  induction Typ; intros; subst; tryfalse.
  inversion H0. exists* T. split.
  rewrite <- H2. apply Typ1.
  split. rewrite <- H3. apply Typ2.
  split. reflexivity. rewrite <- H2. auto.
Qed.

(* ********************************************************************** *)
(** typing preserved by Weakening *)

Lemma typsrc_weaken : forall G E F t T,
  typsrc (E & G) t T ->
  wf (E & F & G) -> 
  typsrc (E & F & G) t T.
Proof.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; eauto.
  (* case: var *)
  apply* typsrc_var. apply* binds_weaken.
  (* case: src_prod *)
  apply_fresh* (@typsrc_prod) as y. apply_ih_bind* H0.
  (* case: src_abs *)
  apply_fresh* (@typsrc_abs) as y.
  forwards TypP: (IHTyp G); auto.
  destruct (typsrc_prod_inv TypP) as [TypU _].
  apply_ih_bind* H0.
  (* case: src_mu *)
  apply_fresh* (@typsrc_mu) as y. apply_ih_bind* H0.
Qed.

(* ********************************************************************** *)
(** Soundness of erasure *)

Definition copen_rec := CoCMu_Definitions.open_rec.
Definition copen t x := CoCMu_Definitions.open t (trm_fvar x).
Definition copent t x n := CoCMu_Definitions.open_rec n (trm_fvar x) t.
Definition opent t x n := open_rec n (src_fvar x) t.
Definition csubst := CoCMu_Infrastructure.subst.
Definition erase_ctx := map erasure.
Definition wfc := CoCMu_Definitions.wf.

Lemma erasure_rename : forall x y t,
    y \notin fv t ->
    |[x ~> src_fvar y] t| = csubst x (trm_fvar y) (|t|).
Proof.
  intros. induction t; simpls. auto.
  case_var~. auto.
  fequals. apply* IHt1. apply* IHt2.
  fequals. apply* IHt1. apply* IHt2.
  fequals. apply* IHt1. apply* IHt2.
  fequals. apply* IHt1. apply* IHt2.
  apply* IHt2.
  apply* IHt2.
Qed.

Lemma erasure_subst : forall x u e,
  |[x ~> u] e| = csubst x (|u|) (|e|).
Proof.
  intros. induction e; simpls; auto.
  case_var~.
  fequals.
  fequals.
  fequals.
  fequals.
Qed.

Lemma erasure_open_rec : forall u e n,
    |open_rec n u e| = copen_rec n (|u|) (|e|).
Proof.
  intros. gen n. induction e; unfold copen_rec;
                   intros; simpls; auto.
  case_nat*.
  fequals. apply IHe1. apply IHe2.
  fequals. apply IHe1. apply IHe2.
  fequals. apply IHe1. apply IHe2.
  fequals. apply IHe1. apply IHe2.
Qed.

Lemma erasure_opene : forall u e,
    |e ^^ u| = copen_rec 0 (|u|) (|e|).
Proof.
  intros. apply erasure_open_rec.
Qed.

Lemma erasure_opent : forall x e n,
    |opent e x n| = copent (|e|) x n.
Proof.
  intros. apply (erasure_open_rec (src_fvar x)).
Qed.

Lemma erasure_open : forall x e,
    |e ^ x| = copen (|e|) x.
Proof.
  intros. 
  apply erasure_opent.
Qed.

Lemma termsrc_to_term : forall e,
    termsrc e -> term (|e|).
Proof.
  introv T. induction T; simpls; auto.
  apply* term_abs. intros.
  pose (erasure_open x t2). unfold copen in e.
  rewrite <- e. apply* H0.
  apply* term_prod. intros.
  pose (erasure_open x t2). unfold copen in e.
  rewrite <- e. apply* H0.
  apply* term_mu. intros.
  pose (erasure_open x t2). unfold copen in e.
  rewrite <- e. apply* H0.
Qed.

Lemma erpared_red_out : red_out erasure_pared.
Proof.
  unfold red_out. unfold erasure_pared.
  intros.
  rewrite -> (erasure_subst x u t).
  rewrite -> (erasure_subst x u t').
  apply* pared_red_out.
  apply* termsrc_to_term.
Qed.

Lemma binds_erasure : forall E x U,
    binds x U E ->
    binds x (|U|) (erase_ctx E).
Proof.
  intros.
  unfold erase_ctx.
  apply* binds_map.
Qed.

Lemma erase_ctx_bind : forall E x U,
    erase_ctx (E & x ~ U) = erase_ctx E & x ~ |U|.
Proof.
  intros. unfold erase_ctx.
  apply* map_push.
Qed.

(* ********************************************************************** *)
(** typing preserved by Substitution *)

Lemma typsrc_substitution : forall V (F:env) v (E:env) x t T,
  typsrc E v V ->
  typsrc (E & x ~ V & F) t T ->
  typsrc (E & (map (subst x v) F)) (subst x v t) (subst x v T).
Proof.
  introv Typv Typt.
  gen_eq G: (E & x ~ V & F). gen F. 
  apply typsrc_induct with
   (P := fun (G:env) t T (Typt : typsrc G t T) => 
      forall (F:env), G = E & x ~ V & F -> 
      typsrc (E & map (subst x v) F) ([x ~> v]t) ([x ~> v]T))
   (P0 := fun (G:env) (W:wf G) => 
      forall F, G = E & x ~ V & F -> 
      wf (E & (map (subst x v) F))); 
   intros; subst; simpls subst. 
  (* case: src_star *)
  autos*.
  (* case: var *)
  case_var.
    binds_mid~. rewrite* subst_fresh. apply_empty* typsrc_weaken.
    apply~ typsrc_var. destruct~ (binds_not_middle_inv b) as [K|[Fr K]].
      rewrite* subst_fresh.
  (* case: src_prod *)
  apply_fresh* (@typsrc_prod) as y.
   cross; auto. apply_ih_map_bind* H0. 
  (* case: src_abs *)
  apply_fresh* (@typsrc_abs) as y.
   cross; auto. apply_ih_map_bind* H0.
  (* case: src_app *)
  rewrite* subst_open.
  (* case: src_mu *)
  apply_fresh* (@typsrc_mu) as y.
  cross; auto. apply_ih_map_bind* H0.
  (* case: src_castup *)
  apply* (@typsrc_castup). apply* erpared_red_out.
  (* case: src_castdn *)
  apply* (@typsrc_castdn). apply* erpared_red_out.
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
(** Types are Themselves Well-typed *)

Lemma typsrc_wf_from_context : forall x U (E:env),
  binds x U E -> 
  wf E -> 
  typsrc E U src_star.
Proof.
  introv B W. induction E using env_ind. 
  false* binds_empty_inv. 
  destruct (binds_push_inv B) as [[? ?]|[? ?]]. 
    subst. inversions W. false (empty_push_inv H0).
     destruct (eq_push_inv H) as [? [? ?]]. subst.
     apply_empty* typsrc_weaken.
    destruct (wf_push_inv W).
     apply_empty* typsrc_weaken.
Qed.

Lemma typsrc_wf_from_typing : forall E t T,
  typsrc E t T ->
  typsrc E T src_star.
Proof.
  induction 1.
  auto.
  destruct* (typsrc_wf_from_context H0).
  auto.
  auto.
  destruct (typsrc_prod_inv IHtypsrc1) as [TypU [L TypT]].
  pick_fresh x. rewrite~ (@subst_intro x).
  unsimpl ([x ~> u](src_star)).
  apply_empty* (@typsrc_substitution U).
  auto. auto. auto.
Qed.

(* ********************************************************************** *)
(** ** Main Results *)

(** Erasure Soundness *)
 
Lemma typsrc_to_typera : forall E t T,
    typsrc E t T ->
    typing (erase_ctx E) (|t|) (|T|)
with wfsrc_to_wf : forall E,
      wf E -> wfc (erase_ctx E).
Proof.
  introv Tsrc.
  inductions Tsrc; simpl.
  apply* typing_star. apply* wfsrc_to_wf.
  apply* typing_var. apply* wfsrc_to_wf. apply* binds_erasure.
  apply typing_prod with (L := L). auto. intros.
  pose (erasure_open x T). unfold copen in e.
  rewrite <- e.
  rewrite <- erase_ctx_bind.
  auto.
  destruct (typing_prod_inv IHTsrc) as [Le [TypU [L2 TypT]]].
  apply typing_abs with (L := L \u L2).
  auto. intros. apply* TypT. intros.
  pose (erasure_open x T). unfold copen in e.
  rewrite <- e.
  pose (erasure_open x t). unfold copen in e0.
  rewrite <- e0.
  rewrite <- erase_ctx_bind.
  auto.
  pose (erasure_opene u T). unfold copen_rec in e. 
  rewrite e.
  apply* typing_app.
  apply typing_mu with (L := L). auto. intros.
  pose (erasure_open x t). unfold copen in e.
  rewrite <- e.
  rewrite <- erase_ctx_bind.
  auto.
  unfold erasure_pared in H.
  pose (para_to_less_rev (pared_to_para H)).
  apply typing_sub with (T := |T|).
  auto. auto. auto.
  unfold erasure_pared in H.
  pose (para_to_less (pared_to_para H)).
  apply typing_sub with (T := |T|).
  auto. auto. auto.

  introv Wf.
  inductions Wf; unfold erase_ctx; simpl.
  assert (map erasure empty = empty).
  apply* map_empty.
  rewrite H.
  apply* CoCMu_Definitions.wf_nil.
  rewrite* map_push.
  apply* CoCMu_Definitions.wf_cons.
  assert (|src_star| = trm_star) by auto.
  rewrite <- H1.
  apply* typsrc_to_typera.
Qed.

(** Type Soundness *)

Theorem subject_reduction_result : forall E t t' T,
    typsrc E t T ->
    |t| ~p> |t'| ->
    typing (erase_ctx E) (|t'|) (|T|).
Proof.
  intros.
  apply* subject_reduction_era.
  apply* typsrc_to_typera.
Qed.

Theorem progress_result : forall t T, 
    typsrc empty t T ->
    value (|t|) 
    \/ exists t', |t| ~~> t'.
Proof.
  intros.
  pose (H' := typsrc_to_typera H).
  assert (erase_ctx empty = empty).
  unfold erase_ctx. apply map_empty.
  rewrite -> H0 in H'.
  apply (progress_era H').
Qed.

