(***************************************************************************
* CoC + Mu + Type-in-type - Subject Reduction                              *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoCMu_Definitions CoCMu_Infrastructure CoCMu_Conversion CoCMu_ChurchRosser.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Inversion Lemmas for Subtyping *)

Lemma less_type_any_inv : forall T1 T2,
  less T1 T2 -> conv T1 trm_star ->
  conv T2 trm_star.
Proof.
  induction 1; intros C1.
  pose (equiv_sym H).
  pose (equiv_trans e C1).
  auto.
  false. apply (conv_type_prod_inv (equiv_sym C1)).
  auto. apply (IHless2 (IHless1 C1)).
Qed.

Lemma less_type_type_inv :
  less trm_star trm_star.
Proof.
  apply* less_conv.
Qed.

Lemma less_prod_any_inv : forall P1 P2,
  less P1 P2 -> forall U1 T1, conv P1 (trm_prod U1 T1) ->
  exists U2, exists T2, conv P2 (trm_prod U2 T2) 
  /\ conv U1 U2 
  /\ exists L, forall x, x \notin L -> less (T1 ^ x) (T2 ^ x).
Proof.
  induction 1; intros U1 T1 C1.
  exists U1 T1. 
   asserts* K: (term (trm_prod U1 T1)). inversions K.
   splits.
     apply* (@equiv_trans beta t1).
     auto.
     exists_fresh. auto.
  exists U' T'. 
   asserts* K: (less (trm_prod U T) (trm_prod U' T')).  
   destruct (conv_prod_prod_inv C1) as [C11 [L1 C12]].
   splits.
    auto.
    apply* (@equiv_trans beta U).
    exists_fresh. intros. apply (@less_trans (T ^ x)).
      forwards*: (C12 x). auto.
  exists U1 T1. asserts* K: (term (trm_prod U1 T1)). inversions* K.
  destruct (IHless1 _ _ C1) as [U2 [T2 [C2 [C21 [L2 C22]]]]].
   destruct (IHless2 _ _ C2) as [U3 [T3 [C3 [C31 [L3 C32]]]]].
   exists U3 T3. splits.
     auto.
     apply* (@equiv_trans beta U2).
     exists_fresh. intros. apply* (@less_trans (T2 ^ x)).
Qed.

Lemma less_prod_prod_inv : forall U1 T1 U2 T2,
  less (trm_prod U1 T1) (trm_prod U2 T2) -> 
     conv U1 U2
  /\ exists L, forall x, x \notin L -> less (T1 ^ x) (T2 ^ x).
Proof.
  introv Le.
  destruct (@less_prod_any_inv _ _ Le U1 T1) 
    as [U2' [T2' [C [C1' [L' C2']]]]]; auto.
  destruct (conv_prod_prod_inv C) as [C1 [L C2]].
  splits.
    apply* (@equiv_trans beta U2'). 
    exists_fresh. intros. apply (@less_trans (T2' ^ x)).
      auto.
      forwards*: (C2 x).
Qed.

Lemma less_star_prod_false : forall U T,
    less trm_star (trm_prod U T) -> False.
Proof.
  introv Le.
  assert (conv trm_star trm_star) by auto.
  apply (conv_type_prod_inv (equiv_sym (less_type_any_inv Le H))).
Qed.

Lemma para_to_less : forall t t',
    para t t' -> less t t'.
Proof.
  intros.
  assert ((para iter) t t').
  apply* iter_step.
  assert ((beta star) t t').
  apply* para_iter_to_beta_star.
  assert (conv t t').
  apply* conv_from_beta_star.
  apply* less_conv.
Qed.

Lemma para_to_less_rev : forall t t',
    para t t' -> less t' t.
Proof.
  intros.
  assert ((para iter) t t').
  apply* iter_step.
  assert ((beta star) t t').
  apply* para_iter_to_beta_star.
  assert (conv t t').
  apply* conv_from_beta_star.
  pose (equiv_sym H2).
  apply* less_conv.
Qed.

(* ********************************************************************** *)
(** ** Inversion Lemmas for Typing *)

Lemma typing_prod_inv : forall E U T P,
  typing E (trm_prod U T) P ->
     less trm_star P
  /\ typing E U trm_star
  /\ exists L, forall x, x \notin L -> typing (E & x ~ U) (T ^ x) trm_star.
Proof.
  introv Typ. gen_eq P1: (trm_prod U T). 
  induction Typ; intros; subst; tryfalse.
  injection H1. intros. subst.
  split. auto. split. auto. exists* L.
  destruct~ (IHTyp1 eq_refl) as [EQi [TypU [L P]]].
  autos* (@less_trans T0).
Qed.

Lemma typing_abs_inv : forall E V t P,
  typing E (trm_abs V t) P -> exists T L,
     typing E V trm_star
  /\ (forall x, x \notin L -> typing (E & x ~ V) (T ^ x) trm_star)
  /\ (less (trm_prod V T) P)
  /\ (forall x, x \notin L -> typing (E & x ~ V) (t ^ x) (T ^ x)).
Proof.
  introv Typ. gen_eq u: (trm_abs V t).
  induction Typ; intros; subst; tryfalse.
  injection H3. intros. subst.
  exists T. exists L. split. auto. split. intros.
  apply (H x H4). split. apply* less_refl.
  apply* term_prod_prove. unfold body.
  exists L. intros. pose (H x H4).
  auto. intros. apply (H1 x H4).
  destruct (IHTyp1 eq_refl) as [T0 [L [TypE [TypT0 [Le P2]]]]].
  exists T0. exists L. split. auto. split. intros.
  apply (TypT0 x H0).
  split. pose (less_trans Le H). auto.
  intros. apply (P2 x H0).
Qed.

Lemma typing_prod_type_inv : forall E U T,
  typing E (trm_prod U T) trm_star ->
  exists L, forall x, x \notin L -> 
      typing (E & x ~ U) (T ^ x) trm_star.
Proof.
  introv Typ. 
  destruct (typing_prod_inv Typ) as [Le [TypU [L TypT]]].
  exists (L \u dom E). intros.
  inversion Le; apply* (@typing_sub trm_star). 
Qed.

Lemma typing_star_inv : forall E P,
    typing E trm_star P ->
    less trm_star P.
Proof.
  introv Typ.
  inductions Typ. auto.
  apply (less_trans IHTyp1 H).
Qed.

(* ********************************************************************** *)
(** Typing preserved by Weakening *)

Lemma typera_weaken : forall G E F t T,
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
  apply_ih_bind* H0. apply_ih_bind* H2.
  (* case: trm_mu *)
  apply_fresh* (@typing_mu) as y. apply_ih_bind* H0.
Qed.


(* ********************************************************************** *)
(** ** Subtyping preserved by Substitution *)

Lemma less_red_out : red_out less.
Proof.
  intros_all. lets: conv_red_out; induction H0; simpl; auto.
  apply_fresh* less_prod as y. cross*.
  apply* (@less_trans ([x ~> u]U)).
Qed.


(* ********************************************************************** *)
(** Typing preserved by Substitution *)

Lemma typera_substitution : forall V (F:env) v (E:env) x t T,
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
  (* case: trm_type *)
  autos*.
  (* case: var *)
  case_var.
    binds_mid~. rewrite* subst_fresh. apply_empty* typera_weaken.
    apply~ typing_var. destruct~ (binds_not_middle_inv b) as [K|[Fr K]].
      rewrite* subst_fresh.
  (* case: trm_prod *)
  apply_fresh* (@typing_prod) as y.
   cross; auto. apply_ih_map_bind* H0. 
  (* case: trm_abs *)
  apply_fresh* (@typing_abs) as y.
   cross; auto. apply_ih_map_bind* H0.
   cross; auto. apply_ih_map_bind* H1.
  (* case: trm_app *)
  rewrite* subst_open.
  (* case: sub *)
  apply* (@typing_sub ([x ~> v]T0)). apply* less_red_out.
  (* case: trm_mu *)
  apply_fresh* (@typing_mu) as y.
  cross; auto. apply_ih_map_bind* H0.
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
     apply_empty* typera_weaken.
    destruct (wf_push_inv W).
     apply_empty* typera_weaken.
Qed.

Lemma typera_wf_from_typera : forall E t T,
  typing E t T ->
  typing E T trm_star.
Proof.
  induction 1. auto.
  destruct* (typing_wf_from_context H0).
  auto. auto.
  apply* typing_prod.
  destruct (typing_prod_inv IHtyping1) as [Le [TypU [L TypT]]].
   pick_fresh x. rewrite~ (@subst_intro x).
   unsimpl ([x ~> u](trm_star)).
   apply_empty* (@typera_substitution U).
  auto. auto.
Qed.


(* ********************************************************************** *)
(** Typing preserved by Subtyping in Environment *)

Inductive env_less : env -> env -> Prop :=
  | env_less_head : forall E U U' x, 
      less U U' -> 
      env_less (E & x ~ U) (E & x ~ U')
  | env_less_tail : forall E E' x U,
      term U -> env_less E E' -> env_less (E & x ~ U) (E' & x ~ U).

Hint Constructors env_less.

Lemma env_less_binds : forall x U E E',
  env_less E' E -> wf E -> wf E' -> binds x U E -> 
     binds x U E' 
  \/ exists U', 
      binds x U' E' /\ less U' U /\ typing E' U trm_star.
Proof.
  introv Le. induction Le; intros WfE WfE' Has.
  destruct (binds_push_inv Has) as [[? ?]|[? ?]]. 
    subst. right. inversions WfE. false (empty_push_inv H1).
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     exists U0. splits~. apply_empty* typera_weaken.  
    left. apply~ binds_push_neq.
  destruct (binds_push_inv Has) as [[? ?]|[? ?]].
    subst. left. apply~ binds_push_eq.
    inversions keep WfE. false (empty_push_inv H3).
     inversions WfE'. false (empty_push_inv H6).
     destruct (eq_push_inv H5) as [? [? ?]]. subst.
     destruct (wf_push_inv WfE).
     destruct IHLe as [|[U' [P1 [P2 P3]]]]; auto. 
      right. exists U'. splits~. apply_empty* typera_weaken.
Qed. 

Lemma typing_sub_env : forall E E' t T,
  typing E t T -> 
  env_less E' E -> 
  wf E' -> 
  typing E' t T.
Proof.
 introv Typ. gen E'. induction Typ; intros E' C W; eauto.
 destruct (env_less_binds C H W H0) as [B |[U' [B [Le Typ]]]].
   apply* typing_var.
   apply* (@typing_sub U').
  apply_fresh (@typing_prod) as y; auto.
  (* forwards~ TypP: (IHTyp E'). *)
  (* destruct (typing_prod_inv TypP) as [_ [Typt1 _]].  *)
  apply_fresh (@typing_abs) as y; auto.
  apply_fresh (@typing_mu) as y; auto.
Qed.


(* ********************************************************************** *)
(** Subject Reduction - Induction *)

Lemma subject_reduction_ind : forall E t t' T,
  typing E t T -> beta t t' -> typing E t' T.
Proof.
  introv Typ. gen t'.
  induction Typ; introv Red;
   try solve [ apply* typing_sub ]; inversions Red.

  (* case: trm_prod 1 *)
  apply_fresh* (@typing_prod) as y.
   apply (@typing_sub_env (E & y ~ U)); eauto 7. 

  (* case: trm_prod 2 *)
  apply_fresh* (@typing_prod) as y.

  (* case: trm_abs 1 *)
  apply* (@typing_sub (trm_prod t1' T)).
    apply_fresh less_prod as y.
      auto.
      forwards*: (H y).
    apply_fresh* (@typing_abs) as y.
     apply (@typing_sub_env (E & y ~ U)); eauto 7.
     apply (@typing_sub_env (E & y ~ U)); eauto 7.

  (* case: trm_abs 2 *)
  apply_fresh* (@typing_abs) as y.

  (* case: trm_app - beta reduction *)
  destruct (typing_abs_inv Typ1) as [T' [L1 [Typt1 [TypT' [LeP Typt2]]]]].
  destruct (less_prod_prod_inv LeP) as [C [L3 LeT]].
  pose (TypUT := typera_wf_from_typera Typ1).
  destruct (typing_prod_type_inv TypUT) as [L4 TypT].
  pick_fresh x.
   rewrite* (@subst_intro x t2).
   rewrite* (@subst_intro x T).
  apply_empty (@typera_substitution t1).
    apply* (@typing_sub U).
    apply (@typing_sub (T' ^ x)); auto.
     apply* (@typing_sub_env (E & x ~ U)).

  (* case: trm_app 1 *)
  autos*.

  (* case: trm_app 2 *)
  pose (TypUT := typera_wf_from_typera Typ1).
  destruct (typing_prod_type_inv TypUT) as [L TypT].
  apply* (@typing_sub (T ^^ t2')).
    apply less_conv. apply* conv_from_open_beta.
    pick_fresh x. rewrite* (@subst_intro x T).
     unsimpl (subst x u trm_star).
     apply_empty* (@typera_substitution U).

  (* case: trm_mu - reduction *)
  pick_fresh x.
  assert ([x ~> trm_mu T t] T = T).
  apply subst_fresh. auto.
  rewrite <- H1 at 2.
  rewrite* (@subst_intro x t).
  apply_empty* (@typera_substitution ([x ~> trm_mu T t] T)).
  rewrite H1.
  apply typing_mu with (L := L).
  apply Typ. apply H.
  rewrite H1. apply H. auto.

  (* case: trm_mu 1 *)
  forwards~ Typt1'T: (IHTyp t1').
  apply* (@typing_sub t1').
  apply_fresh* (@typing_mu) as y.
  forwards~ K: (H y).
  apply (@typing_sub_env (E & y ~ T)).
  apply (@typing_sub) with (T := T).
  auto. auto. 
  rewrite <- (concat_empty_r (E & y ~ T)).
  apply typera_weaken.
  rewrite -> (concat_empty_r E). auto.
  rewrite -> (concat_empty_r (E & y ~ T)). auto.
  apply* env_less_head.
  apply* wf_cons.

  (* case: trm_mu 2 *)
  apply_fresh* (@typing_mu) as y.
Qed.

(* ********************************************************************** *)
(** Subject Reduction - Beta preserves typing  *)

Lemma subject_reduction_result : subject_reduction beta.
Proof.
  introv Red Typ. apply* subject_reduction_ind.
Qed.

(** Subject Reduction - Beta Star preserves typing  *)

Lemma subject_reduction_star_result : 
  subject_reduction (beta star).
Proof.
  introv H. induction* H. apply* subject_reduction_result.
Qed.

(** Subject Reduction - Parallel Reduction preserves typing  *)

Lemma subject_reduction_para_iter_result : 
  subject_reduction (para iter).
Proof.
  introv H. induction* H.
  apply* subject_reduction_star_result.
  apply* para_iter_to_beta_star.
Qed.

Lemma subject_reduction_para_result :
  subject_reduction para.
Proof.
  introv H. 
  pose (iter_step para t t' H).
  apply* subject_reduction_para_iter_result.
Qed.

(* ********************************************************************** *)
(** Progress of weak-head reduction *)

Lemma progress_era : progress_wh.
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  left*.
  false* binds_empty_inv. 
  left*.
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
      inversions Typ1; inversions Val1. exists* (t0 ^^ u).
      false. apply* (less_star_prod_false (less_trans (typing_star_inv H0) H)).
      exists* (t2 ^^ u).
      destruct~ (typing_prod_inv H0) as [EQi [Typt1 [L2 TypT']]].
      false. apply* (less_star_prod_false (less_trans EQi H)).
      exists* (trm_app t1' u).
      apply* IHTyp1.
  right. exists* (t ^^ trm_mu T t).
Qed.

