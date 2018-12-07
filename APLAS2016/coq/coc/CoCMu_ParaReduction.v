(***************************************************************************
* CoC + Mu + Type-in-type - Parallel Reduction                             *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoCMu_Definitions CoCMu_Infrastructure CoCMu_Soundness
        CoCMu_ChurchRosser CoCMu_Conversion CoCMu_BetaStar.
Implicit Types x : var.

(* ********************************************************************** *)
(** Definition of parallel reduction *)

Inductive pared : relation :=
  | pared_red : forall t1 t2 u,
      term (trm_abs t1 t2) -> term u ->
      pared (trm_app (trm_abs t1 t2) u) (t2 ^^ u) 
  | pared_var : forall x, 
      pared (trm_fvar x) (trm_fvar x)
  | pared_star :
      pared trm_star trm_star
  | pared_app : forall t1 t1' t2 t2',
      pared t1 t1' -> 
      pared t2 t2' ->
      pared (trm_app t1 t2) (trm_app t1' t2')
  | pared_abs : forall L t1 t1' t2 t2',
     pared t1 t1' -> 
     (forall x, x \notin L -> pared (t2 ^ x) (t2' ^ x) ) ->
     pared (trm_abs t1 t2) (trm_abs t1' t2')
  | pared_prod : forall L t1 t1' t2 t2',
     pared t1 t1' -> 
     (forall x, x \notin L -> pared (t2 ^ x) (t2' ^ x) ) ->
     pared (trm_prod t1 t2) (trm_prod t1' t2')
  | pared_mured : forall t1 t2,
      term (trm_mu t1 t2) ->
      pared (trm_mu t1 t2) (t2 ^^ trm_mu t1 t2)
  | pared_mu : forall L t1 t1' t2 t2',
      pared t1 t1' -> 
      (forall x, x \notin L -> pared (t2 ^ x) (t2' ^ x) ) ->
      pared (trm_mu t1 t2) (trm_mu t1' t2').

Notation "t ~p> t'" := (pared t t') (at level 67).

(* ********************************************************************** *)
(** ** Lemmas Associated to Additional Definitions *)

Hint Constructors pared.

(* ********************************************************************** *)
(** Regularity *)

Lemma red_regular_pared : red_regular pared.
Proof.
  intros_all. induction* H.
Qed.

Lemma red_regular_pared_iter : red_regular (pared iter).
Proof.
  intros_all. induction* H. apply* red_regular_pared.
Qed.

Hint Extern 1 (term ?t) => match goal with
  | H: pared t _ |- _ => apply (proj1 (red_regular_pared H))
  | H: pared _ t |- _ => apply (proj2 (red_regular_pared H))
  | H: (pared iter) t _ |- _ => apply (proj1 (red_regular_pared_iter))
  | H: (pared iter) _ t |- _ => apply (proj2 (red_regular_pared_iter))
  end.

(* ********************************************************************** *)
(** Automation *)

Hint Resolve pared_var pared_star pared_app.

Hint Extern 1 (pared (trm_abs _ _) (trm_abs _ _)) =>
  let y := fresh "y" in apply_fresh pared_abs as y.
Hint Extern 1 (pared (trm_prod _ _) (trm_prod _ _)) =>
  let y := fresh "y" in apply_fresh pared_prod as y.
Hint Extern 1 (pared (trm_app (trm_abs _ _) _) (_ ^^ _)) =>
  let y := fresh "y" in apply_fresh pared_red as y.
Hint Extern 1 (pared (trm_mu _ _) (trm_mu _ _)) =>
  let y := fresh "y" in apply_fresh pared_mu as y.
Hint Extern 1 (pared (trm_mu _ _) (_ ^^ (trm_mu _ _))) =>
  let y := fresh "y" in apply_fresh pared_mured as y.

(* ********************************************************************** *)
(** Properties of parallel reduction and its iterated version *)

Hint Extern 1 (pared (if _ == _ then _ else _) _) => case_var.

Lemma pared_red_refl : red_refl pared.
Proof.
  intros_all. induction* H. 
Qed.

Lemma pared_red_out : red_out pared.
Proof.
  intros_all. induction H0; simpl.
  rewrite* subst_open.
  case_var*. apply *pared_red_refl.
  apply *pared_red_refl.
  apply* pared_app. 
  apply_fresh* pared_abs as y. cross*. 
  apply_fresh* pared_prod as y. cross*. 
  rewrite* subst_open.
  apply* pared_mured.
  apply_fresh* pared_mu as y. cross*. 
Qed.

Lemma pared_red_rename : red_rename pared.
Proof.
  apply* (red_out_to_rename pared_red_out).
Qed.

Lemma pared_to_para : forall t t',
    pared t t' -> para t t'.
Proof.
  intros_all. induction H.
  apply_fresh* para_red as y. apply* para_red_refl. apply* para_red_refl.
  apply* para_red_refl.
  apply* para_red_refl.
  apply* para_app.
  apply* para_abs.
  apply* para_prod.
  apply_fresh* para_mured as y. apply* para_red_refl. apply* para_red_refl.
  apply* para_mu.
Qed.

Lemma pared_iter_red_refl : red_refl (pared iter).
Proof.
  intros_all. autos* pared_red_refl.
Qed.

(* ********************************************************************** *)
(** Equality of parallel reductions *)

Lemma beta_star_to_pared_iter : 
  (beta star) simulated_by (pared iter).
Proof.
  intros_all. induction* H. 
  apply* pared_iter_red_refl.
  apply iter_step. induction H; autos* pared_red_refl.
Qed.

Lemma para_iter_to_pared_iter : 
  (para iter) simulated_by (pared iter).
Proof.
  intros_all.
  pose (para_iter_to_beta_star H).
  apply (beta_star_to_pared_iter s).
Qed.

Lemma pared_iter_to_para_iter : 
  (pared iter) simulated_by (para iter).
Proof.
  intros_all. induction* H.
  pose (pared_to_para H).
  apply* (iter_step para).
Qed.

(* ********************************************************************** *)
(** Confluence of iterated parallel reduction *)

Lemma pared_iter_confluence : confluence (pared iter).
Proof.
  intros_all.
  pose (H1 := pared_iter_to_para_iter H).
  pose (H2 := pared_iter_to_para_iter H0).
  destruct (para_iter_confluence H1 H2) as [P' [A B]].
  exists P'. split.
  apply* para_iter_to_pared_iter.
  apply* para_iter_to_pared_iter.
Qed.

(* ********************************************************************** *)
(** Subject Reduction *)

Lemma subject_reduction_pared_iter_result : 
  subject_reduction (pared iter).
Proof.
  introv H. induction* H.
  apply* subject_reduction_para_result.
  apply* pared_to_para.
Qed.

Lemma subject_reduction_era :
  subject_reduction pared.
Proof.
  introv H. 
  pose (iter_step pared t t' H).
  apply* subject_reduction_pared_iter_result.
Qed.

(* ********************************************************************** *)
(** Decidability *)

Definition decidable (P : Prop) := (P \/ ~ P).

(** Equality of terms *)

Lemma eq_typ_dec : forall (T T' : trm),
  sumbool (T = T') (T <> T').
Proof.
  decide equality.
  decide equality.
  apply* eq_var_dec.
Qed.

(** Inversion lemmas *)
Lemma typing_app_inv : forall E t1 t2 T,
    typing E (trm_app t1 t2) T ->
    exists U1 U2, typing E t1 U1 /\ typing E t2 U2.
Proof.
  intros. inductions H.
  exists (trm_prod U T).
  exists* U.
  apply IHtyping1.
Qed.

Lemma typing_mu_inv : forall E t1 t2 T,
    typing E (trm_mu t1 t2) T -> 
      typing E t1 trm_star /\
      exists L, forall x, x \notin L ->
                          typing (E & x ~ t1) (t2 ^ x) t1.
Proof.
  intros. inductions H.
  apply IHtyping1.
  split. auto.
  exists* L.
Qed.

(** One-step parallel reduction is decidable *)

Lemma pared_dec : forall E t t' T T',
    typing E t T ->
    typing E t' T' ->
    decidable (pared t t').
Proof.
  introv Typ. gen T'. gen t'. 
  lets Typ': Typ. inductions Typ; intros.

  destruct (eq_typ_dec t' trm_star).
  left. rewrite e. apply* pared_red_refl.
  right. intros P. inversions P. auto.

  destruct (eq_typ_dec t' (trm_fvar x)).
  left. rewrite e. apply* pared_red_refl.
  right. intros P. inversions P. auto.

  inductions H1.
  right. intros P. inversions P.
  right. intros P. inversions P.
  (* main case *)
  destruct (IHTyp Typ U0 trm_star H1) as [A | B].
  pick_fresh y.
  assert (Fr': y \notin L0) by auto.
  pose (TypT0_U0 := H2 y Fr').
  assert (TypT0_U: typing (E & y ~ U) (T0 ^ y) trm_star).
  apply* typing_sub_env. apply *env_less_head.
  apply* para_to_less. apply* pared_to_para.
  assert (Fr'': y \notin L) by auto.
  destruct (H0 y Fr'' (H y Fr'') (T0 ^ y) trm_star TypT0_U).
  left. apply pared_prod with (L := L). auto. intros.
  apply* pared_red_rename.
  right. intros P. inversions P. destruct H4.
  pick_fresh x. assert (Fr''': x \notin L1) by auto.
  pose (Q := H10 x Fr''').
  apply* pared_red_rename.
  right. intros P. inversions P. destruct B. auto.
  (* main case done *)
  right. intros P. inversions P.
  right. intros P. inversions P.
  apply* IHtyping1.
  right. intros P. inversions P.
  
  inductions H3.
  right. intros P. inversions P.
  right. intros P. inversions P.
  right. intros P. inversions P.
  (* main case *)
  destruct (IHTyp Typ U0 trm_star H3) as [A | B].
  pick_fresh y.
  assert (Fr': y \notin L0) by auto.
  pose (TypT0_U0 := H6 y Fr').
  assert (TypT0_U: typing (E & y ~ U) (t0 ^ y) (T0 ^ y)).
  apply* typing_sub_env. apply *env_less_head.
  apply* para_to_less. apply* pared_to_para.
  assert (Fr'': y \notin L) by auto.
  destruct (H2 y Fr'' (H1 y Fr'') (t0 ^ y) (T0 ^ y) TypT0_U).
  left. apply pared_abs with (L := L). auto. intros.
  apply* pared_red_rename.
  right. intros P. inversions P. destruct H8.
  pick_fresh x. assert (Fr''': x \notin L1) by auto.
  pose (Q := H14 x Fr''').
  apply* pared_red_rename.
  right. intros P1. inversions P1. auto.
  (* main case done *)
  right. intros P. inversions P.
  apply* IHtyping1.
  right. intros P. inversions P.

  destruct t'; destruct t;
  match goal with
  | [H: typing ?E (trm_app ?t'1 ?t'2) ?T' |-
     decidable (pared (trm_app ?t ?u) (trm_app _ _)) ] =>
    destruct (typing_app_inv H) as [U1 [U2 [TypU1 TypU2]]]
  | [ |- decidable (pared (trm_app (trm_abs ?a ?b) ?c) ?d) ] =>
    destruct (eq_typ_dec (b ^^ c) d) as [Eq | Neq];
      match goal with
      | [Eq: _ = _ |- decidable (_) ] => left; rewrite <- Eq; apply* pared_red
      | [Neq: _ <> _ |- decidable (_) ] =>   right; intros P; inversions P; auto
      end
  | [ |- decidable (pared (trm_app _ _) _) ] => right; intros P; inversions P
  end.

  destruct (IHTyp1 Typ1 t'1 U1 TypU1).
  destruct (IHTyp2 Typ2 t'2 U2 TypU2).
  left. apply* pared_app.
  right. intros P. inversions P. auto.
  right. intros P. inversions P. auto.
  
  destruct (IHTyp1 Typ1 t'1 U1 TypU1).
  destruct (IHTyp2 Typ2 t'2 U2 TypU2).
  left. apply* pared_app.
  right. intros P. inversions P. auto.
  right. intros P. inversions P. auto.
  
  destruct (IHTyp1 Typ1 t'1 U1 TypU1).
  destruct (IHTyp2 Typ2 t'2 U2 TypU2).
  left. apply* pared_app.
  right. intros P. inversions P. auto.
  right. intros P. inversions P. auto.
  
  destruct (IHTyp1 Typ1 t'1 U1 TypU1).
  destruct (IHTyp2 Typ2 t'2 U2 TypU2).
  left. apply* pared_app.
  right. intros P. inversions P. auto.
  right. intros P. inversions P. auto.
  
  destruct (IHTyp1 Typ1 t'1 U1 TypU1).
  destruct (IHTyp2 Typ2 t'2 U2 TypU2).
  left. apply* pared_app.
  destruct (eq_typ_dec (t2 ^^ u) (trm_app t'1 t'2)) as [Eq | Neq].
  rewrite <- Eq. left. apply* pared_red.
  right. intros P. inversions P. auto. auto.
  destruct (eq_typ_dec (t2 ^^ u) (trm_app t'1 t'2)) as [Eq | Neq].
  rewrite <- Eq. left. apply* pared_red.
  right. intros P. inversions P. auto. auto.
  
  destruct (IHTyp1 Typ1 t'1 U1 TypU1).
  destruct (IHTyp2 Typ2 t'2 U2 TypU2).
  left. apply* pared_app.
  right. intros P. inversions P. auto.
  right. intros P. inversions P. auto.

  destruct (IHTyp1 Typ1 t'1 U1 TypU1).
  destruct (IHTyp2 Typ2 t'2 U2 TypU2).
  left. apply* pared_app.
  right. intros P. inversions P. auto.
  right. intros P. inversions P. auto.

  apply* (IHTyp1 Typ1 t' T' H0).

  destruct (eq_typ_dec (t ^^ trm_mu T t) t') as [Eq | Neq].
  left. rewrite <- Eq. apply* pared_mured.
  destruct t'.
  right; intros P; inversions P; auto.
  right; intros P; inversions P; auto.
  right; intros P; inversions P; auto.
  right; intros P; inversions P; auto.
  right; intros P; inversions P; auto.
  right; intros P; inversions P; auto.

  destruct (typing_mu_inv H1) as [Ty1 [L1 P]].
  destruct (IHTyp Typ t'1 trm_star Ty1).
  pick_fresh y.
  assert (Fr1: y \notin L1) by auto.
  pose (Ty2 := P y Fr1).
  pose (T1y := close_var y t'1).
  assert (Eqt'1: t'1 = T1y ^ y) by (apply* close_var_open).
  assert (Ty2'': typing (E & y ~ T) (t'2 ^ y) t'1).
  apply* typing_sub_env. apply *env_less_head.
  apply* para_to_less. apply* pared_to_para.
  assert (Ty2': typing (E & y ~ T) (t'2 ^ y) (T1y ^ y)).
  rewrite <- Eqt'1. auto.
  assert (Fr2: y \notin L) by auto.
  destruct (H0 y Fr2 (H y Fr2) (t'2 ^ y) (T1y ^ y) Ty2').
  left. apply pared_mu with (L := L). auto. intros.
  apply* pared_red_rename.
  destruct (eq_typ_dec (t ^^ trm_mu T t) (trm_mu t'1 t'2)) as [Eq1 | Neq1].
  left. rewrite <- Eq1. apply* pared_mured.
  right. intros P2. inversion P2. auto.
  pick_fresh z. assert (Fr3: z \notin L0) by auto.
  pose (TZ := H9 z Fr3).
  destruct H3. apply* pared_red_rename.
  destruct (eq_typ_dec (t ^^ trm_mu T t) (trm_mu t'1 t'2)) as [Eq1 | Neq1].
  left. rewrite <- Eq1. apply* pared_mured.
  right. intros P2. inversion P2. auto. auto.
Qed.

