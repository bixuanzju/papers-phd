(***************************************************************************
* FullCast - Decidability of Type Checking                                 *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN
        CoCMu_Definitions FullCast_Definitions CoCMu_ParaReduction FullCast_Infrastructure FullCast_Soundness LibReflect.
Implicit Types x : var.

Definition decidable (P : Prop) := (P \/ ~ P).

(* ********************************************************************** *)
(** Lemmas of decidability *)

(** Equality of terms *)
Lemma eq_typ_dec : forall (T T' : src),
  sumbool (T = T') (T <> T').
Proof.
  decide equality.
  decide equality.
  apply* eq_var_dec.
Qed.

(** Bindings lookup *)
Lemma binds_lookup_dec : forall (x : var) (E : env),
    decidable (exists a, binds x a E).
Proof.
  intros. destruct (decidable_sumbool (indom_decidable E x)).
  left. destruct (get_some m). exists x0. unfold binds. auto.
  right. intros [a P]. unfold binds in P. pose (get_some_inv P). auto.
Qed.

(** A termsrc can be reduced *)
Lemma reduct_dec : forall E t T t' T',
    typsrc E t T ->
    typsrc E t' T' ->
    decidable (|t| ~p> |t'|).
Proof.
  intros.
  apply pared_dec with (T := |T|) (T' := |T'|) (E := erase_ctx E).
  apply* typsrc_to_typera.
  apply* typsrc_to_typera.
Qed.

(* ********************************************************************** *)
(** Lemmas of typing renaming *)

Lemma typsrc_rename_eq : forall x y E e T,
  x \notin (fv e \u fv T) -> y \notin (dom E \u fv e) ->
  typsrc (E & (x ~ T)) (e ^ x) T ->
  typsrc (E & (y ~ T)) (e ^ y) T.
Proof.
  intros x y E e T Fr1 Fr2 H.
  destruct (eq_var_dec x y).
  subst; eauto.
  assert (wf (E & x ~ T)) by auto.
  inversions H0. elimtype False. apply* empty_push_inv.
  destruct (eq_push_inv H1) as [Eq1 [Eq2 Eq3]].
  subst.
  rewrite* (@subst_intro x e).
  assert ([x ~> src_fvar y] T = T).
  apply* subst_fresh.
  rewrite <- H0 at 2.
  apply_empty* (@typsrc_substitution T).
  apply (@typsrc_weaken); auto. 
  apply wf_cons.
  assert (dom (E & y ~ T) = singleton y \u dom E) by (apply dom_push).
  rewrite H4. auto.
  assert (E & y ~ T & empty = E & y ~ T) by (apply concat_empty_r).
  rewrite <- H4.
  apply (@typsrc_weaken).
  rewrite* concat_empty_r.
  rewrite* concat_empty_r.
Qed.

Lemma typsrc_rename : forall x y E e T1 T2,
  x \notin (fv e \u fv T2) -> y \notin (dom E \u fv e) ->
  typsrc (E & (x ~ T1)) (e ^ x) (T2 ^ x) ->
  typsrc (E & (y ~ T1)) (e ^ y) (T2 ^ y).
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (eq_var_dec x y).
  subst; eauto.
  assert (wf (E & x ~ T1)) by auto.
  inversions H0. elimtype False. apply* empty_push_inv.
  destruct (eq_push_inv H1) as [Eq1 [Eq2 Eq3]].
  subst.
  rewrite* (@subst_intro x e).
  rewrite* (@subst_intro x T2).
  apply_empty* (@typsrc_substitution T1).
  apply (@typsrc_weaken); auto. 
  apply wf_cons.
  assert (dom (E & y ~ T1) = singleton y \u dom E) by (apply dom_push).
  rewrite H0. auto.
  assert (E & y ~ T1 & empty = E & y ~ T1) by (apply concat_empty_r).
  rewrite <- H0.
  apply (@typsrc_weaken).
  rewrite* concat_empty_r.
  rewrite* concat_empty_r.
Qed.

(* ********************************************************************** *)
(** ** Main Results *)

(* ********************************************************************** *)
(** Typing is unique *)

Lemma typsrc_unique : forall E e T1 T2,
  typsrc E e T1 ->
  typsrc E e T2 ->
  T1 = T2.
Proof.
  intros E e T1 T2 Typ1 Typ2.
  generalize dependent T2.
  induction Typ1; intros T' Typ'; inversion Typ'; subst; eauto.
  eapply binds_func; eauto.
  f_equal; eauto.
  pick_fresh x.
  apply open_var_inj with (x := x); eauto.
  pose (IHTyp1_1 (src_prod U0 T0) H2).
  injection e.
  intros. subst.
  auto.
Qed.

(* ********************************************************************** *)
(** Type checking is decidable *)


Lemma typsrc_decidable : forall E e,
  termsrc e -> wf E -> decidable (exists T, typsrc E e T).
Proof.
  intros E e Trm Wf.
  generalize dependent E.
  induction Trm; intros E Wf.

  (* Case Var *)
  destruct (@binds_lookup_dec x E) as [[T H] | H].
  left; eauto. right. intros [T J]. inversion J; subst; eauto.

  (* Case App *)
  destruct (IHTrm1 E Wf) as [[T H] | H]; eauto.
  destruct (IHTrm2 E Wf) as [[S J] | J]; eauto.
  destruct T;
    match goal with
    | [ H: typsrc ?E ?t1 (src_prod ?P1 ?P2) |-
        decidable (exists Q, typsrc ?E (src_app ?t1 ?t2) Q) ] => auto
    | [ H: typsrc ?E ?t1 ?P |-
        decidable (exists Q, typsrc ?E (src_app ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        match goal with
        | [H2: typsrc E t1 (src_prod ?U ?T) |- _] =>
          assert (K: P = src_prod U T); eauto using typsrc_unique;
            inversion K
        end
    end.
  
    destruct (eq_typ_dec T1 S). subst. left; eauto.
    right. intros [S' J'].
    inversion J'; subst.
    assert (U = S); eauto using typsrc_unique.
    assert (src_prod T1 T2 = src_prod U T); eauto using typsrc_unique.
    inversion H1; subst; eauto using typsrc_unique.
    
    right. intros [S' J']. inversion J'; subst; eauto.
    right. intros [S' J']. inversion J'; subst; eauto.

  (* Case Star *)
  left. exists* src_star.

  (* Case Lam *)
  destruct (IHTrm E Wf) as [[T H2] | H2]; eauto.
  destruct T;
    match goal with
    | [ H: typsrc ?E ?t1 src_star |-
        decidable (exists Q, typsrc ?E (src_abs ?t1 ?t2) Q) ] => auto
    | [ H: typsrc ?E ?t1 ?P |-
        decidable (exists Q, typsrc ?E (src_abs ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        match goal with
        | [H2: typsrc E (src_prod t1 ?T) src_star |- _] =>
          destruct (typsrc_prod_inv H2);
          assert (K: P = src_star); eauto using typsrc_unique;
            inversion K
        end
    end.
      
    pick_fresh x.
    assert (Fr' : x \notin L) by auto.
    assert (Wf': wf (E & x ~ t1)).
    apply* wf_cons.
    destruct (H0 x Fr' (E & x ~ t1) Wf') as [[S J] | J].
    pose (S' := close_var x S).
    assert (x \notin fv S') by (apply close_var_fresh).
    assert (S = S' ^ x).
    apply* close_var_open.
    rewrite -> H3 in J.
    pose (typsrc_wf_from_typing J).
    assert (src_star = src_star ^ x) by auto.
    rewrite -> H4 in t.
    left. exists (src_prod t1 S').
    apply typsrc_abs with (L := L \u fv t2 \u dom E).
    apply typsrc_prod with (L := L \u fv S' \u dom E).
    auto. intros.
    assert (src_star = src_star ^ x0) by auto.
    rewrite H6.
    apply typsrc_rename with (x := x) (y := x0).
    assert (fv src_star = \{}). auto.
    rewrite H7. auto. auto. auto.
    intros.
    apply typsrc_rename with (x := x) (y := x0).
    auto. auto. auto.
    
    right. intros [S K]. inversion K; subst.
    apply J. destruct (typsrc_prod_inv H5).
    pick_fresh y.
    exists* (T ^ x).
    apply* typsrc_rename.

    right. intros [S K]. inversion K; subst.
    apply H2. destruct (typsrc_prod_inv H5).
    exists* src_star.

  (* Case Pi *)
  destruct (IHTrm E Wf) as [[T H2] | H2]; eauto.
  destruct T;
    match goal with
    | [ H: typsrc ?E ?t1 src_star |-
        decidable (exists Q, typsrc ?E (src_prod ?t1 ?t2) Q) ] => auto
    | [ H: typsrc ?E ?t1 ?P |-
        decidable (exists Q, typsrc ?E (src_prod ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        assert (K: P = src_star); eauto using typsrc_unique;
          inversion K
    end.

    pick_fresh x.
    assert (Fr' : x \notin L) by auto.
    assert (Wf': wf (E & x ~ t1)).
    apply* wf_cons.
    destruct (H0 x Fr' (E & x ~ t1) Wf') as [[S J] | J].
    destruct S;
      match goal with
      | [ H: typsrc (?E & ?x ~ ?t1) (?t2 ^ ?x) src_star |-
          decidable (exists Q, typsrc ?E (src_prod ?t1 ?t2) Q) ] => auto
      | [ H: typsrc (?E & ?x ~ ?t1) (?t2 ^ ?x) ?P |-
          decidable (exists Q, typsrc ?E (src_prod ?t1 ?t2) Q) ] =>
        right; intros [S' J']; inversion J'; subst;
          match goal with
          | [ H7: forall _, _ -> typsrc _ _ src_star |- _ ] =>
            pick_fresh y;
              assert (Fr'': y \notin L0) by auto;
              pose (t := H7 y Fr'');
              assert (H1: src_star = src_star ^ y) by auto;
              rewrite H1 in t;
              assert (EqFv: fv src_star = \{}) by auto;
              assert (H3: typsrc (E & x ~ t1) (t2 ^ x) (src_star ^ x)) by
                  (apply typsrc_rename with (x := y) (y := x); [rewrite EqFv; auto | auto | auto]);
              assert (K : P = src_star); eauto using typsrc_unique;
                inversion K
          end
      end.

      assert (src_star = src_star ^ x) by auto.
      left. exists src_star.
      apply typsrc_prod with (L := L \u fv t2 \u dom E).
      auto. intros.
      assert (src_star = src_star ^ x0) by auto.
      rewrite H4.
      apply typsrc_rename with (x := x) (y := x0).
      assert (fv src_star = \{}). auto.
      rewrite H5. auto. auto.
      rewrite <- H1.
      auto.

    right. intros [S K]. inversion K; subst.
    apply J. exists src_star.
    pick_fresh y.
    assert (Fr'': y \notin L0) by auto.
    pose (H7 y Fr'').
    assert (src_star = src_star ^ y) by auto.
    rewrite H1 in t.
    assert (typsrc (E & x ~ t1) (t2 ^ x) (src_star ^ x)).
    apply typsrc_rename with (x := y) (y := x).
    assert (fv src_star = \{}) by auto.
    rewrite H3. auto. auto. auto.
    assert (src_star = src_star ^ x) by auto.
    rewrite -> H4. auto.

    right. intros [S K]. inversion K; subst.
    apply H2.
    exists* src_star.

  (* Case Mu *)
  destruct (IHTrm E Wf) as [[T H2] | H2]; eauto.
  destruct T;
    match goal with
    | [ H: typsrc ?E ?t1 src_star |-
        decidable (exists Q, typsrc ?E (src_mu ?t1 ?t2) Q) ] => auto
    | [ H: typsrc ?E ?t1 ?P |-
        decidable (exists Q, typsrc ?E (src_mu ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        assert (K: P = src_star); eauto using typsrc_unique;
          inversion K
    end.
    
    pick_fresh x.
    assert (Fr' : x \notin L) by auto.
    assert (Wf': wf (E & x ~ t1)).
    apply* wf_cons.
    destruct (H0 x Fr' (E & x ~ t1) Wf') as [[S J] | J].
    destruct (eq_typ_dec t1 S).
    left. exists t1.
    apply typsrc_mu with (L := L \u fv t2 \u dom E).
    auto. intros. subst.
    apply typsrc_rename_eq with (x := x) (y := x0).
    auto. auto. auto.
    right. intros [S' K]. inversion K; subst.
    pick_fresh y.
    assert (Fr'': y \notin L0) by auto.
    pose (H7 y Fr'').
    assert (typsrc (E & x ~ S') (t2 ^ x) S').
    apply typsrc_rename_eq with (x := y) (y := x).
    auto. auto. auto.
    assert (K' : S = S'); eauto using typsrc_unique.
    
    right. intros [S K]. inversion K; subst.
    apply J. exists S.
    pick_fresh y.
    assert (Fr'': y \notin L0) by auto.
    pose (H7 y Fr'').
    apply typsrc_rename_eq with (x := y) (y := x).
    auto. auto. auto.

    right. intros [S K]. inversion K; subst.
    apply H2.
    exists* src_star.

  (* Case CastUp *)
  destruct (IHTrm1 E Wf) as [[T H] | H]; eauto.
  destruct (IHTrm2 E Wf) as [[S J] | J]; eauto.
  destruct T;
    match goal with
    | [ H: typsrc ?E ?t1 src_star |-
        decidable (exists Q, typsrc ?E (src_castup ?t1 ?t2) Q) ] => auto
    | [ H: typsrc ?E ?t1 ?P |-
        decidable (exists Q, typsrc ?E (src_castup ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        assert (K: P = src_star); eauto using typsrc_unique;
          inversion K
    end. 
    
    pose (typsrc_wf_from_typing J).
    destruct (reduct_dec H t) as [L | R].
    left.
    exists t1. apply typsrc_castup with (T := S).
    auto. auto. auto.
    right. intros [T' P]. destruct (typsrc_castup_inv P) as [A [B [C [D F]]]].
    subst. assert (S = A) by (apply* typsrc_unique).
    rewrite <- H0 in F. auto.

    right. intros [S' J']. inversion J'; subst; eauto.
    right. intros [S' J']. inversion J'; subst; eauto.

  (* Case CastDn *)
  destruct (IHTrm1 E Wf) as [[T H] | H]; eauto.
  destruct (IHTrm2 E Wf) as [[S J] | J]; eauto.
  destruct T;
    match goal with
    | [ H: typsrc ?E ?t1 src_star |-
        decidable (exists Q, typsrc ?E (src_castdn ?t1 ?t2) Q) ] => auto
    | [ H: typsrc ?E ?t1 ?P |-
        decidable (exists Q, typsrc ?E (src_castdn ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        assert (K: P = src_star); eauto using typsrc_unique;
          inversion K
    end. 
    
    pose (typsrc_wf_from_typing J).
    destruct (reduct_dec t H) as [L | R].
    left.
    exists t1. apply typsrc_castdn with (T := S).
    auto. auto. auto.
    right. intros [T' P]. destruct (typsrc_castdn_inv P) as [A [B [C [D F]]]].
    subst. assert (S = A) by (apply* typsrc_unique).
    rewrite <- H0 in F. auto.

    right. intros [S' J']. inversion J'; subst; eauto.
    right. intros [S' J']. inversion J'; subst; eauto.
Qed.

