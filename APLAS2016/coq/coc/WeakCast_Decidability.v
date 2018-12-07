(***************************************************************************
* WeakCast - Decidability of Type Checking                                 *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN WeakCast_Definitions WeakCast_Infrastructure WeakCast_Soundness LibReflect.
Implicit Types x : var.

Definition decidable (P : Prop) := (P \/ ~ P).

(* ********************************************************************** *)
(** Lemmas of decidability *)

(** Equality of terms *)
Lemma eq_typ_dec : forall (T T' : trm),
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

(** A term is a value *)
Lemma value_dec : forall E t T,
    typing E t T ->
    decidable (value t).
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  left*.
  right*. intros P. inversion P.
  left*.
  left*.
  right*. intros P. inversion P.
  right*. intros P. inversion P.
  destruct (IHTyp2 Typ2) as [P | Q].
  left. apply* value_castup.
  right. intros P. inversions P. auto.
  right*. intros P. inversion P.
Qed.

(** A term can be reduced *)
Lemma reduct_dec : forall E t T,
    typing E t T ->
    decidable (exists t', t ~~> t').
Proof.
  introv Typ. lets Typ': Typ. inductions Typ.
  right. intros [S J]. inversion J.
  right. intros [S J]. inversion J.
  right. intros [S J]. inversion J.
  right. intros [S J]. inversion J.
  
  destruct (value_dec Typ1) as [Val | Q].
  inversions Typ1; inversions Val. left. exists* (t0 ^^ u).
  inversions H1.
  inversions Typ1. right. intros [T' P]. inversion P. inversion H5.
  destruct Q. apply value_lam. assert (term (trm_app (trm_abs U t0) u)) by auto. inversion H. auto.
  assert (typing E (trm_app t0 u0) (trm_prod U T)).
  rewrite <- H.
  apply* typing_app.
  destruct (IHTyp1 H1) as [[t' L] | R].
  left. exists* (trm_app t' u).
  right. intros [t' P]. inversions P. destruct R.
  exists* e1'.
  left. exists* (trm_app (t0 ^^ trm_mu (trm_prod U T) t0) u).
  inversion H1.
  assert (typing E (trm_castdn t0) (trm_prod U T)).
  apply* typing_castdn.
  destruct (IHTyp1 H1) as [[t' L] | R].
  left. exists* (trm_app t' u).
  right. intros [t' P]. inversions P. destruct R.
  exists* e1'.

  left. exists* (t ^^ trm_mu T t).
  
  destruct (value_dec Typ2) as [Val | Q].
  right*. intros [t' P]. inversions P.
  apply* value_cannot_red.
  destruct (IHTyp2 Typ2) as [[t' L] | R].
  left. exists* (trm_castup U t').
  right. intros [t' P]. inversions P. destruct R.
  exists* e'.
  
  destruct (value_dec Typ) as [Val | Q].
  inversions Typ; inversions Val.
  inversion H. inversion H. inversion H.
  left. exists* t0.
  destruct (IHTyp Typ) as [[t' L] | R].
  left. exists* (trm_castdn t').
  right. intros [t' P]. inversions P. destruct R.
  exists* e'. destruct Q. apply* value_castup.
Qed.

(* ********************************************************************** *)
(** Lemmas of typing renaming *)

Lemma typing_rename_eq : forall x y E e T,
  x \notin (fv e \u fv T) -> y \notin (dom E \u fv e) ->
  typing (E & (x ~ T)) (e ^ x) T ->
  typing (E & (y ~ T)) (e ^ y) T.
Proof.
  intros x y E e T Fr1 Fr2 H.
  destruct (eq_var_dec x y).
  subst; eauto.
  assert (wf (E & x ~ T)) by auto.
  inversions H0. elimtype False. apply* empty_push_inv.
  destruct (eq_push_inv H1) as [Eq1 [Eq2 Eq3]].
  subst.
  rewrite* (@subst_intro x e).
  assert ([x ~> trm_fvar y] T = T).
  apply* subst_fresh.
  rewrite <- H0 at 2.
  apply_empty* (@typing_substitution T).
  apply (@typing_weaken); auto. 
  apply wf_cons.
  assert (dom (E & y ~ T) = singleton y \u dom E) by (apply dom_push).
  rewrite H4. auto.
  assert (E & y ~ T & empty = E & y ~ T) by (apply concat_empty_r).
  rewrite <- H4.
  apply (@typing_weaken).
  rewrite* concat_empty_r.
  rewrite* concat_empty_r.
Qed.

Lemma typing_rename : forall x y E e T1 T2,
  x \notin (fv e \u fv T2) -> y \notin (dom E \u fv e) ->
  typing (E & (x ~ T1)) (e ^ x) (T2 ^ x) ->
  typing (E & (y ~ T1)) (e ^ y) (T2 ^ y).
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
  apply_empty* (@typing_substitution T1).
  apply (@typing_weaken); auto. 
  apply wf_cons.
  assert (dom (E & y ~ T1) = singleton y \u dom E) by (apply dom_push).
  rewrite H0. auto.
  assert (E & y ~ T1 & empty = E & y ~ T1) by (apply concat_empty_r).
  rewrite <- H0.
  apply (@typing_weaken).
  rewrite* concat_empty_r.
  rewrite* concat_empty_r.
Qed.

(* ********************************************************************** *)
(** Typing is unique *)

Lemma typing_unique : forall E e T1 T2,
  typing E e T1 ->
  typing E e T2 ->
  T1 = T2.
Proof.
  intros E e T1 T2 Typ1 Typ2.
  generalize dependent T2.
  induction Typ1; intros T' Typ'; inversion Typ'; subst; eauto.
  eapply binds_func; eauto.
  f_equal; eauto.
  pick_fresh x.
  apply open_var_inj with (x := x); eauto.
  pose (IHTyp1_1 (trm_prod U0 T0) H2).
  injection e.
  intros. subst.
  auto.
  pose (IHTyp1 T0 H1).
  rewrite <- e in H3.
  pose (reduct_determ H H3).
  auto.
Qed.

(* ********************************************************************** *)
(** Type checking is decidable *)

Lemma typing_decidable : forall E e,
  term e -> wf E -> decidable (exists T, typing E e T).
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
    | [ H: typing ?E ?t1 (trm_prod ?P1 ?P2) |-
        decidable (exists Q, typing ?E (trm_app ?t1 ?t2) Q) ] => auto
    | [ H: typing ?E ?t1 ?P |-
        decidable (exists Q, typing ?E (trm_app ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        match goal with
        | [H2: typing E t1 (trm_prod ?U ?T) |- _] =>
          assert (K: P = trm_prod U T); eauto using typing_unique;
            inversion K
        end
    end.
  
    destruct (eq_typ_dec T1 S). subst. left; eauto.
    right. intros [S' J'].
    inversion J'; subst.
    assert (U = S); eauto using typing_unique.
    assert (trm_prod T1 T2 = trm_prod U T); eauto using typing_unique.
    inversion H1; subst; eauto using typing_unique.
    
    right. intros [S' J']. inversion J'; subst; eauto.
    right. intros [S' J']. inversion J'; subst; eauto.

  (* Case Star *)
  left. exists* trm_star.

  (* Case Lam *)
  destruct (IHTrm E Wf) as [[T H2] | H2]; eauto.
  destruct T;
    match goal with
    | [ H: typing ?E ?t1 trm_star |-
        decidable (exists Q, typing ?E (trm_abs ?t1 ?t2) Q) ] => auto
    | [ H: typing ?E ?t1 ?P |-
        decidable (exists Q, typing ?E (trm_abs ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        match goal with
        | [H2: typing E (trm_prod t1 ?T) trm_star |- _] =>
          destruct (typing_prod_inv H2);
          assert (K: P = trm_star); eauto using typing_unique;
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
    pose (typing_wf_from_typing J).
    assert (trm_star = trm_star ^ x) by auto.
    rewrite -> H4 in t.
    left. exists (trm_prod t1 S').
    apply typing_abs with (L := L \u fv t2 \u dom E).
    apply typing_prod with (L := L \u fv S' \u dom E).
    auto. intros.
    assert (trm_star = trm_star ^ x0) by auto.
    rewrite H6.
    apply typing_rename with (x := x) (y := x0).
    assert (fv trm_star = \{}). auto.
    rewrite H7. auto. auto. auto.
    intros.
    apply typing_rename with (x := x) (y := x0).
    auto. auto. auto.
    
    right. intros [S K]. inversion K; subst.
    apply J. destruct (typing_prod_inv H5).
    pick_fresh y.
    exists* (T ^ x).
    apply* typing_rename.

    right. intros [S K]. inversion K; subst.
    apply H2. destruct (typing_prod_inv H5).
    exists* trm_star.

  (* Case Pi *)
  destruct (IHTrm E Wf) as [[T H2] | H2]; eauto.
  destruct T;
    match goal with
    | [ H: typing ?E ?t1 trm_star |-
        decidable (exists Q, typing ?E (trm_prod ?t1 ?t2) Q) ] => auto
    | [ H: typing ?E ?t1 ?P |-
        decidable (exists Q, typing ?E (trm_prod ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        assert (K: P = trm_star); eauto using typing_unique;
          inversion K
    end.

    pick_fresh x.
    assert (Fr' : x \notin L) by auto.
    assert (Wf': wf (E & x ~ t1)).
    apply* wf_cons.
    destruct (H0 x Fr' (E & x ~ t1) Wf') as [[S J] | J].
    destruct S;
      match goal with
      | [ H: typing (?E & ?x ~ ?t1) (?t2 ^ ?x) trm_star |-
          decidable (exists Q, typing ?E (trm_prod ?t1 ?t2) Q) ] => auto
      | [ H: typing (?E & ?x ~ ?t1) (?t2 ^ ?x) ?P |-
          decidable (exists Q, typing ?E (trm_prod ?t1 ?t2) Q) ] =>
        right; intros [S' J']; inversion J'; subst;
          match goal with
          | [ H7: forall _, _ -> typing _ _ trm_star |- _ ] =>
            pick_fresh y;
              assert (Fr'': y \notin L0) by auto;
              pose (t := H7 y Fr'');
              assert (H1: trm_star = trm_star ^ y) by auto;
              rewrite H1 in t;
              assert (EqFv: fv trm_star = \{}) by auto;
              assert (H3: typing (E & x ~ t1) (t2 ^ x) (trm_star ^ x)) by
                  (apply typing_rename with (x := y) (y := x); [rewrite EqFv; auto | auto | auto]);
              assert (K : P = trm_star); eauto using typing_unique;
                inversion K
          end
      end.

      assert (trm_star = trm_star ^ x) by auto.
      left. exists trm_star.
      apply typing_prod with (L := L \u fv t2 \u dom E).
      auto. intros.
      assert (trm_star = trm_star ^ x0) by auto.
      rewrite H4.
      apply typing_rename with (x := x) (y := x0).
      assert (fv trm_star = \{}). auto.
      rewrite H5. auto. auto.
      rewrite <- H1.
      auto.

    right. intros [S K]. inversion K; subst.
    apply J. exists trm_star.
    pick_fresh y.
    assert (Fr'': y \notin L0) by auto.
    pose (H7 y Fr'').
    assert (trm_star = trm_star ^ y) by auto.
    rewrite H1 in t.
    assert (typing (E & x ~ t1) (t2 ^ x) (trm_star ^ x)).
    apply typing_rename with (x := y) (y := x).
    assert (fv trm_star = \{}) by auto.
    rewrite H3. auto. auto. auto.
    assert (trm_star = trm_star ^ x) by auto.
    rewrite -> H4. auto.

    right. intros [S K]. inversion K; subst.
    apply H2.
    exists* trm_star.

  (* Case Mu *)
  destruct (IHTrm E Wf) as [[T H2] | H2]; eauto.
  destruct T;
    match goal with
    | [ H: typing ?E ?t1 trm_star |-
        decidable (exists Q, typing ?E (trm_mu ?t1 ?t2) Q) ] => auto
    | [ H: typing ?E ?t1 ?P |-
        decidable (exists Q, typing ?E (trm_mu ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        assert (K: P = trm_star); eauto using typing_unique;
          inversion K
    end.
    
    pick_fresh x.
    assert (Fr' : x \notin L) by auto.
    assert (Wf': wf (E & x ~ t1)).
    apply* wf_cons.
    destruct (H0 x Fr' (E & x ~ t1) Wf') as [[S J] | J].
    destruct (eq_typ_dec t1 S).
    left. exists t1.
    apply typing_mu with (L := L \u fv t2 \u dom E).
    auto. intros. subst.
    apply typing_rename_eq with (x := x) (y := x0).
    auto. auto. auto.
    right. intros [S' K]. inversion K; subst.
    pick_fresh y.
    assert (Fr'': y \notin L0) by auto.
    pose (H7 y Fr'').
    assert (typing (E & x ~ S') (t2 ^ x) S').
    apply typing_rename_eq with (x := y) (y := x).
    auto. auto. auto.
    assert (K' : S = S'); eauto using typing_unique.
    
    right. intros [S K]. inversion K; subst.
    apply J. exists S.
    pick_fresh y.
    assert (Fr'': y \notin L0) by auto.
    pose (H7 y Fr'').
    apply typing_rename_eq with (x := y) (y := x).
    auto. auto. auto.

    right. intros [S K]. inversion K; subst.
    apply H2.
    exists* trm_star.

  (* Case CastUp *)
  destruct (IHTrm1 E Wf) as [[T H] | H]; eauto.
  destruct (IHTrm2 E Wf) as [[S J] | J]; eauto.
  destruct T;
    match goal with
    | [ H: typing ?E ?t1 trm_star |-
        decidable (exists Q, typing ?E (trm_castup ?t1 ?t2) Q) ] => auto
    | [ H: typing ?E ?t1 ?P |-
        decidable (exists Q, typing ?E (trm_castup ?t1 ?t2) Q) ] =>
      right; intros [S' J']; inversion J'; subst;
        assert (K: P = trm_star); eauto using typing_unique;
          inversion K
    end. 
    
    destruct (reduct_dec H) as [[t1' L] | R].
    destruct (eq_typ_dec S t1').
    left. subst.
    exists t1. apply typing_castup with (T := t1').
    auto. auto. auto.
    right. intros [T' P]. destruct (typing_castup_inv P) as [A [B [C [D F]]]].
    subst. assert (S = A) by (apply* typing_unique).
    subst. assert (A = t1') by (apply* reduct_determ).
    auto.
    right. intros [T' P]. destruct (typing_castup_inv P) as [A [B [C [D F]]]]. destruct R. exists* A.
    right. intros [S' J']. inversion J'; subst; eauto.
    right. intros [S' J']. inversion J'; subst; eauto.

  (* Case CastDn *)
  destruct (IHTrm E Wf) as [[T H] | H]; eauto.
  pose (typing_wf_from_typing H).
  destruct (reduct_dec t) as [[t' A] | B].
  left. exists* t'.
  right. intros [T0 P]. inversions P. destruct B.
  assert (T = T1) by (apply* typing_unique).
  subst. exists* T0.
  right. intros [T P]. inversions P. destruct H.
  exists* T0.
Qed.
