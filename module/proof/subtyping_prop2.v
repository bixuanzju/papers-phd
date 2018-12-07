Set Implicit Arguments.

Require Import definitions infrastructure axioms.
Require Import LibLN List.



(*

discuss

1. subtyping proof and elaboration proof: mutual recursion, see FIXME1

 *)

Axiom typ_weaken : forall G E F e T,
    has_type (E & G) e T ->
    wft (E & F & G) ->
    has_type (E & F & G) e T.


Inductive Result : list DExp -> list (var * DExp) -> DExp -> DExp -> (TExp -> TExp) -> Prop :=
| RBNil : forall c A B S,
    (forall Γ Ω E a b d,
        trans_ctx_alg Γ Ω ->
        elab_typing_alg Γ E Inf (substS S A) d ->
        elab_typing_alg Γ (substS S A) Chk DStar a ->
        elab_typing_alg Γ (substS S B) Chk DStar b ->
        has_type Ω d a ->
        has_type Ω (c d) b) ->
    Result nil S A B c
| RFVar : forall x T D S,
    Result (T :: D) S (DFVar x) (DFVar x) (fun e => e)
| RLam : forall L c B C T D S,
    (forall x, x \notin L -> Result D ((x, T) :: S) (B ^ x) (C ^ x) c) ->
    Result (T :: D) S (DLam B) (DLam C) (fun e => TCastup (c (TCastdn e)))
| RApp : forall c B C D (S : list (var * DExp)) (E T : DExp),
    Result (E :: T :: D) S B C c -> Result (T :: D) S (DApp B E) (DApp C E) c.

Hint Constructors Result.


Lemma apps_lemma : forall D2 D1 S A B c,
    subM (D1 ++ D2) S A B c -> Result (D1 ++ D2) S A B c -> Result D2 S (apps A D1) (apps B D1) c.
Proof.

  destruct D2; introv AsubB AresB.
  rewrite (app_nil_r D1) in *.
  induction AresB.
  (* Base case *)
  - simpl. apply* RBNil.
  (* Var *)
  - simpl. apply* RBNil. intros.
    lets* : (elab_coherence H1 H2). subst~.
  (* Lam case *)
  - lets RAB : regular_subM AsubB.
    inverts AsubB.
    Require Import FunctionalExtensionality.
    assert (forall y, TCastup (c0 (TCastdn y)) = TCastup (c (TCastdn y))).
    intros y.
    apply equal_f with (x := y) in H7. auto.
    apply coercion_eq in H1.
    clear H7; subst.
    pick_fresh x.
    forwards* BresC : H x.
    forwards* BsresCs : H0 x.
    inverts BsresCs.
    apply RBNil; intros.
    forwards* : H4 x.
    lets [? [? ?]]: sub_S H8.
    rewrite cons_to_push in H9, H10.
    lets* : contains_cons H10.
    lets : ok_push_inv_ok H9.
    unfold contains_terms in H10.
    forwards* : H10 x T.
    admit. admit. admit.

    (*

    H5 and H6 should be impossible!!! We should have subtyping rule for annotation!


     *)

    (* assert (RedB : substS S (apps (DLam B) (T :: D)) ~~> substS ((x, T) :: S) (apps (B ^ x) D)). *)
    (* simpl. *)
    (* rewrite substS_apps. *)
    (* asserts_rewrite ((map (subst_source x T) D) = D). admit. (* because x is fresh *) *)
    (* apply* substS_sred. *)
    (* apply* apps_red. *)
    (* rewrite* <- subst_intro_s. *)


    (* assert (TyB : exists c, elab_typing_alg Γ (substS ((x, T) :: S) (apps (B ^ x) D)) Chk DStar c). *)
    (* apply reduction_preserve_kind with (A := substS S (apps (DLam B) (T :: D))) (a := a); auto. *)


    (* assert (RedC : substS S (apps (DLam C) (T :: D)) ~~> substS ((x, T) :: S) (apps (C ^ x) D)). *)
    (* simpl. *)
    (* rewrite substS_apps. *)
    (* asserts_rewrite ((map (subst_source x T) D) = D). admit. (* because x is fresh *) *)
    (* apply* substS_sred. *)
    (* apply* apps_red. *)
    (* rewrite* <- subst_intro_s. *)

    (* assert (TyC : exists c, elab_typing_alg Γ (substS ((x, T) :: S) (apps (C ^ x) D)) Chk DStar c). *)
    (* apply reduction_preserve_kind with (A := substS S (apps (DLam C) (T :: D))) (a := b); auto. *)

    (* destruct TyB as [bb ?]. *)
    (* destruct TyC as [cc ?]. *)
    (* assert (a --> bb). apply (reduction_consistency RedB H5 H15). *)

    (* apply TyTCastUp with (t2 := cc). *)
    (* apply* H1. *)
    (* apply (reduction_consistency RedC H6 H16). *)


  (* app case *)
  - inverts* AsubB.

  (* Inductive case *)
  - generalize AsubB AresB. clear AsubB AresB. generalize S A B c d. clear d S A B c.
    induction D1; simpl; intros; auto.
    apply* IHD1.
    destruct D1. simpls*.
    simpls*.

Admitted.




Lemma sub_gen : forall c B C D S, subM D S B C c -> Result D S B C c.
Proof.
  intros.
  induction H using subM_ind'.

  (* Var *)
  - destruct* S1.
    apply RBNil.
    intros.
    lets : elab_coherence H1 H2. subst~.


  (* Star *)
  - apply RBNil. intros.
    lets : elab_coherence H1 H2. subst~.

  (* Pi *)
  - apply RBNil. intros.
    rewrite substS_pi in *.
    destruct (elab_pi_inv H5) as [e [f [? [TyA' [L0 TyB']]]]]. subst. clear H5.
    destruct (elab_pi_inv H4) as [g [h [? [TyA [L1 TyB]]]]]. subst. clear H4.
    apply_fresh TyTLam as y.
    forwards* [BsubB' Body] : H y.  rewrite Body. clear H.

    assert (Lset: y \notin L) by auto.
    assert (L0set :y \notin L0) by auto.
    assert (L1set:y \notin L1) by auto.
    assert (TyTB' : elab_typing_alg (Γ & y ~ substS S A') (substS S B' ^ y) Chk DStar (f $ y)) by (apply (TyB' y L0set)). clear TyB'.
    assert (TyTB : elab_typing_alg (Γ & y ~ substS S A) (substS S B ^ y) Chk DStar (h $ y)) by (apply (TyB y L1set)). clear TyB.
    clear Lset L0set L1set.
    forwards* BresB' : H0 y.
    inverts IHsubM. inverts BresB'.

    rewrite* <- close_var_open.
    lets [? [? ?]]: sub_S H1.

    assert (wft (Ω & y ~ e)).
    apply* wft_cons. admit. (* FIXME1 : this requires gen_wt_target, we have mutual recursive! *)

    assert (TyC1 : has_type (Ω & y ~ e) (c1 (TFVar y)) g).
    apply* H.
    apply_empty* typing_weaken.
    apply_empty* typing_weaken.

    assert (has_type (Ω & y ~ e) (TApp d (c1 (TFVar y))) (h $$ (c1 (TFVar y)))).
    apply* TyTApp.
    apply_empty* typ_weaken.

    assert (HA : elab_typing_alg (Γ & y ~ substS S A') (DApp E (DFVar y)) Inf (substS S B ^ y) ([y |~> c1 (TFVar y)] (TApp d (TFVar y)))).
    apply_empty* typing_narrowing. apply* subM_substS.
    apply* ATyApp.
    apply_empty * typing_weaken.
    simpl in HA.
    case_var.
    rewrite* subst_fresh in HA.

    apply* H4.
    rewrite* <- substS_open.

    rewrite subst_intro with (x := y); auto. rewrite~ <- substS_open.
    apply_empty* typing_narrowing. apply* subM_substS.
    apply* coercion_regular.
    rewrite~ <- substS_open.

    apply* coercion_regular.
    apply* term_app.
    apply* coercion_regular.

  (* Lam *)
  - apply_fresh* RLam as x.


  (* App *)
  - assert (forall A, DApp A T = apps A (T :: nil)). intros. auto.
    rewrite (H1 A). rewrite (H1 B). clear H1.
    apply* apps_lemma.

  (* Anno *)
  - admit.

  (* Merge1 *)
  - inverts IHsubM.
    apply RBNil. intros.
    rewrite substS_and in *.
    destruct (elab_and_inv H5) as [? [? [? [TyA TyB]]]]. subst.
    apply* H2.
    apply* and_eliminate1.

  (* Merge2 *)
  - inverts IHsubM.
    apply RBNil. intros.
    rewrite substS_and in *.
    destruct (elab_and_inv H5) as [? [? [? [TyA TyB]]]]. subst.
    apply* H2.
    apply* and_eliminate2.

  (* Merge3 *)
  - inverts IHsubM1.
    inverts IHsubM2.
    apply RBNil. intros.
    rewrite substS_and in H6.
    destruct (elab_and_inv H6) as [? [? [? [TyA TyB]]]]. subst.
    apply* TyTPair.


Admitted.

Lemma sub_prop2 : forall Γ Ω A B c a b d E,
    subM nil nil A B c ->
    elab_typing_alg Γ E Inf A d ->
    elab_typing_alg Γ A Chk DStar a ->
    elab_typing_alg Γ B Chk DStar b ->
    trans_ctx_alg Γ Ω ->
    has_type Ω d a ->
    has_type Ω (c d) b.
Proof.
  intros.
  pose (Res := sub_gen H).
  inverts* Res.
Qed.
