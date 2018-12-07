Set Implicit Arguments.
Require Import infrastructure definitions subtyping_prop2.
Require Import LibLN.

Require Import axioms.



(* See Theorem 3 of Complete and Easy Bidirectional Typechecking
for Higher-Rank Polymorphism *)
Lemma typing_substitution : forall T' F E A B T a b x Mode,
    elab_typing_alg E A Inf T' a ->
    elab_typing_alg (E & x ~ T' & F) B Mode T b ->
    elab_typing_alg (E & (map (subst_source x A) F)) ([x ~> A] B) Mode ([x ~> A] T) (subst x a b).
Proof.
  introv Typv Typt.
  gen_eq G: (E & x ~ T' & F). gen F.
  apply elab_induct with
  (P := fun (G:env DExp) B Mode T b (Typt : elab_typing_alg G B Mode T b) =>
          forall F, G = E & x ~ T' & F ->
               elab_typing_alg (E & map (subst_source x A) F) ([x ~> A] B) Mode ([x ~> A] T) ([x |~> a] b))
    (P0 := fun (G:env DExp) (W:awfs G) =>
             forall F, G = E & x ~ T' & F ->
                  awfs (E & map (subst_source x A) F));
    intros; subst; simpls*.

   (* var *)
   - case_var.
     binds_mid~.
     rewrite~ subst_fresh_s. apply_empty* typing_weaken.
     apply~ ATyVar. destruct~ (binds_not_middle_inv b0) as [K|[Fr K]].
     rewrite* subst_fresh_s.

   (* pi *)
   - apply_fresh* ATyPi as x.
     cross; auto. rewrite* subst_open_var.
     apply_ih_map_bind* H0.

   (* app *)
   - rewrite* subst_open_s.

   (* and *)
   - apply* ATyAnd.
     apply* ortho_subst.

   (* merge *)
   - apply* ATyMerge.
     apply* ortho_subst.

   (* lam *)
   - apply_fresh* ATyLam as x.
     cross; auto. rewrite* subst_open_var.
     apply_ih_map_bind* H0.

   (* castdn *)
   - apply* ATyCastDown.
     apply* subst_sred.

   (* castup *)
   - apply* ATyCastUp.
     apply* subst_sred.

   (* Sub *)
   - lets cShape : sub_shape s0.
     rewrite* co_substi_commute.

     apply* ATySub.
     apply* (@sub_subst nil nil).

   (* empty *)
   - false (empty_middle_inv H).
   (* cons *)
   - induction F using env_ind.
     rewrite concat_empty_r in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_empty. rewrite~ concat_empty_r.
     clear IHF. rewrite concat_assoc in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_push. rewrite* concat_assoc.
Qed.


Lemma typing_strengthen : forall Γ C c x,
    elab_typing_alg (Γ & x ~ C) C Chk DStar c ->
    elab_typing_alg Γ C Chk DStar c.
Proof.
  intros.
  destruct (regular_typing H) as [WFS ?].
  inverts WFS.
  false (empty_push_inv H2).

  destructs (eq_push_inv H1). subst.
  assert (elab_typing_alg (Γ & x ~ C) C Chk DStar e).
  apply_empty* typing_weaken.
  lets : (elab_coherence H H4). subst~.
Qed.


Lemma typing_wf_from_context : forall x U Γ,
  binds x U Γ ->
  awfs Γ ->
  exists e, elab_typing_alg Γ U Chk DStar e.
Proof.
  introv B W.
  induction Γ using env_ind.
  false* binds_empty_inv.

  destruct (binds_push_inv B) as [[? ?]|[? ?]].
  subst. inversions W. false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. subst.
  exists e. apply_empty* typing_weaken.
  destruct (wf_push_inv W). forwards~ [k P]: IHΓ.
  exists k. apply_empty* typing_weaken.
Qed.

Lemma typing_wf_from_typing : forall Γ A B e Mode,
    elab_typing_alg Γ A Mode B e ->
    exists e', elab_typing_alg Γ B Chk DStar e'.
Proof.
  induction 1; auto_star.

  (* var *)
  - destruct* (typing_wf_from_context H0).

  (* App *)
  - destruct IHelab_typing_alg1 as [e IHPi].
    destruct (elab_pi_inv IHPi) as [a [b [? [? [L IHB]]]]].
    exists (open b e2).
    pick_fresh x.
    rewrite~ (@subst_intro x).
    rewrite~ (@subst_intro_s x).
    asserts_rewrite~ (DStar = [x ~> E2] DStar).
    apply_empty* (@typing_substitution A).
    subst~.

  (* And *)
  - destruct IHelab_typing_alg1 as [a TyA].
    destruct IHelab_typing_alg2 as [b TyB].
    exists (TProd a b).
    apply ATySub with (c := (fun e => e)) (B := DStar); auto.

  (* Subsumption *)
  - destruct IHelab_typing_alg.
    lets* : sub_preserve H1.
Qed.

Lemma ctx_trans : forall Γ Ω x t T,
    trans_ctx_alg Γ Ω ->
    binds x T Γ ->
    elab_typing_alg Γ T Chk DStar t ->
    binds x t Ω.
Proof.
  introv Trans.
  gen x t T.
  induction Trans; intros.

  (* Empty *)
  false* binds_empty_inv.

  (* Cons *)
  destruct (binds_push_inv H0) as [[? ?]|[? ?]]. subst.
  apply typing_strengthen in H1.
  lets: elab_coherence H H1. subst~.

  apply~ binds_push_neq.
  apply IHTrans with (T := T0); auto.
  destruct (typing_wf_from_context H3) as [t' HH]; auto.
  assert (elab_typing_alg (Γ & x ~ T) T0 Chk DStar t').
  apply_empty* typing_weaken.
  lets: elab_coherence H1 H4. subst~.
Qed.



Definition P := fun (Γ : sctx) (A : DExp) (Mode : Dir) (B : DExp) (e : TExp) (Ty : elab_typing_alg Γ A Mode B e) =>
                   forall (Ω : env TExp) (b : TExp), trans_ctx_alg Γ Ω -> elab_typing_alg Γ B Chk DStar b -> has_type Ω e b.
Definition P0 := fun (Γ : sctx) (W : awfs Γ) => forall (Ω : env TExp), trans_ctx_alg Γ Ω -> wft Ω.

Lemma gen_wt_target : forall Γ Mode Ω A B e b,
    elab_typing_alg Γ A Mode B e ->
    trans_ctx_alg Γ Ω ->
    elab_typing_alg Γ B Chk DStar b ->
    has_type Ω e b.
Proof.
  introv Ty.
  gen Ω b.

  (* Why

  apply elab_induct with (P := P) (P0 := P0)

  doesn't work????

   *)
  apply (elab_induct P P0) with (d := A) (d0 := Mode); unfold P;
  intros; subst; simpls subst; autos; simpl.

  (* Star *)
  - asserts_rewrite (b = TStar).
    apply* elab_star_inv.
    unfold P0 in H.
    apply* TyTStar.

  (* Var *)
  - apply TyTVar.
    unfold P0 in H.
    apply* H.
    apply* ctx_trans.

  (* Pi *)
  - lets : elab_star_inv H2.
    subst.
    apply_fresh* TyTPi as y.
    apply* H0.
    apply ATySub with (c := (fun e => e)) (B := DStar); auto_star.


  (* App *)
  - lets [e' TyTy1] : typing_wf_from_typing e0.
    lets HH : elab_pi_inv TyTy1.
    destruct HH as [c [d [HH1 [HH2 [L HH3]]]]].
    subst.
    lets IHTy1' : H H1 TyTy1. clear H.
    lets IHTy2' : H0 H1 HH2. clear H0.
    pick_fresh y.
    forwards* TyB : HH3 y. clear HH3.
    assert (elab_typing_alg Γ0 ([y ~> E2] B0 ^ y) Chk ([y ~> E2] DStar) ([y |~> e2] d $ y)).
    apply_empty* (@typing_substitution A').
    simpl in H.
    rewrite* <- subst_intro_s in H.
    rewrite* <- subst_intro in H.

    lets : elab_coherence H2 H.
    subst*.

  (* And *)
  - lets : elab_star_inv H2.
    subst.
    apply* TyTProd.

  (* Merge *)
  - lets HH : elab_and_inv H2.
    destruct HH as [c [d [? [TyA TyB]]]].
    subst.
    apply* TyTPair.

  (* Lam *)
  - destruct (elab_pi_inv H2) as [c [d [HH1 [HH2 HH3]]]].
    subst.
    destruct HH3 as [L0 HH3].
    apply_fresh TyTLam as x.
    apply* H0.

  (* castdn *)
  - lets [? ?]: typing_wf_from_typing e0.
    apply* TyTCastDown.
    eapply reduction_consistency; eauto.

  (* castup *)
  - lets [? ?]: typing_wf_from_typing e0.
    apply* TyTCastUp.
    eapply reduction_consistency; eauto.

  (* Subsumption *)
  - lets [? ?]: typing_wf_from_typing e0.
    apply* sub_prop2.


  (* Empty context *)
  - unfold P0; intros.
    inverts* H.
    symmetry in H0.
    false (empty_push_inv H0).

  (* Finally! *)
  - unfold P0; intros.
    inverts H0.
    false (empty_push_inv H2).
    destructs (eq_push_inv H1); subst.
    apply wft_cons.
    lets : trans_dom H2.
    intros F. apply n. rewrite* H0.
    lets: elab_coherence H3 e1. subst~.
    apply* H.
    apply ATySub with (c := (fun e => e)) (B := DStar); auto.
Qed.

(* Print Assumptions gen_wt_target. *)

Definition almost_unique (A B : DExp) (d : Dir) : Prop :=
  match d with
  | Inf => A = B
  | Chk => True
  end.

Lemma typ_unique : forall Γ d E A B a b,
    elab_typing_alg Γ E d A a ->
    elab_typing_alg Γ E d B b ->
    almost_unique A B d.
Proof.
  introv H. gen B b.
  induction H; intros; unfold almost_unique; auto.

  (* Star *)
  - inverts* H0.

  (* Var *)
  - inverts H1.
    lets* : binds_func H0 H5.

  (* Pi *)
  - inverts* H2.

  (* App *)
  - inverts H2.
    apply IHelab_typing_alg1 in H5. simpl in H5.
    inverts* H5.
    
  (* And *)
  - inverts* H2.

  (* Merge *)
  - inverts H2.
    apply IHelab_typing_alg1 in H5. simpl in H5.
    apply IHelab_typing_alg2 in H7. simpl in H7.
    subst~.

  (* Ann *)
  - inverts* H1.
Qed.
