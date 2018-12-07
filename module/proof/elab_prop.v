Set Implicit Arguments.
Require Import infrastructure definitions subtyping_prop.
Require Import LibLN.


Scheme elab_induct := Induction for elab_typing Sort Prop with wf_induct := Induction for wfs3 Sort Prop.
Hint Constructors elab_typing wfs3.

(* ********************************************************************** *)
(** ** Inversion Lemmas for Typing *)

Lemma typing_star_inv : forall E e,
    elab_typing E DStar DStar e -> e = TStar.
Proof.

Admitted.

Lemma typing_pi_inv : forall Gamma A B e,
    elab_typing Gamma (DPi A B) DStar e -> exists a b,
      e = TPi a b /\ elab_typing Gamma A DStar a /\
      exists L, forall x, x \notin L ->
                elab_typing (Gamma & x ~ A) (B ^ x) DStar (b $ x).
Proof.
Admitted.

Lemma typing_and_inv : forall Gamma A B e,
    elab_typing Gamma (DAnd A B) DStar e ->
    exists a b, e = TProd a b /\ elab_typing Gamma A DStar a /\ elab_typing Gamma B DStar b.
Proof.
Admitted.


(* ********************************************************************** *)


Lemma regular_typing : forall Gamma A B e,
    elab_typing Gamma A B e ->
    wfs3 Gamma /\ ok Gamma /\ contains_terms Gamma /\ sterm A /\ sterm B /\ term e.
Proof.
  apply elab_induct with
    (P0 := fun Gamma (_ : wfs3 Gamma) => wfs3 Gamma /\ ok Gamma /\ contains_terms Gamma);
      unfolds contains_terms; intros; splits*.

  (* lam *)
  apply_fresh sterm_lam as y.
  forwards* : H0 y.
  apply_fresh term_lam as y.
  forwards* : H0 y.

  (* app *)
  destructs H.
  destructs H0.
  inverts* H4.
  pick_fresh y.
  assert (y \notin L) by auto.
  rewrite subst_intro_s with (x := y); auto.

  (* pi *)
  apply_fresh* sterm_pi as y.
  forwards * : H0 y.
  apply_fresh* term_pi as y.
  forwards * : H0 y.

  (* wf empty *)
  intros. false* binds_empty_inv.

  (* wf cons *)
  intros.
  destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst*.
Qed.

Lemma ok_from_wf : forall E, wfs3 E -> ok E.
Proof.
  induction 1. auto. autos* (regular_typing H0).
Qed.

Hint Extern 1 (ok ?E) => match goal with
  | H: wfs3 E |- _ => apply (ok_from_wf H)
  end.

Hint Extern 1 (wfs3 ?E) => match goal with
  | H: elab_typing E _ _ _ |- _ => apply (proj1 (regular_typing H))
  end.

Hint Extern 1 (sterm ?t) => match goal with
  | H: elab_typing _ t _ _ |- _ => apply (proj1 (proj44 (regular_typing H)))
  | H: elab_typing _ _ t _ |- _ => apply (proj1 (proj2 (proj44 (regular_typing H))))
  end.

Hint Extern 1 (term ?t) => match goal with
  | H: elab_typing _ _ _ t |- _ => apply (proj2 (proj2 (proj44 (regular_typing H))))
  end.



Lemma wf_push_inv : forall E x U,
  wfs3 (E & x ~ U) -> wfs3 E /\ sterm U.
Proof.
  introv W. inversions W.
  false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. subst~.
Qed.

Lemma wf_left : forall E F : sctx,
  wfs3 (E & F) -> wfs3 E.
Proof.
  intros. induction F using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   inversions H. false (empty_push_inv H1).
   destruct (eq_push_inv H0) as [? [? ?]]. subst~.
Qed.

Lemma fv_open_var : forall y x t,
  x <> y -> x \notin fv_source (t ^ y) -> x \notin fv_source t.
Proof.
  (* introv Neq. unfold open_source. generalize 0. *)
  (* induction t; simpl; intros; try notin_solve. *)
  (* specializes IHt1 n. auto. specializes IHt2 n. auto. *)
  (* specializes IHt1 n. auto. specializes IHt2 (S n). auto. *)
  (* specializes IHt1 n. auto. specializes IHt2 (S n). auto. *)
Admitted.

Lemma typing_fresh : forall E T e x,
  elab_typing E T DStar e -> x # E -> x \notin fv_source T.
Proof.
Admitted.


Lemma notin_fv_from_wf : forall E F x V,
  wfs3 (E & x ~ V & F) -> x \notin fv_source V.
Proof.
  intros.
  lets W: (wf_left H). inversions W.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. subst~.
    (*todo: factorize the above pattern *)
  apply* typing_fresh.
Qed.

Hint Extern 1 (?x \notin fv_source ?V) =>
  match goal with H: wfs3 (?E & x ~ V & ?F) |- _ =>
    apply (@notin_fv_from_wf E F) end.



Lemma typing_weaken : forall G E F e T c,
    elab_typing (E & G) e T c ->
    wfs3 (E & F & G) ->
    elab_typing (E & F & G) e T c.
Proof.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; eauto.

  (* case: var *)
  apply* Ty3Var. apply* binds_weaken.

  (* case: trm_abs *)
  apply_fresh* Ty3Lam as y.
  forwards TypP: (IHTyp G); auto.
  destruct (typing_pi_inv TypP) as [a [b [? [TyA [L0 TyB]]]]]. subst.
  apply_ih_bind* H0.

  (* case: trm_prod *)
  apply_fresh* Ty3Pi as y. apply_ih_bind* H0.
Qed.


Lemma typing_wf_from_context : forall x U E,
  binds x U E ->
  wfs3 E ->
  exists e, elab_typing E U DStar e.
Proof.
  introv B W.
  induction E using env_ind.
  false* binds_empty_inv.

  destruct (binds_push_inv B) as [[? ?]|[? ?]].
  subst. inversions W. false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. subst.
  exists e. apply_empty* typing_weaken.
  destruct (wf_push_inv W). forwards~ [k P]: IHE.
  exists k. apply_empty* typing_weaken.
Qed.


Ltac cross :=
  rewrite subst_open_var_s; try cross.

Tactic Notation "cross" "*" :=
  cross; autos*.


Lemma subst_value : forall x u e,
    svalue e ->
    sterm u ->
    svalue (subst_source x u e).
Proof.
  introv Val.
  induction Val; intros; simpl; auto.

  apply* svalue_lam.
  lets* : subst_term_s H0 H.

  apply* svalue_pi.
  lets* : subst_term_s H0 H.

  apply* svalue_inter.
  lets* : subst_term_s H0 H.
Qed.


Lemma red_subst : forall x A B C,
    B ~~> C ->
    sterm A ->
    [x ~> A] B ~~> [x ~> A] C.
Proof.
  introv Red. gen x A.
  induction Red; introv Well; simpl.

  rewrite subst_open_s; auto.
  apply sred_beta.
  lets* : (subst_term_s x Well H).
  apply* subst_value.

  apply* sred_app1.
  apply* sred_app2.
  apply* subst_value.

  apply* sred_castelem.
  apply* subst_value.

  apply* sred_castdn.
  apply* sred_castup.

  apply* sred_merge1.
  apply* sred_merge2.
  apply* subst_value.

  apply* sred_unmerge1.
  apply* sred_unmerge2.
Qed.

Lemma typing_substitution : forall T' F E A B T a b x,
    elab_typing E A T' a ->
    elab_typing (E & x ~ T' & F) B T b ->
    elab_typing (E & (map (subst_source x A) F)) ([x ~> A] B) ([x ~> A] T) (subst x a b).
Proof.
  introv Typv Typt.
  gen_eq G: (E & x ~ T' & F). gen F.
  apply elab_induct with
  (P := fun (G:env DExp) B T b (Typt : elab_typing G B T b) =>
          forall F, G = E & x ~ T' & F ->
               elab_typing (E & map (subst_source x A) F) ([x ~> A] B) ([x ~> A] T) ([x |~> a] b))
    (P0 := fun (G:env DExp) (W:wfs3 G) =>
             forall F, G = E & x ~ T' & F ->
                  wfs3 (E & map (subst_source x A) F));
    intros; subst; simpls subst; autos; simpl.

   (* var *)
   - case_var.
     binds_mid~.
     rewrite~ subst_fresh_s. apply_empty* typing_weaken.
     apply~ Ty3Var. destruct~ (binds_not_middle_inv b0) as [K|[Fr K]].
     rewrite* subst_fresh_s.
     admit.
   (* lam *)
   - apply_fresh* Ty3Lam as x.
     cross; auto. rewrite* subst_open_var.
     apply_ih_map_bind* H0.
   (* app *)
   - rewrite* subst_open_s.
   (* pi *)
   - apply_fresh* Ty3Pi as x.
     cross; auto. rewrite* subst_open_var.
     apply_ih_map_bind* H0.
   (* And *)
   - apply* Ty3And.
   (* Castdn *)
   - apply* Ty3CastDown.
     apply* red_subst.
   (* Castup *)
   - apply* Ty3CastUp.
     apply* red_subst.
   (* Merge *)
   - apply* Ty3Merge.
   (* Sub *)
   - apply* Ty3Sub.
     apply* subst_term.
     apply* sub_subst.

   (* empty *)
   - false (empty_middle_inv H).
   (* cons *)
   - induction F using env_ind.
     rewrite concat_empty_r in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_empty. rewrite~ concat_empty_r.
     clear IHF. rewrite concat_assoc in H0.
     destruct (eq_push_inv H0) as [? [? ?]]. subst.
     rewrite map_push. rewrite concat_assoc. apply* wfs3_cons.
Qed.



Lemma typing_strengthen : forall Gamma C c x,
    elab_typing (Gamma & x ~ C) C DStar c ->
    elab_typing Gamma C DStar c.
Proof.
  intros.
  destruct (regular_typing H) as [WFS ?].
  inverts WFS.
  false (empty_push_inv H2).

  destructs (eq_push_inv H1). subst.
  assert (elab_typing (Gamma & x ~ C) C DStar e).
  apply_empty* typing_weaken.
  lets : (elab_unique H H4). subst~.
Qed.




Lemma typing_wf_from_typing : forall E A B e,
    elab_typing E A B e ->
    exists e', elab_typing E B DStar e'.
Proof.
  induction 1; auto.

  (* star *)
  - exists* TStar.
  (* var *)
  - destruct* (typing_wf_from_context H0).
  (* Pi *)
  - exists* e.
  (* App *)
  - destruct IHelab_typing1 as [e IHPi].
    destruct (typing_pi_inv IHPi) as [a [b [? [? [L IHB]]]]].
    exists (open b e2).
    pick_fresh x.
    rewrite~ (@subst_intro x).
    rewrite~ (@subst_intro_s x).
    asserts_rewrite~ (DStar = [x ~> E2] DStar).
    apply_empty* (@typing_substitution A).

  - exists~ c.
  - exists~ b.
  (* And *)
  - destruct IHelab_typing1 as [a TyA].
    destruct IHelab_typing2 as [b TyB].
    exists* (TProd a b).
  (* Subsumption *)
  - destruct IHelab_typing as [b TyB].

    apply* (sub_preserve H2 TyB).
Qed.

Lemma ctx_trans : forall Gamma Gamma' x t T,
    trans_ctx Gamma Gamma' ->
    binds x T Gamma ->
    elab_typing Gamma T DStar t ->
    binds x t Gamma'.
Proof.
  introv Trans.
  gen x t T.
  induction Trans; intros.

  (* Empty *)
  false* binds_empty_inv.

  (* Cons *)
  destruct (binds_push_inv H0) as [[? ?]|[? ?]]. subst.
  apply typing_strengthen in H1.
  lets: elab_unique H H1. subst~.

  apply~ binds_push_neq.
  apply IHTrans with (T := T0); auto.
  destruct (typing_wf_from_context H3) as [t' HH]; auto.
  assert (elab_typing (sctx & x ~ T) T0 DStar t').
  apply_empty* typing_weaken.
  lets: elab_unique H1 H4. subst~.

Qed.




Lemma gen_wt_target: forall SE E A B b e,
    elab_typing SE A B e ->
    trans_ctx SE E ->
    elab_typing SE B DStar b ->
    has_type E e b.
Proof.
  introv Ty.
  gen E b.
  induction Ty; introv Ctx TransB.

  (* Star *)
  - asserts_rewrite (b = TStar).
    eapply typing_star_inv; eauto.
    apply TyTStar.
    eapply trans_wf; eauto.

  (* Var *)
  - apply TyTVar.
    apply (trans_wf H Ctx).
    apply (ctx_trans Ctx H0 TransB).

  (* lam *)
  - destruct (typing_pi_inv TransB) as [c [d [HH1 [HH2 HH3]]]].
    subst.
    destruct HH3 as [L0 HH3].
    apply_fresh TyTLam as x.
    apply* H0.
    apply trans_cons; auto.

  (* App *)
  - lets [e TyTy1] : typing_wf_from_typing Ty1.
    lets H : typing_pi_inv TyTy1.
    destruct H as [c [d [HH1 [HH2 [L HH3]]]]].
    subst.
    lets IHTy1' : IHTy1 Ctx TyTy1. clear IHTy1.
    lets IHTy2' : IHTy2 Ctx HH2. clear IHTy2.
    pick_fresh y.
    forwards* TyB : HH3 y. clear HH3.
    assert (elab_typing SE ([y ~> E2] B ^ y) ([y ~> E2] DStar) ([y |~> e2] d $ y)).
    apply_empty* (@typing_substitution A).
    simpl in H.
    rewrite* <- subst_intro_s in H.
    rewrite* <- subst_intro in H.

    lets : elab_unique TransB H.
    subst.
    apply* TyTApp.

  (* Pi *)
  - lets : typing_star_inv TransB.
    subst.
    apply_fresh* TyTPi as y.
    apply* H0.
    apply* trans_cons.


  (* And *)
  - lets : typing_star_inv TransB.
    subst.
    apply* TyTProd.

  (* cast down *)
  - lets [bb TT] : typing_wf_from_typing Ty1.
    lets : IHTy1 Ctx TT.
    eapply TyTCastDown; eauto.
    apply (reduction_consistency H TT TransB).

  (* cast up *)
  - lets [cc TT] : typing_wf_from_typing Ty1.
    lets : IHTy1 Ctx TT.
    eapply TyTCastUp; eauto.
    admit.

  (* Merge *)
  - lets : typing_and_inv TransB.
    destruct H as [c [d [? [TyA TyB]]]].
    subst.
    apply* TyTPair.

  (* Subsumption *)
  - lets [? ?]: typing_wf_from_typing Ty.
    apply* sub_prop.

Qed.
