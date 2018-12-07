Set Implicit Arguments.
Require Import definitions infrastructure.
Require Import LibLN.
Require Import List.



(* ********************************************************************** *)
(* A bunch of things we don't know how to prove yet *)


(*

Discuss:

1. hasAnno, FIXME and FIXME2
2. subtyping_prop2, see FIXME (from shape)

TODO:
1. beta preserve type
2. reduction_consistency

 *)

Axiom elab_coherence : forall Γ E Mode e e' T,
    elab_typing_alg Γ E Mode T e -> elab_typing_alg Γ E Mode T e' -> e = e'.

Axiom sub_refl2 : forall S1 S2 A c, subM S1 S2 A A c.


Axiom reduction_preserve_kind : forall Γ A C a,
    A ~~> C ->
    elab_typing_alg Γ A Chk DStar a ->
    exists c, elab_typing_alg Γ C Chk DStar c.

(* ********************************************************************** *)


Lemma coercion_eq : forall c c0,
    (forall y, TCastup (c0 (TCastdn y)) = TCastup (c (TCastdn y))) ->
    coShape c ->
    coShape c0 ->
    c = c0.
Proof.
  intros.
  gen c0.
  induction H0; intros.
  - induction H1.
    auto.
    lets HH : H TStar.
    inversion HH.

    lets HH : H TStar.
    inversion HH.

    lets HH : H TStar.
    inversion HH.


    admit.

    admit.

    lets HH : H TStar.
    inversion HH.



Admitted.

Lemma reduction_consistency : forall A C m Γ a c B,
    A ~~> C ->
    elab_typing_alg Γ A m B a ->
    elab_typing_alg Γ C m B c ->
    a --> c.
Proof.
  introv Red. gen m Γ a c B.
  induction Red; intros.


Admitted.

Lemma beta_red_preserve_kind : forall Γ D E T a,
    elab_typing_alg Γ (DApp (DLam D) E) Inf T a ->
    exists c, elab_typing_alg Γ (D ^^ E) Inf T c.
Proof.
  intros.
  inverts H.
  inverts H2.

Admitted.

Lemma and_eliminate1 : forall Γ E A B e,
    elab_typing_alg Γ E Inf (DAnd A B) e ->
    elab_typing_alg Γ (DAnn E A) Inf A (TFst e).
Proof.
  intros.
  apply* ATyAnn.
  destructs (regular_typing H).
  inverts* H4.
  apply* ATySub.
  apply SL1M with (c := fun e => e); auto.
  admit.                            (* ordinary *)
  apply sub_refl2.
  admit.                            (* A is star *)

  Unshelve.
  exact e.
Admitted.

Lemma and_eliminate2 : forall Γ E A B e,
    elab_typing_alg Γ E Inf (DAnd A B) e ->
    elab_typing_alg Γ (DAnn E B) Inf B (TSnd e).
Proof.
  intros.
  apply* ATyAnn.
  destructs (regular_typing H).
  inverts* H4.
  apply* ATySub.
  apply SL2M with (c := fun e => e); auto.
  admit.                            (* ordinary *)
  apply sub_refl2.
  admit.                            (* B is star *)

  Unshelve.
  exact e.
Admitted.


(* Lack more condition *)
Lemma sub_S : forall S1 S2 A B c,
    subM S1 S2 A B c -> ok S2 /\ contains_terms S2 /\ all_terms S1.
Proof.
  introv Sub.
  induction Sub using subM_ind'; auto.

  admit.
  admit.
  pick_fresh x.
  forwards* [? [? ?]]: H0 x.
  rewrite  cons_to_push in *.
  splits.
  lets* : ok_push_inv H1.
  apply* contains_cons.
  unfold all_terms.
  intros.
  inverts* H4.

  splits*.
  inversion IHSub as [? [? ?]].
  apply* all_term_rest.


Admitted.


Lemma co_substi_commute : forall c y a e,
    coShape c ->
    [y |~> a] (c e) = c ([y |~> a] e).
Proof.
  introv Shape. gen y e. induction Shape; intros; simpls*.

  (* Pi *)
  - tests: (x = y).
    rewrite subst_fresh.
    assert (y \notin fv e). admit.
    rewrite* subst_fresh.
    apply close_var_fresh.

    assert (x \notin fv a). admit.
    rewrite* close_var_subst.
    rewrite* IHShape2.
    simpl.
    rewrite* IHShape1.
    simpl.
    case_var*.

  (* lam *)
  - rewrite* IHShape.

  (* L1 *)
  - rewrite* IHShape.
  (* L2 *)
  - rewrite* IHShape.
  (* L3 *)
  - rewrite IHShape1.
    rewrite* IHShape2.

Admitted.

(*

Counter example when ordinary

|- Int & Int : *

x : *, y : x & int |- y : x

y : (Int & Int) & int |- y : Int & Int


 *)

Lemma sub_subst : forall S1 S2 A c B C x,
    sterm A ->
    subM S1 S2 B C c ->
    subM (map (fun E => [x ~> A] E) S1) (map (fun Ep => (fst Ep, [x ~> A] (snd Ep))) S2) ([x ~> A] B) ([x ~> A] C) c.
Proof.
  introv Typ Sub. induction Sub using subM_ind'; try (apply sub_refl2); simpl; auto.

  (* Pi *)
  - apply_fresh SPiM as y.
    forwards* [? ?]: H y. subst. clear H.
    forwards* : H0 y.
    repeat rewrite* subst_open_var_s.
    exact IHSub.

  (* Lam *)
  - apply_fresh SLamM as y.
    cross*.
    simpl in H0. auto.

  (* SL1M *)
  - admit.

  (* SL2M *)
  - admit.
Admitted.

Lemma subM_substS : forall S1 S2 A B c,
    subM S1 S2 A B c -> subM S1 nil (substS S2 A) (substS S2 B) c.
Proof.
  introv Sub. induction Sub using subM_ind'.
  apply sub_refl2.
  apply sub_refl2.

  (* Pi *)
  - repeat rewrite substS_pi.
    apply_fresh* SPiM as x.
    forwards* [? ?] : H x.
    splits*.
    forwards* BsubB' : H0 x.
    lets [? ?]: sub_S Sub.
    repeat rewrite* substS_open.

  (* Lam *)
  - admit.

  (* App *)
  - repeat rewrite substS_app.
    apply SAppM. admit.

    admit.


  - repeat rewrite substS_anno.
    apply* SAnnoM.
    lets [? ?] : sub_S Sub.
    apply* sterm_substS.

  - repeat rewrite substS_and.
    apply* SL1M. admit.             (* ordinary *)
    lets [? ?] : sub_S Sub.
    apply* sterm_substS.
  - repeat rewrite substS_and.
    apply* SL2M. admit.
    lets [? ?] : sub_S Sub.
    apply* sterm_substS.
  - repeat rewrite substS_and.
    apply* SL3M.
Admitted.



Section SubEq.

Lemma DPi_subM_exists : forall L A B A' B' S c1 c2 x body,
    x \notin L \u fv_source B \u fv_source B' \u (fold_vars fv_source S) ->
    subM nil S (B ^ x) (B' ^ x) c2 ->
    body = (fun e : TExp => close_var x (c2 (TApp e (c1 (TFVar x))))) ->
    subM nil S A' A c1 ->
    subM nil S (DPi A B) (DPi A' B') (fun e : TExp => TLam (body e)).
Proof.
  introv Hnotin HsubMB Hbody HsubMA.
  apply_fresh* SPiM as y.
  split.

  rewrite subst_intro_s with (x := x); auto.
  rewrite subst_intro_s with (x := x) (t := B'); auto.
  asserts_rewrite (S = (map (fun Ep => (fst Ep, [x ~> DFVar y] (snd Ep))) S)).
  (* from x \notin fold_vars fv_source S *) admit.
  apply* (@sub_subst nil).

  rewrite Hbody.
  apply func_ext_dep.
  intros e.
  (* how? *)
  assert (x \notin fv e). admit.
  assert (y \notin fv e). admit.
  asserts_rewrite ((c2 (TApp e (c1 (TFVar y)))) = [x |~> TFVar y] (c2 (TApp e (c1 (TFVar x))))).
  rewrite* co_substi_commute.
  simpl.
  rewrite* co_substi_commute.
  simpl. case_var*.
  rewrite* subst_fresh.
  rewrite* close_var_rename.
  apply* coercion_fv.
  simple.
  rewrite notin_union.
  splits*.
  apply* coercion_fv.
  simpls*.
Admitted.

Lemma DLam_subM_exists : forall L A B S c T D x,
    x \notin L ->         
    subM D ((x, T) :: S) (A ^ x) (B ^ x) c ->
    subM (T :: D) S (DLam A) (DLam B) (fun e : TExp => TCastup (c (TCastdn e))).
Proof.
  introv Hnotin HsubMB.
  apply_fresh SLamM as x; eauto.
  lets HH : sub_shape HsubMB.
  (* eapply subM_renaming with (x := x); eauto. *)
  (* missing substitution in env *)
Admitted.
  
Lemma sub_sound : forall S1 S2 t1 t2, usubM S1 S2 t1 t2 -> exists c, subM S1 S2 t1 t2 c.
Proof.
  introv HusubM.
  induction HusubM; (try destruct IHHusubM); eauto.
  - pick_fresh y.
    forwards* [c HsubMB] : H0 y.
    eexists; apply* DPi_subM_exists.
  - pick_fresh y.
    forwards* [c HsubMB] : H0 y.
    eexists; apply* DLam_subM_exists.
  - admit. (* sand1 at disjointness.v *)
  - admit. (* sand2 at disjointness.v *)
  - destruct IHHusubM1, IHHusubM2. eauto.
Admitted.

Lemma sub_complete : forall S1 S2 t1 t2, (exists c, subM S1 S2 t1 t2 c) -> usubM S1 S2 t1 t2.
Proof.
  introv.
  intros [c HsubM].
  induction HsubM using subM_ind'; eauto.
Qed.

End SubEq.



Lemma sub_preserve : forall S1 S2 Γ c A B Mode,
    subM S1 S2 A B c ->
    (forall a, elab_typing_alg Γ (apps (substS S2 A) S1) Mode DStar a ->
    exists b, elab_typing_alg Γ (apps (substS S2 B) S1) Mode DStar b) /\
    (forall a, elab_typing_alg Γ (apps (substS S2 B) S1) Mode DStar a ->
    exists b, elab_typing_alg Γ (apps (substS S2 A) S1) Mode DStar b).
Proof.
  introv Sub. gen Γ Mode.
  lets :  sub_S Sub.
  induction Sub using subM_ind'; intros; split; intros.

  - exists* a.
  - exists* a.
  - exists* a.
  - exists* a.
  - simpl in *.
    rewrite substS_pi in *.
    lets [c [d [? [HA [L' HB]]]]]: elab_pi_inv H2. subst. clear H2.
    pick_fresh x.
    forwards* [HH HA']: IHSub Γ Chk. clear HH.
    forwards* [HB' HH]: H1 x (Γ & x ~ substS S A) Chk. clear HH.
    lets [a' HA'']: HA' HA.
    (* assert (contains_terms S). admit. (* should hold *) *)
    (* assert (ok S). admit. (* should hold *) *)
    forwards* : HB x.
    rewrite* substS_open in H2.
    lets [b' HB'']: HB' H2.
    exists (TPi a' b').
    destruct Mode.
    apply_fresh* ATyPi as y.
    admit.




Admitted.



Lemma sub_awfs : forall P Q E x c,
    subM nil nil P Q c ->
    awfs (E & x ~ Q) ->
    awfs (E & x ~ P).
Proof.
  introv PsubQ WF. gen_eq E': (E & x ~ Q).
  inductions WF; introv EQ.

  (* empty *)
  false (empty_push_inv EQ).

  (* nonempty *)
  destructs (eq_push_inv EQ). subst.
  lets [? HP] : sub_preserve PsubQ.
  simpls.
  apply HP in H0.
  inverts* H0.

Qed.


Inductive hasAnno : DExp -> DExp -> Prop :=
| anno_star : hasAnno DStar DStar
| anno_var : forall x, hasAnno (DFVar x) (DFVar x)
| anno_pi : forall L A B A' B',
    hasAnno A' A ->
    (forall x, x \notin L -> hasAnno (B' ^ x) (B ^ x)) ->
    hasAnno (DPi A' B') (DPi A B)
| anno_app : forall E1 E1' E2 E2',
    hasAnno E1' E1 ->
    hasAnno E2' E2 ->
    hasAnno (DApp E1' E2') (DApp E1 E2)
| anno_and : forall A A' B B',
    hasAnno A' A ->
    hasAnno B' B ->
    hasAnno (DAnd A' B') (DAnd A B)
| anno_merge : forall E1 E1' E2 E2',
    hasAnno E1' E1 ->
    hasAnno E2' E2 ->
    hasAnno (DMerge E1' E2') (DMerge E1 E2)
| anno_ann : forall A A' T,
      hasAnno A' A ->
      (* hasAnno T' T -> *)
      hasAnno (DAnn A' T) (DAnn A T)

| anno_lam : forall L t t' T,
    (forall x, x \notin L -> hasAnno (t' ^ x) (t ^ x)) ->
    hasAnno (DAnn (DLam t') T) (DLam t)
| anno_castdn : forall A A' T,
    hasAnno A' A ->
    hasAnno (DAnn (DCastdn A') T) (DCastdn A)
| anno_castup : forall A A' T,
    hasAnno A' A ->
    hasAnno (DAnn (DCastup A') T) (DCastup A)
| anno_sub : forall A A' T,
    hasAnno A' A ->
    hasAnno (DAnn A' T) A.

Hint Constructors hasAnno.



Lemma close_var_open_s : forall x t,
  sterm t -> t = (close_source x t) ^ x.
Proof.
Admitted.


Lemma check_to_infer : forall Γ A T e m,
    elab_typing_alg Γ A m T e ->
    exists A', hasAnno A' A /\ elab_typing_alg Γ A' Inf T e.
Proof.
  introv Typ.
  induction Typ; auto_star.

  (* Pi *)
  - pick_fresh x.
    destruct IHTyp as [A' [? ?]].
    forwards * [B' [? ?]]: H0 x.
    exists* (DPi A' (close_source x B')).
    split*.
    apply_fresh* anno_pi as y.
    asserts_rewrite (y = x). admit. (* LN with existential *)
    rewrite* <- close_var_open_s.

    apply_fresh* ATyPi as y.
    apply ATySub with (c := fun e => e) (B := DStar); auto.
    admit.                          (* FIXME: Look at H4 *)

  (* App *)
  - destruct IHTyp1 as [E1' [? ?]].
    destruct IHTyp2 as [E2' [? ?]].
    exists* (DApp E1' E2'); split*.
    (* FIXME2: E2 is not correct? *)
    admit.

  (* Ann *)
  - destruct IHTyp1 as [A' [? ?]].
    destruct IHTyp2 as [B' [? ?]].
    exists* (DAnd A' B'); split*.
    apply ATyAnd.
    apply ATySub with (c := fun e => e) (B := DStar); auto.
    apply ATySub with (c := fun e => e) (B := DStar); auto.
    admit.                          (* ortho *)

  (* Merge *)
  - destruct IHTyp1 as [E1' [? ?]].
    destruct IHTyp2 as [E2' [? ?]].
    exists* (DMerge E1' E2').

  (* Ann *)
  - destruct IHTyp1 as [A' [? ?]].
    exists* (DAnn A' T); split*.
    apply* ATyAnn.
    apply ATySub with (c := fun e => e) (B := T); auto.
    apply sub_refl2.

  (* Lam *)
  - pick_fresh x.
    destruct IHTyp as [A' [? ?]].
    forwards * [B' [? ?]] : H0 x.
    exists* (DAnn (DLam (close_source x B')) (DPi A B)).
    split.
    apply_fresh anno_lam as y.
    asserts_rewrite (y = x). admit. (* LN with existential *)
    rewrite* <- close_var_open_s.
    apply* ATyAnn.
    apply_fresh* ATyLam as y.
    asserts_rewrite (y = x). admit. (* LN with existential *)
    rewrite* <- close_var_open_s.
    apply ATySub with (c := fun e => e) (B := (B ^ x)); auto.
    apply sub_refl2.

  (* Castdn *)
  - destruct IHTyp1 as [A' [? ?]].
    exists* (DAnn (DCastdn A') C); split*.

  (* Castup *)
  - destruct IHTyp1 as [A' [? ?]].
    exists* (DAnn (DCastup A') C); split*.

  (* Sub *)
  - destruct IHTyp as [A' [? ?]].
    exists* (DAnn A' C); splits*.
    apply* ATyAnn.
    admit.                          (* easy *)

Admitted.






(* ********************************************************************** *)
(** Typing preserved by Subtyping in Environment *)

Lemma typing_narrowing : forall F x Q E P c e t T m,
  subM nil nil P Q c ->
  elab_typing_alg (E & x ~ Q & F) t m T e ->
  elab_typing_alg (E & x ~ P & F) t m T ([x |~> c (TFVar x)] e).
Proof.
  introv PsubQ Typ. gen_eq G: (E & x ~ Q & F). gen F.
  apply elab_induct with
  (P := fun (G:env DExp) B d T e (Typt : elab_typing_alg G B d T e) =>
          forall F, G = E & x ~ Q & F ->
               elab_typing_alg (E & x ~ P & F) B d T ([x |~> c (TFVar x)] e))
  (P0 := fun (G:env DExp) (W:awfs G) =>
          forall F, G = E & x ~ Q & F -> awfs (E & x ~ P & F)); intros; subst; simpls*.



  (* Var *)
  - case_var.
    forwards* : binds_middle_eq_inv b; subst.
    admit.
    lets : ok_middle_inv_r (ok_from_wf a).
    binds_cases b; apply* ATyVar.

  (* Pi *)
  - apply_fresh* ATyPi as y.
    rewrite* subst_open_var.
    apply_ih_bind* H0.
    apply* coercion_regular.

  (* Lam *)
  - apply_fresh* ATyLam as y.
    rewrite* subst_open_var.
    apply_ih_bind* H0.
    apply* coercion_regular.

  -  rewrite* co_substi_commute.


  (* empty *)
  - false (empty_middle_inv H).

  (* cons *)
  - induction F using env_ind.
    rewrite concat_empty_r in *.
    destruct (eq_push_inv H0) as [? [? ?]]. subst.
    apply* sub_awfs.

    rewrite concat_assoc in *.
    destruct (eq_push_inv H0) as [? [? ?]]. subst*.

Admitted.
