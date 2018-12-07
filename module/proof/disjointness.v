Set Implicit Arguments.
Require Import definitions infrastructure elab_prop_alg.
Require Import LibLN.
Require Import List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.


Definition Sub (S1 : list DExp) (S2 : list (var * DExp)) (t1 t2 : DExp) :
  Prop :=
  exists c, subM S1 S2 t1 t2 c. 

Hint Unfold Sub.

Ltac ord_inv :=
  match goal with
    | [ H : ordinary ?t |- _ ] => inversion H
  end.

(* Smart constructors for Sub *)

Definition sand3 : forall t t1 t2 S2, Sub nil S2 t t1 -> Sub nil S2 t t2 ->
                                 Sub nil S2 t (DAnd t1 t2).
  introv H1 H2; destruct H1; destruct H2; eauto.
Defined.

Definition sand1_atomic :
  forall t t1 t2 S2, Sub nil S2 t1 t -> ordinary t -> sterm t2 ->
                Sub nil S2 (DAnd t1 t2) t.
  unfold Sub; introv HSub HOrd.
  destruct_conjs; eauto.
Defined.

Definition sand2_atomic :
  forall t t1 t2 S2, Sub nil S2 t2 t -> ordinary t -> sterm t1 ->
                Sub nil S2 (DAnd t1 t2) t.
  unfold Sub; introv HSub HOrd.
  destruct_conjs; eauto.
Defined.

Hint Resolve sand3 sand1_atomic sand2_atomic.

Definition sand1 : forall t t1 t2 S2, Sub nil S2 t1 t -> Sub nil S2 (DAnd t1 t2) t.
  intro t.
  induction t; intros; eauto; try (now inversion H; inversion H0; subst; ord_inv).
  destruct H; inversion H; subst; try ord_inv; eauto 10.
Defined.


Definition sand2 : forall t t1 t2 S2, Sub nil S2 t1 t -> Sub nil S2 (DAnd t1 t2) t.
  intro t.
  induction t; intros; eauto; try (now inversion H; inversion H0; subst; ord_inv).
  destruct H; inversion H; subst; try ord_inv; eauto 10.
Defined.

Hint Resolve sand1 sand2.

Ltac orthoax_inv H :=
  let H' := fresh in
  let m := fresh in
  let H1 := fresh in
  let H2 := fresh in
  inversion H as [H' | m H1 H2 ]; orthoax_inv H1.
 
(* Solving goals by inversion, with the form OrthoAx t1 t2,
   where t1 is not part of OrthoAx *)
Ltac orthoax_inv_l :=
  match goal with
    | H: orthoax _ _ |- _ => let H1 := fresh in
                          destruct H as [H1 _]; orthoax_inv H1
  end.
 
(* Solving goals by inversion, with the form OrthoAx t1 t2,
   where t2 is not part of OrthoAx *)
Ltac orthoax_inv_r :=
   match goal with
    | H: orthoax _ _ |- _ => let H1 := fresh in
                            destruct H as [_ [H1 _]]; orthoax_inv H1
   end.

Ltac orthoax_inv_neq :=
   match goal with
    | H: orthoax _ _ |- _ => let H1 := fresh in
                            destruct H as [_ [_ H1]]; exfalso; now apply H1
   end.


(* Unique subtype contributor *)

Lemma uniquesub : forall A B C S1 S2,
  ortho A B -> Sub S1 S2 (DAnd A B) C -> not (Sub S1 S2 A C /\ Sub S1 S2 B C).
Proof.
  intros.
  unfold not; intros.
  destruct H1.
  gen C S1 S2.
  dependent induction H; intros.
  (* OAnd1 *)
  - induction C; try (now inversion H2; inversion H4; subst; eauto).
    + inversion H2; inversion H4; subst; try ord_inv.
      inversion H3; inversion H5; subst; try ord_inv.
      apply IHC1; eauto.
  (* OAnd2 *)
  - induction C; try (now inversion H3; inversion H4; subst; eauto).
    + inversion H2; inversion H4; subst; try ord_inv.
      inversion H3; inversion H5; subst; try ord_inv.
      apply IHC1; eauto.
  (* OLam *)
  - induction C; try (now inversion H3; inversion H4; subst).
    + inversion H1; inversion H4; subst.
      inversion H2; inversion H5; subst.
      inversion H2; inversion H5; subst.
    + inversion H2; inversion H4; subst.
      inversion H3; inversion H5; subst.
      apply IHC1; eauto.
  (* OPi *)
  - induction C; try (now inversion H3; inversion H4; subst).
    + inversion H2; inversion H4; subst.
      inversion H3; inversion H5; subst.
      pick_fresh x.
      forwards* [HH1 HH2] : H12 x.
      forwards* [HH3 HH4] : H11 x.
      eapply H0 with (x := x); eauto.
    + inversion H2; inversion H4; subst.
      inversion H3; inversion H5; subst.
      apply IHC1; eauto.
  (* OApp *)
  - induction C; try (now inversion H2; inversion H3).
    + inversion H1; inversion H3; subst.
      inversion H2; inversion H4; subst.
      inversion H0; inversion H5; subst.
      eapply IHortho; eauto. admit. (* subM DAnd requires nil. Maybe we should change this? *)
      eapply IHortho; eauto. admit. (* same as above *)
    + inversion H1; inversion H3; subst.
      inversion H2; inversion H4; subst.
      apply IHC1; eauto.
  (* OAx - TODO consider switching to an inductive def. for OAx *)
  - induction C.
    + inversion H1; inversion H3; inversion H2; inversion H7; subst;
      [ orthoax_inv_neq H | orthoax_inv_r H | orthoax_inv_r H |
        orthoax_inv_l H | orthoax_inv_l H ].
    + inversion H1; inversion H3; inversion H2; inversion H7; subst; orthoax_inv_l H.
    + inversion H1; inversion H3; inversion H2; inversion H7; subst; orthoax_inv_l H.
    + inversion H1; inversion H3; inversion H2; inversion H10; subst;
      [ orthoax_inv_neq H | orthoax_inv_r H | orthoax_inv_r H |
        orthoax_inv_l H | orthoax_inv_l H ].
    + inversion H1; inversion H3; inversion H2; inversion H11; subst;
      [ orthoax_inv_neq H | orthoax_inv_r H | orthoax_inv_r H | | | | | | ];
      orthoax_inv_l H.
    + inversion H1; inversion H3; inversion H2; inversion H11; subst; orthoax_inv_l H.
    + inversion H1; inversion H3; inversion H2; inversion H11; subst; orthoax_inv_l H.
    + inversion H1; inversion H3.
      inversion H2; inversion H12; subst. orthoax_inv_neq H. orthoax_inv_r H.
      orthoax_inv_r H.
      inversion H2; inversion H11; subst. orthoax_inv_l H. orthoax_inv_l H.
      orthoax_inv_r H.
      subst; orthoax_inv_l H.
    + inversion H1; inversion H2; inversion H3; inversion H4; subst; try ord_inv.
      apply IHC1; eauto.
    + inversion H1; inversion H3; inversion H2; inversion H7; subst; orthoax_inv_l H.
    + inversion H1; inversion H3; inversion H2; inversion H7; subst; orthoax_inv_l H.
Admitted.

Print elab_typing_alg.

Eval cbv in (env DExp).

Inductive kind : sctx -> DExp -> Prop :=
  | KStar : forall Gamma, kind Gamma DStar
  | KVar : forall Gamma x, x \in (dom Gamma) ->
                  kind Gamma (DFVar x)
  | KPi: forall L Gamma T A, (forall x, x \notin L -> kind (Gamma & x ~ DStar) (T ^ x)) ->
                    kind Gamma (DPi A T).

Hint Constructors kind.

Fixpoint collapse (S : list DExp) (T : DExp) : DExp :=
  match S with
    | nil => T
    | cons arg args => collapse args (DApp T arg)
  end.

Definition collapse_fold (S : list DExp) (T : DExp) : DExp :=
  fold_left (fun r arg => DApp r arg) S T.

Definition exp := ((DCastdn DStar) :: ((DCastup DStar) :: nil)).

Eval cbv in collapse exp DStar.
Eval cbv in collapse_fold exp DStar.

Hint Unfold collapse.

Lemma kind_app : forall T, kind empty T -> exists (S : list DExp) c,
                                     elab_typing_alg empty (collapse S T) Inf DStar c.
Proof.
  introv KindT.
  dependent induction KindT.
  - exists (@nil DExp); eauto.
  - rewrite dom_empty in H; exfalso; apply* in_empty_elim.
  - pick_fresh x.
    forwards* [HH1 [HH2 HH3]] : H0 x.
    admit.
    eexists (cons DStar HH1). eexists. simpl.
    (* apply_fresh ATyPi as y. *)
Admitted.
  
Lemma sub_kind :
  forall E A T1 c m1, elab_typing_alg E A m1 T1 c -> kind E T1 ->
  forall S1 S2 B, Sub S1 S2 A B ->
  forall T2 m2, elab_typing_alg E B m2 T2 c -> kind E T2.
Proof.
  introv HTyp.
  induction HTyp; intros.
  - inversion H1; inversion H3; subst.
    inversion H2; subst; eauto.
    inversion H6; subst; eauto.
    inversion H11; subst; eauto.
    inversion H4.
    inversion H2; subst.
    inversion H8; subst.
    inversion H13; subst; inversion H6.
  - inversion H2; inversion H4; subst.
    inversion H3; subst.
    admit. (* by H0 and H8 *)
    inversion H7; subst.
    admit. (* similar to case above? *)
    
    
Admitted.                      

Lemma sub_coherent :
  forall S1 S2 A B,
  forall {e1}, subM S1 S2 A B e1 ->
          forall E F c1 c2 M1 M2, elab_typing_alg E A M1 DStar c1 ->
                             elab_typing_alg F B M2 DStar c2 ->
                             forall {e2}, subM S1 S2 A B e2 -> e1 = e2.
Proof.
  introv Hsub.
  induction Hsub using subM_ind'; introv HWFA HWFB; intros.
  - now inversion H.
  - now inversion H.
  - inversion H1; inversion HWFA; inversion HWFB; subst;
    [ | inversion H18 | inversion H11 | inversion H11; inversion H19 ]; subst;
    pick_fresh x;
    forwards* [HH1 HH2] : H x;
    forwards* [HH3 HH4] : H7 x;
    rewrite HH2, HH4;
    erewrite IHHsub with (e2 := c4); eauto;
    erewrite H0 with (e2 := c5); eauto.
  - inversion H1; inversion HWFA; inversion HWFB; subst.
    inversion H18.
  - inversion H; inversion HWFA; inversion HWFB; subst.
    admit.
  - inversion H0; subst; try now ord_inv.
    + inversion HWFA; subst. 
      forwards* HH : IHHsub H4 HWFB H5; now subst.
      inversion H2; subst.
      forwards* HH : IHHsub H8 HWFB H5; now subst.
    + inversion HWFA; subst.
      assert (HSub : Sub nil S (DAnd A B) C) by eauto.
      lets* HH : uniquesub H9 HSub.
      exfalso; apply* HH.
      inversion H2; subst.
      inversion H2; subst.
      assert (HSub : Sub nil S (DAnd A B) C) by eauto.
      lets* HH : uniquesub H16 HSub.
      exfalso; apply* HH.
  - inversion H0; subst; try now ord_inv.
    + inversion HWFA; subst.
      assert (HSub : Sub nil S (DAnd A B) C) by eauto.
      lets* HH : uniquesub H9 HSub.
      exfalso; apply* HH.
      inversion H2; subst.
      inversion H2; subst.
      assert (HSub : Sub nil S (DAnd A B) C) by eauto.
      lets* HH : uniquesub H16 HSub.
      exfalso; apply* HH.
    + inversion HWFA; subst. 
      forwards* HH : IHHsub H7 HWFB H5; now subst.
      inversion H2; subst.
      forwards* HH : IHHsub H10 HWFB H5; now subst.
  - inversion H; subst; try ord_inv.
    dependent induction HWFB.
    erewrite IHHsub1 with (e2 := c4); eauto.
    erewrite IHHsub2 with (e2 := c5); eauto.
    inversion H0; subst.
    apply IHHWFB; auto.
    inversion HWFB.
    inversion HWFB.  
Admitted.

Lemma elab_coherence' :
  forall Gamma E Mode e e' T, elab_typing_alg Gamma E Mode T e ->
                     elab_typing_alg Gamma E Mode T e' ->
                     e = e'.
Proof.
  introv HTyp.
  generalize dependent e'.
  induction HTyp; intros; eauto.
  - now inversion H0.
  - now inversion H1.
  - inversion H1; subst. 
    erewrite* IHHTyp.
    pick_fresh x.
    assert (Ha1 : t2 $ x = t3 $ x) by forwards*: H0 x.
    lets* Ha2 : open_var_inj Ha1.
    now subst.
  - inversion H; subst.
    lets HH : typ_unique HTyp1 H4; inversion HH; subst.
    rewrite IHHTyp2 with (e' := e3); auto.
    rewrite IHHTyp1 with (e' := e0); auto.
  - inversion H0; subst.
    erewrite IHHTyp1, IHHTyp2; try reflexivity; auto.
  - inversion H0; subst.
    erewrite IHHTyp1, IHHTyp2; try reflexivity; auto.
  - inversion H; subst.
    erewrite IHHTyp1.
    reflexivity. auto.
  - inversion H1; subst.
    pick_fresh x.
    assert (Ha1 : t1 $ x = t2 $ x) by (forwards*: H x).
    lets* Ha2 : open_var_inj Ha1.
    now subst.
    inversion H3.
  - inverts H0.
    asserts_rewrite* (a = a0).
    apply* IHHTyp1.
    lets HH : typ_unique HTyp1 H2.
    inverts* HH.
    inverts H2.
  - inverts H0.
    asserts_rewrite* (a = a0).
    apply* IHHTyp1.
    lets HH : typ_unique HTyp1 H2.
    inverts* HH.
    inverts H2.
  - inversion H1; subst.
    inversion HTyp.
    inversion HTyp.
    inversion HTyp.
    lets HH : typ_unique HTyp H3.
    inversion HH; subst; clear HH.
    apply typing_wf_from_typing in H1 as [HH1 HH2].
    apply typing_wf_from_typing in HTyp as [HH3 HH4].
    lets* HH: sub_coherent H4 HH4 HH2 H0.
    rewrite HH.
    erewrite* IHHTyp.
Qed.
