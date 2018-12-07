Set Implicit Arguments.

Require Import LibLN definitions infrastructure.
Require Import List.

(**


Discuss
- counter example in pi
- counter example in castdn


 *)




Fixpoint substS (S : list (var * DExp)) (A : DExp) : DExp :=
  match S with
  | nil => A
  | (x, E) :: ES => substS ES ([x ~> E ]A)
  end.

Lemma list_ass : forall {A a} (D1 : list A) {D2}, (a :: D1) ++ D2 = a :: (D1 ++ D2).
  intros.
  rewrite (app_comm_cons D1 D2). auto.
Defined.

Lemma substS_pi : forall S A A', substS S (DPi A A') = DPi (substS S A) (substS S A').
  intros S.
  induction* S.
Qed.

Lemma substS_castup : forall S A, substS S (DCastup A) = DCastup (substS S A).
  intros S. induction* S.
Qed.

Lemma substS_dand : forall S A B, substS S (DAnd A B) = DAnd (substS S A) (substS S B).
  intros S. induction* S.
Qed.



Inductive Result : list DExp -> list (var * DExp) -> DExp -> DExp -> DExp -> DExp -> Prop :=
| RBNil : forall A B C A' S,
    (forall Gamma, has_type_source Gamma A (substS S B) -> has_type_source Gamma A' (substS S C)) ->
    Result nil S A B C A'
| RFVar : forall A x T D S, Result (T :: D) S A (DFVar x) (DFVar x) A
| RLam : forall L A A' B C T D S,
    (forall x, x \notin L -> Result D ((x, T) :: S) (DCastdn A) (open_source B (DFVar x)) (open_source C (DFVar x)) A') ->
    Result (T :: D) S A (DLam B) (DLam C) (DCastup A')
| RApp : forall A A' B C E D S T,
    Result (E :: T :: D) S A B C A' -> Result (T :: D) S A (DApp B E) (DApp C E) A'.


Fixpoint apps A D : DExp :=
  match D with
  | nil => A
  | T :: TS => apps (DApp A T) TS
  end.


Lemma apps_lemma : forall {D2 D1 S E A B E'},
    sub (D1 ++ D2) S E A B E' -> Result (D1 ++ D2) S E A B E' -> Result D2 S E (apps A D1) (apps B D1) E'.
  destruct D2; intros.
  -
    rewrite (app_nil_r D1) in H, H0.
    induction H0.
    (* Base case *)
    simpl. apply RBNil. auto.
    simpl. apply RBNil. auto.
    (* Lam case *)
    inversion H; subst; clear H.
    pick_fresh x.
    assert (x \notin L0) by auto.
    lets : H6 H; clear H6.
    assert (x \notin L) by auto.
    lets : H1 H3 H2; clear H1.
    inversion H4; subst. apply RBNil. intros.
    pose (@TyCastDown _ _ _ (substS ((x, T) :: S) (apps (open_source B (DFVar x)) D)) H5).
    assert (substS S (apps (DLam B) (T :: D)) ~~> substS ((x, T) :: S) (apps (open_source B (DFVar x)) D)). admit.
    assert ((substS S (apps (DLam C) (T :: D))) ~~> substS ((x, T) :: S) (apps (open_source C (DFVar x)) D)). admit.

    apply (H1 _) in h; auto.
    apply (@TyCastUp _ _ _ (substS ((x, T) :: S) (apps (open_source C (DFVar x)) D))); auto.


    pose (WF2 := typing_wf_from_typing h).
    (* cast require both star, might still need red_star *)
    pose (red_star_rev H7 WF2). auto.

    pose (WF1 := typing_wf_from_typing H5).
    (* cast require both star, might still need red_star *)
    pose (red_star H6 WF1). auto.

    (* app case *)
    inversion H; subst. apply IHResult in H8. simpl. simpl in H8. auto.
  -
    (* Inductive case *)
    generalize H H0. clear H H0. generalize S E A B E' d. clear d S E A B E'.
    induction D1; simpl; intros.
    auto.
    apply IHD1. apply SApp. auto.
    destruct D1. simpl in H0. simpl. apply RApp. auto.
    rewrite (list_ass D1). apply RApp.
    rewrite (list_ass D1) in H0. auto.
Qed.

Inductive Form : DExp -> Prop :=
| FBase : Form DStar
| FStep1 : forall A B, Form A -> Form (DAnd A B)
| FStep2 : forall A B, Form B -> Form (DAnd A B).

Lemma bad_form : forall B C, Form B -> B ~~> C -> False.
  intros.
  induction H. inversion H0.
  inversion H0. inversion H0.
Defined.

Require Import Program.Equality.

Lemma form_preserve: forall C, Form C -> forall B D S A A', sub D S A B C A' -> Form B.
  intros C fc.
  induction fc; intros.
  dependent induction H; subst.
  apply FBase. apply (@FStep1 _ _ IHsub). apply (@FStep2 _ _ IHsub).
  dependent induction H; subst.
  apply IHsub in fc. apply (@FStep1 _ _ fc). auto.
  apply IHsub in fc. apply (@FStep2 _ _ fc). auto.
  apply (@IHfc _ _ _  _ _ H).
  dependent induction H; subst.
  apply IHsub in fc. apply (@FStep1 _ _ fc). auto.
  apply IHsub in fc. apply (@FStep2 _ _ fc). auto.
  apply (@IHfc _ _ _  _ _ H0).
Defined.

Lemma castup_false : forall B, Form B -> forall A Gamma, has_type_source Gamma (DCastup A) B -> False.
  intros.
  dependent induction H0; subst.
  apply (bad_form H H0).
  apply IHhas_type_source. apply (@form_preserve C H _ _ _ _ _ H1).
  inversion H; subst. apply IHhas_type_source1. auto. apply IHhas_type_source2. auto.
  apply (IHhas_type_source (@FStep1 _ _ H)).
  apply (IHhas_type_source (@FStep2 _ _ H)).
Defined.

Lemma sub_gen : forall {A A' B C D S}, sub D S A B C A' -> Result D S A B C A'.
  intros.
  induction H using sub_ind'; intros.
  (* DBVar *)
  destruct S1.
  apply RBNil. intros. auto.
  apply RFVar.
  (* Star *)
  apply RBNil; intros. auto.
  (* Pi *)
  apply RBNil; intros.
  rewrite substS_pi in *.
  apply_fresh TyLam as x.
  (* star should hold *)
  admit.
  assert (x \notin L) by auto.
  lets [IH1 IH2] : H0 H2; clear H0.
  inverts IH1 as HH1.
  inverts IH2 as HH2.
  forwards TyE1 : HH1 (Gamma & x ~ (substS S A')).
  apply TyVar.
  (* WFS *)
  admit. auto.

  forwards TyE: typing_weaken x Gamma (substS S A') H1.
  (* WFS *)
  admit.
  assert (open_source (substS S B') (DFVar x) = substS S (open_source B' (DFVar x))). admit.
  rewrite H0.
  apply HH2.
  lets TyApp: TyApp TyE TyE1.
  assert (open_source (substS S B) (DFVar x) = substS S (open_source B (DFVar x))). admit.
  rewrite <- H3.
  (*


    typing relation of merge

    look at TyApp and the goal


    Here is an counter example:

    Assume the context E = y : Pi x : * & *. x


    x <| * <: * & * |> x,,x       y (x,,x) <| x <: x |> y (x,,x)
  ------------------------------------------------------------
    y <| Pi x : * & *. x <: Pi x : *. x |> \x. y (x,,x)


    But   G |- \x . y (x,,x) : Pi x : *. x,,x

    Not   Pi x : *. x


   *)
  admit.

  (* Lam *)
  apply_fresh RLam as x.
  assert (x \notin L) by auto.
  lets : H0 H1; auto.

  (* App *)
  assert (forall A, DApp A T = apps A (T :: nil)). intros. simpl. auto.
  rewrite (H0 A). rewrite (H0 B). clear H0.
  apply apps_lemma. rewrite (list_ass nil). simpl. auto.
  rewrite (list_ass nil). simpl. auto.

  (* CastDown *)
  inversion IHsub; subst. clear IHsub.
  apply RBNil. intros.
  lets H2 : typing_wf_from_typing H1.
  (* seems the conditions are useless *)




  (**



   y  <|  castup nat&* <: castup nat  |> y
---------------------------
    y : castdn castup nat&*   <:   castdn castup nat |> y



castup 1 <| nat <: nat & nat  |>  castup 1 ,, castup 1
---------------------------------------------------------
castup 1 <| castup nat  <:  castup (nat & nat)  |> castup 1 ,, castup 1
-------------------------------------------------------------------------
castup 1 <| castdn (castup nat) <: castdn (castup (nat & nat)) |> castup 1 ,, castup 1


But  |- castup 1 ,, castup 1 : castdn (castup (nat & nat)) is wrong



   *)

  admit.

  (* CastUp *)
  inversion IHsub; subst. clear IHsub.
  apply RBNil. intros.
  pose (H2 := typing_wf_from_typing H1).
  rewrite (substS_castup S A) in H2.
  destruct (@castup_false _ FBase _ _ H2).

  (* And *)
  inversion IHsub; subst. apply RBNil. intros.
  rewrite (substS_dand S A B) in H1.
  exact (H0 _ (@TyInter1 _ _ _ _ H1)).
  inversion IHsub; subst. clear IHsub. apply RBNil. intros.
  rewrite (substS_dand S A B) in H1.
  exact (@H0 _ (@TyInter2 _ _ _ _ H1)).
  inversion IHsub1. inversion IHsub2. subst. apply RBNil. intros.
  pose (H1 _ H3).
  pose (H2 _ H3).
  rewrite (substS_dand S B C).
  apply TyInter.
  apply TyMerge1; auto.
  apply TyMerge2; auto.
Qed.

(* has_type_source A (DApp B C) -> exists T, DApp B C ~~> T /\ has_type_source (castDown A) T *)

(* Lemma main : forall A B C A', sub nil nil A B C A' -> *)
(*                          forall Gamma, has_type_source Gamma B DStar B' -> *)
(*                                   has_type_source Gamma C DStar C' -> *)
(*                                   has_type_source2 Gamma A B' -> *)
(*                                   has_type_source2 Gamma A' C'. *)
(*   intros A B C A' H. pose (sub_gen H). inversion r; subst. simpl in H0. auto. *)
(* Defined. *)
