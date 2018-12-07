
Set Implicit Arguments.

Require Import definitions infrastructure axioms.
Require Import LibLN.
Require Import List.


Hint Constructors has_type wft.

Lemma typ_weaken : forall G E F e T,
    has_type (E & G) e T ->
    wft (E & F & G) ->
    has_type (E & F & G) e T.
Proof.
Admitted.



Lemma substS_pi : forall S A B,
    substS S (DPi A B) = DPi (substS S A) (substS S B).
Proof.
  intros S.
  induction S; intros; auto.
  destruct a.
  simpl.
  apply IHS.
Qed.


Lemma substS_lam : forall S A,
    substS S (DLam A) = DLam (substS S A).
Proof.
  intros S.
  induction S; intros; auto.
  destruct a.
  simpl.
  apply IHS.
Qed.

Lemma substS_app : forall S A B,
    substS S (DApp A B) = DApp (substS S A) (substS S B).
Proof.
  intros S.
  induction S; intros; auto.
  destruct a.
  simpl.
  apply IHS.
Qed.

Lemma substS_and : forall S A B,
    substS S (DAnd A B) = DAnd (substS S A) (substS S B).
Proof.
  intros S.
  induction S; intros; auto.
  destruct a.
  simpl.
  apply IHS.
Qed.


Lemma notin_cons : forall (A:Type) (ys:env A) x y t,
    x # (ys & y ~ t) -> x # ys /\ x <> y.
Proof.
  intros.
  simpl_dom.
  apply notin_union_r in H.
  split*.
  inverts* H.
Qed.


Lemma contains_cons : forall E x t,
    ok (E & x ~ t) ->
    contains_terms (E & x ~ t) ->
    contains_terms E.
Proof.
  intros.
  unfold contains_terms in *.
  intros.
  case_if_eq x0 x.
  destruct (ok_push_inv H).
  apply get_some_inv in H1.
  false* H3.
  apply* H0.
Qed.

Lemma substS_open : forall S A y,
    y # S ->
    ok S ->
    contains_terms S ->
    substS S A ^ y = substS S (A ^ y).
Proof. 
  intros S.
  induction S; intros; auto.
  destruct a.
  simpl.
  rewrite cons_to_push in *.
  apply notin_cons in H.
  rewrite* <- subst_open_var_s.
  apply* IHS.
  apply* contains_cons.
Qed.


Inductive Result : list DExp -> list (var * DExp) -> TExp -> DExp -> DExp -> TExp -> Prop :=
| RBNil : forall e e' A B S,
    (forall Gamma Gamma' a b,
        trans_ctx_alg Gamma Gamma' ->
        elab_typing_alg Gamma (substS S A) Chk DStar a ->
        elab_typing_alg Gamma (substS S B) Chk DStar b ->
        has_type Gamma' e a ->
        has_type Gamma' e' b) ->
    Result nil S e A B e'
| RFVar : forall x e T D S,
    Result (T :: D) S e (DFVar x) (DFVar x) e
| RLam : forall L e e' B C T D S,
    (forall x, x \notin L -> Result D ((x, T) :: S) (TCastdn e) (B ^ x) (C ^ x) e') ->
    Result (T :: D) S e (DLam B) (DLam C) (TCastup e')
| RApp : forall e e' B C D (S : list (var * DExp)) (E T : DExp),
    Result (E :: T :: D) S e B C e' -> Result (T :: D) S e (DApp B E) (DApp C E) e'.


Lemma list_ass : forall {A a} (D1 : list A) {D2}, (a :: D1) ++ D2 = a :: (D1 ++ D2).
  intros.
  rewrite (app_comm_cons D1 D2). auto.
Defined.


Lemma apps_lemma : forall {D2 D1 S E A B E'},
    sub (D1 ++ D2) S E A B E' -> Result (D1 ++ D2) S E A B E' -> Result D2 S E (apps A D1) (apps B D1) E'.
Proof.
  destruct D2; intros.
  rewrite (app_nil_r D1) in H, H0.
  induction H0.
  (* Base case *)
  simpl. apply RBNil. auto.
  (* Var *)
  simpl. apply RBNil. intros.
  lets : (elab_coherence H1 H2). subst. auto.
  (* Lam case *)
  inverts H.
  pick_fresh x.
  assert (x \notin L0) by auto.
  lets : H6 H; clear H6.
  assert (x \notin L) by auto.
  lets : H1 H3 H2; clear H1.
  inverts H4.
  apply RBNil; intros.
  assert (substS S (apps (DLam B) (T :: D)) ~~> substS ((x, T) :: S) (apps (B ^ x) D)). admit. (* should be derived from beta-reduction *)
  assert (exists c, elab_typing_alg Gamma (substS ((x, T) :: S) (apps (B ^ x) D)) Chk DStar c). admit. (* I think this can be derived from the substitution lemma *)
  assert (substS S (apps (DLam C) (T :: D)) ~~> substS ((x, T) :: S) (apps (C ^ x) D)). admit. (* should be derived from beta-reduction *)
  assert (exists c, elab_typing_alg Gamma (substS ((x, T) :: S) (apps (C ^ x) D)) Chk DStar c). admit. (* I think this can be derived from the substitution lemma *)
  destruct H9. destruct H11.
  (*assert (elab_typing Gamma (substS ((x, T) :: S) (apps (B ^ x) D)) DStar a).*)
  pose (@TyTCastDown _ _ x0 _ H7).
  apply TyTCastUp with (t2 := x1).
  assert (a --> x0). apply (reduction_consistency H8 H5 H9).
  apply (H1 _ _ _ _ H4 H9 H11 (h H12)).
  apply (reduction_consistency H10 H6 H11).
  (* app case *)
  inversion H; subst. apply IHResult in H8. simpl. simpl in H8. auto.
  (* Inductive case *)
  generalize H H0. clear H H0. generalize S E A B E' d. clear d S E A B E'.
  induction D1; simpl; intros.
  auto.
  apply IHD1. apply SApp. auto.
  destruct D1. simpl in H0. simpl. apply RApp. auto.
  rewrite (list_ass D1). apply RApp.
  rewrite (list_ass D1) in H0. auto.
Qed.


(* This lemma is not true at the moment, but we can make it true *)
(*
Lemma gen_refl : forall A e S2, (exists S1, sub S1 S2 e A A e).
  induction A; intros.
  exists (@nil DExp). apply SStar. admit. (* impossible *)
  exists (@nil DExp). apply SVar.
  destruct (IHA e S2). exists x.
  apply SLam.
  admit. (* impossible *)
  apply SApp.
Admitted.
*)  


Require Import Program.Equality.

Lemma trivial_subst : forall e x, [x |~> TFVar x] e = e.
induction e; simpl; intros; try (rewrite IHe; auto). 
auto. auto.
admit.
rewrite IHe1. auto.
rewrite IHe2. auto.
rewrite IHe1. auto.
rewrite IHe2. auto.
rewrite IHe1. auto.
rewrite IHe2. auto.
rewrite IHe1. auto.
rewrite IHe2. auto.
Defined.

(*
Lemma sub_weaken : forall x A A' e1 S1, sub S1 nil (TFVar x) A' A e1 -> forall F E B T e Mode,
    elab_typing_alg (E & x ~ A & F) B Mode T e ->
    elab_typing_alg (E & x ~ A' & F) B Mode T ([x |~> e1] e).
  intros x A A' e1 S1 S2 s. dependent induction s; intros.
*)

(* find some interesting names for these 2 lemmas *)

Lemma t : forall T D S e A B e', sub (T :: D) S e A B e' -> forall Gamma T r, elab_typing_alg Gamma (substS S B) Inf T r -> e = e' /\ A = B.
  intros T D S e A B e' s. dependent induction s; intros. auto.
  rewrite substS_lam in *.
  inversion H1; subst. 
  rewrite substS_app in *.
  inversion H; subst.
  split.
  apply* IHs.
  assert (A = B) by (apply* IHs). subst. auto.
Defined.

Lemma t1 : forall T D S e A B e', sub (T :: D) S e A B e' -> forall Gamma T r, elab_typing_alg Gamma (substS S A) Inf T r -> e = e' /\ A = B.
  intros T D S e A B e' s. dependent induction s; intros. auto.
  rewrite substS_lam in *.
  inversion H1; subst. 
  rewrite substS_app in *.
  inversion H; subst.
  split.
  apply* IHs.
  assert (A = B) by (apply* IHs). subst. auto.
Defined.

(* Lemma sub_refl : forall {A S1 S2 a}, sub S1 S2 a A A a -> forall {b}, sub S1 S2 b A A b. *)
(*   induction A; intros; try (inversion H; subst). *)
(*   auto. auto. admit. (*impossible *) *)
(*   apply SApp. apply* IHA1. *)
(*   admit. (*impossible *) *)
(*   admit. (*impossible: not (A1 <: A1 & A2) with disjointness *) *)
(*   admit. (*impossible: not (A1 <: A1 & A2) with disjointness *) *)
(*   admit. (*impossible: *) *)
(* Admitted. *)

Lemma trivial_impossible : forall A0 B, A0 = DAnd A0 B -> False.
  induction A0; intros; try (inversion H).
  apply (IHA0_1 A0_2). auto.
Defined.

Lemma eq_types : forall {S1 S2 a A B}, sub S1 S2 a A B a -> A = B.
  intros. dependent induction H using sub_ind'. auto. auto.
  pick_fresh x. assert (x \notin L) by auto.
  destruct (H x H1). destruct (H0 x H1).
  (* impossible H3 *)
  admit.
  pick_fresh x. assert (x \notin L) by auto. pose (H x H1).
  admit.
  (* impossible *)
  rewrite IHsub. auto.
  admit.
  (* impossible *)
  admit. (* impossible *)
  admit. (* impossible *)
Admitted.

(*
Lemma fund_sub_dand1_gen : forall A m T a Gamma, elab_typing_alg Gamma A m T a -> forall { C e B}, sub nil nil a T C (TFst e) -> elab_typing_alg Gamma (DAnd A B) m C e.
  intros T A m e Gamma elab. induction elab; intros.
  inversion H0. admit.
  admit. admit. admit. admit. admit. admit. admit.
  assert (sub nil nil a B C0 (TFst e)) by admit. (* transitivity *)
  pose (IHelab C0 e B0 H3). apply* ATySub. admit. (* reflexivity *)
Admitted.

Lemma fund_sub_dand1 : forall {T A m e Gamma}, elab_typing_alg Gamma A m T (TFst e) -> forall {B}, elab_typing_alg Gamma (DAnd A B) m T e.
  intros. apply* fund_sub_dand1_gen. admit. (* reflexivity *)
Admitted.
*)
  
(* Lemma fund_sub_dand1 : forall {T A m e Gamma}, elab_typing_alg Gamma A m T (TFst e) -> forall {B}, elab_typing_alg Gamma (DAnd A B) m T e. *)
(*   intros T A m e Gamma elab. dependent induction elab; intros. *)
(*   pose (IHelab1 B). inversion e0; subst. *)
(*   inversion H1; subst. inversion H2; subst. *)
(*   apply ATyAnd.  *)
(*   apply* ATySub. admit. (* should be provable if we have conversions? *) auto.  *)
(*   admit. (* not possible when we have disjoint subtyping: Star only a subtype of Star *) *)
(*   inversion H1; subst. *)
(*   pose (IHelab e eq_refl B0). apply* ATySub. *)
(*   pose (IHelab e eq_refl B0). apply* ATySub. *)
(*   inversion H2; subst. *)
(*   pose (IHelab e eq_refl B0). apply* ATySub. *)
(*   assert (exists b, elab_typing_alg SE (DApp (DApp A1 T0) T) Chk DStar b) by admit. *)
(*   destruct H4. *)
(*   inversion H4; subst. inversion H7; subst. *)
(*   destruct (t1 H2 H12). subst. *)
(*   pose (IHelab e eq_refl B0). injection H10. intros; subst. *)
(*   apply* ATySub. apply SApp. apply SApp. auto. *)
(*   apply (sub_refl H3). *)
(*   clear IHelab. *)
(*   (* Tough case *)  *)
(*   admit. admit. *)
(* Admitted. *)

Lemma fund_sub_dand2 : forall {T B m e Gamma}, elab_typing_alg Gamma B m T (TSnd e) -> forall {A}, elab_typing_alg Gamma (DAnd A B) m T e.
  intros T A m e Gamma elab. dependent induction elab; intros.
  pose (IHelab1 A). inversion e0; subst.
  inversion H1; subst. inversion H2; subst.
Admitted.

(* Lam 0 <| Pi x : * . x <: Pi x : * . x |> *)

Lemma gen_sub : forall {S1 S2 a A B b}, sub S1 S2 a A B b ->
                                         forall Gamma e, elab_typing_alg Gamma e Chk (substS S2 A) a -> elab_typing_alg Gamma e Chk (substS S2 B) b.
  intros S1 S2 a A B b sub.
  induction sub using sub_ind'; intros.
  (* Var and Star *)
  auto. auto. 
  (* Pi case *)
  rewrite substS_pi in *.
  inversion H1; subst. 
  Admitted.

(* Lemma not_and : forall {T D S e A B e'}, sub (T :: D) S e A B e' -> forall {Gamma m T e}, *)
(*                  elab_typing_alg Gamma (substS S B) m T e -> not (exists C D, A = DAnd C D). *)
(*   intros T D S e A B e' s. dependent induction s; intros; unfold not; intros. *)
(*   destruct H0. destruct H0. *)
(*   discriminate H0. *)
(*   destruct H2. destruct H2. discriminate H2. *)
(*   destruct H0. destruct H0. discriminate H0. *)
(* Defined. *)

(* 
- sub nil nil a (DAnd A0 B1) C (TFst e)
- elab_typing_alg SE A Inf (DAnd A0 B1) a 
 *)


(* substitution preserves target terms: not true at the moment *)

Lemma sub_substS : forall S1 S2 a A B b,
    sub S1 S2 a A B b -> sub S1 nil a (substS S2 A) (substS S2 B) b.
Proof.
  introv Sub. induction Sub using sub_ind'.
  apply sub_refl.
  apply sub_refl.

  (* Pi *)
  repeat rewrite substS_pi.
  apply_fresh SPi as x.
  assert (x \notin L) by auto.
  destruct (H0 x H1).
  split.
  exact H2.
  assert (ok S). admit.         (* should hold *)
  assert (contains_terms S). admit. (* should hold *)
  repeat rewrite* substS_open.

  (* Lam *)
  repeat rewrite substS_lam.
  apply_fresh SLam as x.
  assert (x \notin L) by auto.
  lets: (H0 x H1). (* pose (H0 x H1). *)
  admit.

  (* app *)
  (* need to move from one stack to another *)
  repeat rewrite substS_app.
  apply SApp. auto. admit. (* issue: may need to generalize the lemma *)

  repeat rewrite substS_and.
  apply* SL1. admit.
  repeat rewrite substS_and.
  apply* SL2. admit.
  repeat rewrite substS_and.
  apply* SL3.
Admitted.

(* Lemma fund_sub : forall {S1 S2 a A B b}, sub S1 S2 a A B b -> *)
(*                                        forall Gamma m T, elab_typing_alg Gamma (substS S2 B) m T b -> elab_typing_alg Gamma (substS S2 A) m T a. *)
(*   intros S1 S2 a A B b sub. *)
(*   induction sub using sub_ind'; intros. *)
(*   (* Var and Star *) *)
(*   auto. auto. *)
(*   (* Pi case *) *)
(*   rewrite substS_pi in *. *)
(*   inversion H1; subst. inversion H4; subst. inversion H5. *)
(*   (* Lam case *) *)
(*   rewrite substS_lam in *. *)
(*   inversion H1; subst. *)
(*   inversion H4. *)
(*   (* App case *) *)
(*   rewrite substS_app in *. *)
(*   inversion H; subst. assert (e = TApp e1 e2 /\ A = B) by (apply (t sub H3)). *)
(*   destruct H0. subst. auto. *)
(*   inversion H2; subst. *)
(*   assert (e = e' /\ A = B) by (apply (t sub H7)). destruct H4; subst. auto. *)
(*   (* And case *) *)
(*   apply (IHsub _) in H. *)
(*   rewrite substS_and in *. (* T has to be star? *) *)
(*   apply (fund_sub_dand1 H). *)
(*   apply (IHsub _) in H. *)
(*   rewrite substS_and in *. *)
(*   apply (fund_sub_dand2 H). *)
(*   rewrite substS_and in *. *)
(*   inversion H; subst. *)
(*   inversion H2; subst. *)
(*   assert (T = DStar). admit. subst. (* by disjointness *) *)
(*   inversion H3. *)
(* Admitted. *)

(* Lemma fund_sub2 : forall {S1 S2 a A B b}, sub S1 S2 a A B b -> *)
(*                                           forall Gamma m T, elab_typing_alg Gamma (substS S2 A) m T a -> elab_typing_alg Gamma (substS S2 B) m T b. *)
(*   intros S1 S2 a A B b sub. *)
(*   induction sub using sub_ind'; intros. *)
(*   (* Var and Star *) *)
(*   - auto. *)
(*   - auto. *)
(*   (* Pi *) *)
(*   - rewrite substS_pi in *. *)
(*     admit. *)
(*   (* Lam *) *)
(*   - rewrite substS_lam in *. *)
(*     inversion H1; subst. *)
(*     admit. *)
(*     inversion H1; subst. *)
(*     inversion H4; subst. *)
(*     admit. *)
(*   (* App *) *)
(*   - rewrite substS_app in *. *)
(*     inversion H; subst. assert (TApp e1 e2 = e' /\ A = B) by (apply (t1 sub H3)). *)
(*     destruct H0. subst. auto. *)
(*     inversion H2; subst. *)
(*     assert (e = e' /\ A = B) by (apply (t1 sub H7)). destruct H4; subst. auto. *)
(*   - *)
    
    
(* Lemma fund_sub : forall {S1 S2 a A B b}, sub S1 S2 a A B b -> *)
(*                                        forall Gamma, elab_typing_alg Gamma (substS S2 B) Chk DStar b <-> elab_typing_alg Gamma (substS S2 A) Chk DStar a. *)
(*   intros S1 S2 a A B b sub. *)
(*   induction sub using sub_ind'; intros; split; intros. *)
(*   (* Var and Star *) *)
(*   auto. auto. auto. auto. *)
(*   (* Pi case *) *)
(*   rewrite substS_pi in *. *)
(*   inversion H1; subst. inversion H4; subst. inversion H5. *)
(*   rewrite substS_pi in *. *)
(*   admit. *)
(*   (* Lam case *) *)
(*   rewrite substS_lam in *. *)
(*   inversion H1; subst. *)
(*   inversion H4. *)
(*   rewrite substS_lam in *. *)
(*   inversion H1; subst. *)
(*   inversion H4; subst. *)
(*   (* App case *) *)
(*   rewrite substS_app in *. *)
(*   inversion sub; subst. *)
(*   auto. *)
(*   inversion H; subst. inversion H2; subst. (* generated coercions seem wrong: is theorem right *) *)
(*   admit. *)
(*   admit. *)
(*   admit. *)
(*   (* And case *) *)
(*   apply (IHsub _) in H. *)
(*   rewrite substS_and in *. *)
(*   apply (fund_sub_dand1 H). *)
(*   admit. *)
(*   apply (IHsub _) in H. *)
(*   rewrite substS_and in *. *)
(*   apply (fund_sub_dand2 H). *)
(*   admit. *)
(*   rewrite substS_and in *. *)
(*   inversion H; subst. *)
(*   inversion H2; subst. *)
(*   inversion H3. *)
(*   destruct (IHsub1 Gamma). *)
(*   destruct (IHsub2 Gamma). *)
(*   pose (H1 H). pose (H3 H). *)
(*   admit. *)
(* Admitted. *)

(* Lemma fund_sub_cor : forall S1 S2 x A B b, sub S1 S2 (TFVar x) A B b -> *)
(*                                            forall Gamma, elab_typing_alg Gamma (substS S2 B) Chk DStar b -> elab_typing_alg Gamma (substS S2 A) Chk DStar (TFVar x). *)
(*   intros. *)
(*   destruct (fund_sub H Gamma). *)
(*   apply H1. auto. *)
(* Defined. *)

(* Lemma fund_sub_cor2 : forall S1 S2 x A B b, sub S1 S2 (TFVar x) A B b -> *)
(*                                            forall Gamma, elab_typing_alg Gamma A Chk DStar (TFVar x)-> elab_typing_alg Gamma B Chk DStar b. *)
(* Admitted. *)

(* (* Todo: Needs to be different for inference and Chk modes *) *)
(* Lemma sub_weaken : forall B x A A' e1 S1 S2 Mode e T E F, elab_typing_alg (E & x ~ substS S2 A & F) B Mode T e -> *)
(*     sub S1 S2 (TFVar x) A' A e1 -> *)
(*     elab_typing_alg (E & x ~ substS S2 A' & F) B Mode T ([x |~> e1] e). *)
(*   induction B; intros. *)
(*   inversion H; subst. simpl. apply ATyStar. admit. *)
(*   admit. *)
(*   inversion H; subst. admit. (* impossible *) *)
(*   inversion H; subst. simpl. admit. (* important case *) *)
(*   admit. *)
(*   inversion H; subst; simpl. *)
(*   (* inversion H; subst; simpl. *) *)
(*   (* intros x A A' e1 S1 S2 s. dependent induction s; intros. *) *)
(*   (* rewrite trivial_subst. auto.  *) *)
(*   (* rewrite trivial_subst. auto.  *) *)
(*   (* admit. (* induction is broken for Pi case? *) *) *)
(*   (* clear H0. *) *)
(* Admitted. *)

(*
Lemma fund_sub : forall S1 S2 a A B b, sub S1 S2 a A B b ->
                 forall Gamma m T, elab_typing_alg Gamma B m T b <-> elab_typing_alg Gamma A m T a.
  intros S1 S2 a A B b sub.
  induction sub; intros; split; intros.
  (* Var and Star *)
  auto. auto. auto. auto.
  (* Pi case *)
  (* I.H. is missing ? *)
  inversion H0; subst. inversion H3; subst. inversion H4.
  admit.
  (* Lam case *)
  inversion H1; subst.
  inversion H4.
  inversion H1; subst.
  inversion H3; subst. inversion H6; subst. inversion H7; subst.
  pick_fresh x. assert (x \notin L) by auto. assert (x \notin L1) by auto.
  pose (H x H8). pose (H12 x H9).
  pose (H0 x H8). admit.
  (* apply (@ATySub _ _ (A ^ x) _ (TCastdn (TLam t1))). admit. admit. *)
  apply* ATySub. admit. 
  (* App case *)
  inversion H; subst.
  inversion sub; subst. (* I think I need an inductive lemma here *)
  auto.
  admit.
  admit.
  (* And case *)
  induction H. admit. (* impossible *)
  admit. (* impossible *)
  Admitted.
*)


Lemma sub_gen : forall {e e' B C D S}, sub D S e B C e' -> Result D S e B C e'.
Proof.
  intros.
  induction H using sub_ind'.

  (* Var *)
  destruct S1.
  apply RBNil.
  intros.
  lets : elab_coherence H1 H2. subst~.
  apply RFVar.

  (* Star *)
  apply RBNil. intros.
  lets : elab_coherence H1 H2. subst~.

  (* Pi TODO *)
  apply RBNil. intros.
  rewrite substS_pi in *.
  (* experiment *)
  (*inversion H3; subst.*)
  destruct (elab_pi_inv H3) as [c [d [? [TyA' [L0 TyB']]]]]. subst. clear H3.
  destruct (elab_pi_inv H2) as [g [h [? [TyA [L1 TyB]]]]]. subst. clear H2.
  apply_fresh TyTLam as y.
  assert (Lset: y \notin L) by auto.
  assert (L0set :y \notin L0) by auto.
  assert (L1set:y \notin L1) by auto.
  destruct (H y Lset) as [SubA SubB]. clear H.
  destruct (H0 y Lset) as [HH1 HH2]. clear H0.
  assert (TyTB' : elab_typing_alg (Gamma & y ~ substS S A') (substS S B' ^ y) Chk DStar (d $ y)) by (apply (TyB' y L0set)). clear TyB'.
  assert (TyTB : elab_typing_alg (Gamma & y ~ substS S A) (substS S B ^ y) Chk DStar (h $ y)) by (apply (TyB y L1set)). clear TyB.
  clear Lset L0set L1set.
  inverts HH1. inverts HH2.

  (* Some thoughts go here *)
  assert (F : elab_typing_alg (Gamma & y ~ substS S A') ((substS S B ^ y)) Chk DStar ([y |~> (e1 $ y)] (h $ y))).
  apply_empty * typing_narrowing. apply* sub_substS.


  assert (contains_terms S). admit. (* should hold *)
  assert (ok S). admit. (* should hold *)
  apply (H0 (Gamma & y ~ substS S A') _  ([y |~> (e1 $ y)] (h $ y)) _).
  apply Atrans_cons; auto. rewrite~ <- substS_open. rewrite~ <- substS_open.
  rewrite* <- subst_intro.
  apply TyTApp with (a := g).
  apply_empty* typ_weaken. admit. (* well-formedness of context *)
  assert (elab_typing_alg (Gamma & y ~ substS S A') (substS S A') Chk DStar c).
  apply_empty* typing_weaken.
  assert (elab_typing_alg (Gamma & y ~ substS S A') (substS S A) Chk DStar g).
  apply_empty* typing_weaken.
  assert (has_type (Gamma' & y ~ c) (TFVar y) c).
  apply* TyTVar. admit. (* well-formedness of context*)
  apply* H.

  (* Lam *)
  apply_fresh RLam as x.
  apply~ H0.

  (* App *)
  assert (forall A, DApp A T = apps A (T :: nil)). intros. auto.
  rewrite (H0 A). rewrite (H0 B). clear H0.
  apply apps_lemma. rewrite (list_ass nil). simpl. auto.
  rewrite (list_ass nil). simpl. auto.

  (* Merge1 *)
  inverts IHsub.
  apply RBNil. intros.
  rewrite substS_and in H3.
  destruct (elab_and_inv H3) as [c [d [? [TyA TyB]]]]. subst.
  apply* H1.

  (* Merge2 *)
  inverts IHsub.
  apply RBNil. intros.
  rewrite substS_and in H3.
  destruct (elab_and_inv H3) as [c [d [? [TyA TyB]]]]. subst.
  apply* H1.

  (* Merge3 *)
  inverts IHsub1.
  inverts IHsub2.
  apply RBNil. intros.
  rewrite substS_and in H5.
  destruct (elab_and_inv H5) as [c [d [? [TyA TyB]]]]. subst.
  apply* TyTPair.
Admitted.

Lemma sub_prop : forall Gamma Gamma' A B e e' a b,
    sub nil nil e A B e' ->
    elab_typing_alg Gamma A Chk DStar a ->
    elab_typing_alg Gamma B Chk DStar b ->
    trans_ctx_alg Gamma Gamma' ->
    has_type Gamma' e a ->
    has_type Gamma' e' b.
Proof.
  intros.
  pose (Res := sub_gen H).
  inverts Res.
  apply* H4.
Defined.

(* Old experiments

Lemma fund_sub : forall S1 S2 a A B b, sub S1 S2 a A B b ->
                                       forall Gamma, elab_typing_alg Gamma B Chk DStar b <-> elab_typing_alg Gamma A Chk DStar a.
  intros S1 S2 a A B b sub.
  induction sub using sub_ind'; intros; split; intros.
  (* Var and Star *)
  auto. auto. auto. auto.
  (* Pi case *)
  (* I.H. is missing ? *)
  inversion H0; subst. inversion H3; subst. inversion H4.
  admit.
  (* Lam case *)
  inversion H1; subst.
  inversion H4.
  inversion H1; subst.
  inversion H4; subst.
  (* App case *)
  inversion sub; subst.
  auto.
  inversion H; subst. inversion H2; subst. (* generated coercions seem wrong: is theorem right *)
  admit.  
  admit.
  admit.
  (* And case *)
  apply (IHsub _) in H. apply (fund_sub_dand1 H).
  admit.
  apply (IHsub _) in H. apply (fund_sub_dand2 H).
  admit.
  inversion H; subst.
  inversion H2; subst.
  inversion H3.
  destruct (IHsub1 Gamma).
  destruct (IHsub2 Gamma).
  pose (H1 H). pose (H3 H).
  admit.
Admitted.

Lemma fund_sub : forall S1 S2 a A B b, sub S1 S2 a A B b ->
                                       forall Gamma m T, elab_typing_alg Gamma B m T b <-> elab_typing_alg Gamma A m T a.
  intros S1 S2 a A B b sub.
  induction sub; intros; split; intros.
  (* Var and Star *)
  auto. auto. auto. auto.
  (* Pi case *)
  (* I.H. is missing ? *)
  inversion H0; subst. inversion H3; subst. inversion H4.
  admit.
  (* Lam case *)
  inversion H1; subst.
  inversion H4.
  inversion H1; subst.
  admit. (* what's this case ? *)
  inversion H4; subst.
  (* App case *)
  inversion sub; subst.
  auto.
  inversion H; subst. inversion H2; subst. (* generated coercions seem wrong: is theorem right *)
  admit.  
  admit.
  admit.
  (* And case *)
  apply (IHsub _ _ _) in H. apply (fund_sub_dand1 H).
  admit.
  apply (IHsub _ _ _) in H. apply (fund_sub_dand2 H).
  admit.
  inversion H; subst.
  inversion H2; subst.
  assert (T = DStar). admit. (* in disjoint subtyping T must be DStar *)
  subst. inversion H3.
  destruct (IHsub1 Gamma m T).
  destruct (IHsub2 Gamma m T).
  pose (H1 H). pose (H3 H).
  destruct m.
  assert (T = DStar). admit. subst. (* T must be DStar. Why? *)
  apply* ATyAnd.
  

Lemma fund_sub : forall S1 S2 a A B b, sub S1 S2 a A B b ->
                 forall Gamma m T, elab_typing_alg Gamma B m T b -> elab_typing_alg Gamma A m T a.
  intros S1 S2 a A B b sub.
  induction sub; intros.
  (* Var and Star *)
  auto. auto.
  (* Pi case *)
  (* I.H. is missing ? *)
  inversion H0; subst. inversion H3; subst. inversion H4.
  (* Lam case *)
  inversion H1; subst.
  inversion H4.
  (* App case *)
  dependent induction sub; subst.
  auto.
  inversion H1; subst. 
  admit.  
  admit.
  (* And case *)
  apply (IHsub _ _ _) in H. apply (fund_sub_dand1 H). 
  apply (IHsub _ _ _) in H. apply (fund_sub_dand2 H). 
  inversion H; subst.
  inversion H2; subst.
  assert (T = DStar). admit. (* in disjoint subtyping T must be DStar *)
  subst. inversion H3.

Admitted.

*)
