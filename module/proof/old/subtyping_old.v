Require Import definitions.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module SubTyping
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.


  Inductive sub2 : list SExp -> list SExp -> SExp -> SExp -> SExp -> SExp -> Prop :=
  | SubVar : forall E S1 S2 x, sub2 S1 S2 E (SBVar x) (SBVar x) E (* if S1 != empty, V else N *)
  | SubFVar : forall E S1 S2 x, sub2 S1 S2 E (SFVar x) (SFVar x) E (* if S1 != empty, V else N *)
  | SubStar : forall E S, sub2 nil S E SStar SStar E
  (* Not correct *)
  | SubPi : forall A B A' B' E E1 E2 S,
      sub2 nil S (SBVar 0) A' A E1 -> sub2 nil S (SApp E E1) B B' E2 -> sub2 nil S E (SPi A B) (SPi A' B') (SLam E2)
  | SubLam: forall E A B E' T D S, (* I believe we need this here: A T ~~> C /\ B T ~~> D *)
      sub2 D (T :: S) (SCastdn E) A (*C*) (*D*) B E' -> sub2 (T :: D) S E (SLam A) (SLam B) (SCastup E')
  | SubApp: forall T E A B E' D S,
      sub2 (T :: D) S E A B E' -> sub2 D S E (SApp A T) (SApp B T) E'
  | SubCastDown: forall E A B E' S,
      sub2 nil S E A B E' -> sub2 nil S E (SCastdn A) (SCastdn B) E'
  | SubCastUp: forall E A B E' S,
      sub2 nil S E A B E' -> sub2 nil S E (SCastup A) (SCastup B) E'
  | SubL1: forall E A C E' B S,
      sub2 nil S E A C E' -> sub2 nil S E (SAnd A B) C E'
  | SubL2: forall E A C E' B S,
      sub2 nil S E B C E' -> sub2 nil S E (SAnd A B) C E'
  | SubL3 : forall E A B C E1 E2 S,
      sub2 nil S E A B E1 -> sub2 nil S E A C E2 -> sub2 nil S E A (SAnd B C) (SMerge E1 E2).



  Hint Constructors sub2.

  Definition Sub2 (t1 t2 : SExp) : Prop := exists S1 S2 A B, sub2 S1 S2 A t1 t2 B.


  (* Coercive Subtyping *)

  (* hold for closed term or not? *)

  Inductive sub : SExp -> SExp -> TExp -> Prop :=
  | sub_star : sub SStar SStar (TLam (TBVar 0))
  | sub_fvar : forall x, sub (SFVar x) (SFVar x) (TLam (TBVar 0))
  | sub_bvar : forall n, sub (SBVar n) (SBVar n) (TLam (TBVar 0))
  | sub_pi : forall A' A c1 B B' c2,
      sub A' A c1 ->
      sub B B' c2 ->
      sub (SPi A B) (SPi A' B') (TLam (TLam (TApp c2 (TApp (TBVar 1) (TApp c1 (TBVar 0))))))
  | sub_lam : forall A B c, sub A B c -> sub (SLam A) (SLam B) (TLam (TCastup (TApp c (TCastdn (TBVar 0)))))
  | sub_app : forall A B E c, sub A B c -> sub (SApp A E) (SApp B E) c
  | sub_castdn : forall A B c, sub A B c -> sub (SCastdn A) (SCastdn B) c
  | sub_castup : forall A B c, sub A B c -> sub (SCastup A) (SCastup B) c
  | sub_and1 : forall A B C c, sub A C c -> sub (SAnd A B) C (TLam (TApp c (TFst (TBVar 0))))
  | sub_and2 : forall A B C c, sub B C c -> sub (SAnd A B) C (TLam (TApp c (TSnd (TBVar 0))))
  | sub_and3 : forall A B C c1 c2,
      sub A B c1 ->
      sub A C c2 ->
      sub A (SAnd B C) (TLam (TPair (TApp c1 (TBVar 0)) (TApp c2 (TBVar 0))))
  | sub_merge : forall A B, sub (SMerge A B) (SMerge A B) (TLam (TBVar 0)).
  (* | sub_anno : forall A B T c, sub A B c -> sub (SAnno A T) (SAnno B T) c. *)

  (* Hint Constructors sub. *)



  Definition Sub (t1 t2 : SExp) : Prop := exists (e : TExp), sub t1 t2 e.





  (* Smart constructors for Sub *)

  Definition sstar : Sub SStar SStar.
    unfold Sub. exists (TLam (TBVar 0)).
    apply sub_star.
  Defined.

  Definition sfvar : forall x, Sub (SFVar x) (SFVar x).
    unfold Sub; intros. exists (TLam (TBVar 0)).
    apply sub_fvar.
  Defined.

  Definition sbvar : forall x, Sub (SBVar x) (SBVar x).
    unfold Sub; intros. exists (TLam (TBVar 0)).
    apply sub_bvar.
  Defined.

  Definition spi : forall A' A B B',
      Sub A' A ->
      Sub B B' ->
      Sub (SPi A B) (SPi A' B').
    unfold Sub; intros.
    inversion H as [c1 H1]; clear H.
    inversion H0 as [c2 H2]; clear H0.
    exists (TLam (TLam (TApp c2 (TApp (TBVar 1) (TApp c1 (TBVar 0)))))).
    apply sub_pi; assumption.
  Defined.

  Definition slam : forall A B, Sub A B -> Sub (SLam A) (SLam B).
    unfold Sub; intros.
    inversion H as [c Hm]; clear H.
    exists (TLam (TCastup (TApp c (TCastdn (TBVar 0))))).
    apply sub_lam. assumption.
  Defined.

  Definition sapp : forall A B E, Sub A B -> Sub (SApp A E) (SApp B E).
    unfold Sub; intros.
    inversion H as [c Hm]; clear H.
    exists c. apply sub_app. assumption.
  Defined.

  Definition scastdn : forall A B, Sub A B -> Sub (SCastdn A) (SCastdn B).
    unfold Sub; intros.
    inversion H as [c Hm]; clear H.
    exists c. apply sub_castdn. assumption.
  Defined.

  Definition scastup : forall A B, Sub A B -> Sub (SCastup A) (SCastup B).
    unfold Sub; intros.
    inversion H as [c Hm]; clear H.
    exists c. apply sub_castup. assumption.
  Defined.

  Definition sand1 : forall A B C, Sub A C -> Sub (SAnd A B) C.
    unfold Sub; intros.
    inversion H as [c Hm]; clear H.
    exists (TLam (TApp c (TFst (TBVar 0)))).
    apply sub_and1. assumption.
  Defined.

  Definition sand2 : forall A B C, Sub B C -> Sub (SAnd A B) C.
    unfold Sub; intros.
    inversion H as [c Hm]; clear H.
    exists (TLam (TApp c (TSnd (TBVar 0)))).
    apply sub_and2. assumption.
  Defined.

  Definition sand3 : forall A B C, Sub A B -> Sub A C -> Sub A (SAnd B C).
    unfold Sub; intros.
    inversion H as [c1 H1]; clear H.
    inversion H0 as [c2 H2]; clear H0.
    exists (TLam (TPair (TApp c1 (TBVar 0)) (TApp c2 (TBVar 0)))).
    apply sub_and3; assumption.
  Defined.

  Definition smerge : forall A B, Sub (SMerge A B) (SMerge A B).
    unfold Sub; intros.
    exists (TLam (TBVar 0)).
    apply sub_merge.
  Defined.

  (* Definition sanno : forall A B T, Sub A B -> Sub (SAnno A T) (SAnno B T). *)
  (*   unfold Sub. *)
  (*   intros. *)
  (*   inversion H. *)
  (*   exists x. *)
  (*   apply sub_anno. *)
  (*   auto. *)
  (* Defined. *)

  Hint Resolve sstar sfvar sbvar spi slam sapp scastdn scastup sand1 sand2 sand3 smerge.


  Lemma sub_soundness : forall t1 t2, Sub2 t1 t2 -> Sub t1 t2.
  Proof.
    intros t1 t2 H.
    unfold Sub2 in H.
    inversion H as [? [? [? [? IHSub]]]]; clear H.
    induction IHSub; auto.
  Qed.

  Lemma sub_completeness : forall t1 t2, Sub t1 t2 -> Sub2 t1 t2.
  Proof.
    intros.
    unfold Sub in H.
    unfold Sub2.
    inversion H as [e IHSub].
    induction IHSub.
    exists nil.
    exists nil.
    exists SStar.
    exists SStar; auto.

    exists nil.
    exists nil.
    exists SStar.
    exists SStar; auto.


    exists nil.
    exists nil.
    exists SStar.
    exists SStar; auto.


    (* Inductive sub : list DExp -> list DExp -> DExp -> DExp -> DExp -> DExp -> Prop := *)
    (* | SVar : forall E S1 S2 x, sub S1 S2 E (DBVar x) (DBVar x) E (* if S1 != empty, V else N *) *)
    (* | SStar : forall E S, sub nil S E DStar DStar E *)
    (* (* Not correct *) *)
    (* | SPi : forall A B A' B' E E1 E2 S, *)
    (*     sub nil S (DBVar 0) A' A E1 -> sub nil S (DApp E E1) B B' E2 -> sub nil S E (DPi A B) (DPi A' B') (DLam E2) *)
    (* | SLam: forall E A B E' T D S, (* I believe we need this here: A T ~~> C /\ B T ~~> D *)  *)
    (*     sub D (T :: S) (DCastdn E) A (*C*) (*D*) B E' -> sub (T :: D) S E (DLam A) (DLam B) (DCastup E') *)
    (* | SApp: forall T E A B E' D S, *)
    (*     sub (T :: D) S E A B E' -> sub D S E (DApp A T) (DApp B T) E' *)
    (* | SCastDown: forall E A B E' S, *)
    (*     sub nil S E A B E' -> sub nil S E (DCastdn A) (DCastdn B) E' *)
    (* | SCastUp: forall E A B E' S, *)
    (*     sub nil S E A B E' -> sub nil S E (DCastup A) (DCastup B) E' *)
    (* | SL1: forall E A C E' B S, *)
    (*     sub nil S E A C E' -> sub nil S E (DAnd A B) C E' *)
    (* | SL2: forall E A C E' B S, *)
    (*     sub nil S E B C E' -> sub nil S E (DAnd A B) C E' *)
    (* | SL3 : forall E A B C E1 E2 S, *)
    (*     sub nil S E A B E1 -> sub nil S E A C E2 -> sub nil S E A (DAnd B C) (DMerge E1 E2). *)


    (* how to get S1 S2 A B out of nowhere *)
    (* compute some of the fields *)
    Lemma sub_completeness : forall t1 t2, Sub t1 t2 -> forall A, exists S1 S2 B, sub2 S1 S2 A t1 t2 B.
    Proof.
      intros t1 t2 H.
      unfold Sub in H.
      inversion H as [e IHSub]; clear H.
      induction IHSub; intros.

      (* Star *)
      exists nil.
      exists nil.
      exists A; auto.


      (* SFVar *)
      exists nil.
      exists nil.
      exists A; auto.

      (* SBVar *)
      exists nil.
      exists nil.
      exists A; auto.


      (* SPi *)
      admit.


      (* SLam *)
      pose (E := IHIHSub (SCastdn A0)).
      admit.


      (* SApp *)
      admit.


    (*


  | SubPi : forall A B A' B' E E1 E2 S,
      sub2 nil S (SBVar 0) A' A E1 -> sub2 nil S (SApp E E1) B B' E2 -> sub2 nil S E (SPi A B) (SPi A' B') (SLam E2)
  | SubLam: forall E A B E' T D S, (* I believe we need this here: A T ~~> C /\ B T ~~> D *)
      sub2 D (T :: S) (SCastdn E) A (*C*) (*D*) B E' -> sub2 (T :: D) S E (SLam A) (SLam B) (SCastup E')
  | SubApp: forall T E A B E' D S,
      sub2 (T :: D) S E A B E' -> sub2 D S E (SApp A T) (SApp B T) E'
  | SubCastDown: forall E A B E' S,
      sub2 nil S E A B E' -> sub2 nil S E (SCastdn A) (SCastdn B) E'
  | SubCastUp: forall E A B E' S,
      sub2 nil S E A B E' -> sub2 nil S E (SCastup A) (SCastup B) E'
  | SubL1: forall E A C E' B S,
      sub2 nil S E A C E' -> sub2 nil S E (SAnd A B) C E'
  | SubL2: forall E A C E' B S,
      sub2 nil S E B C E' -> sub2 nil S E (SAnd A B) C E'
  | SubL3 : forall E A B C E1 E2 S,
      sub2 nil S E A B E1 -> sub2 nil S E A C E2 -> sub2 nil S E A (SAnd B C) (SMerge E1 E2).



     *)


    Admitted.

    (* Reflexivity *)

    Lemma reflex : forall (t : SExp), Sub t t.
    Proof.
      intros t; induction t; auto.
    Qed.

    (* Transivity *)

    Lemma invAnd : forall t t1 t2, Sub t (SAnd t1 t2) -> Sub t t1 /\ Sub t t2.
    Proof.
      intro t.
      induction t; intros.
      (* SStar *)
      - inversion H.
        inversion H0; subst.
        split.
        unfold Sub.
        exists c1; auto.
        unfold Sub.
        exists c2; auto.
      (* SBVar *)
      - inversion H.
        inversion H0; subst.
        split.
        unfold Sub.
        exists c1; auto.
        unfold Sub.
        exists c2; auto.
      (* SFVar *)
      - inversion H.
        inversion H0; subst.
        split.
        unfold Sub.
        exists c1; auto.
        unfold Sub.
        exists c2; auto.
      (* SLam *)
      - inversion H.
        inversion H0; subst.
        split.
        exists c1; auto.
        exists c2; auto.
      (* SApp *)
      - inversion H.
        inversion H0; subst.
        split.
        exists c1; auto.
        exists c2; auto.
      (* SCastdn *)
      - inversion H.
        inversion H0; subst.
        split.
        exists c1; auto.
        exists c2; auto.
      (* SCastup *)
      - inversion H.
        inversion H0; subst.
        split.
        exists c1; auto.
        exists c2; auto.
      (* SPi *)
      - inversion H.
        inversion H0; subst.
        split.
        exists c1; auto.
        exists c2; auto.
      (* SAnd *)
      - inversion H.
        inversion H0; subst.
        assert (Sub t1 t0 /\ Sub t1 t3).
        apply IHt1.
        exists c; auto.
        split.
        apply sand1.
        inversion H1; auto.
        apply sand1.
        inversion H1; auto.
        assert (Sub t2 t0 /\ Sub t2 t3).
        apply IHt2.
        exists c; auto.
        split.
        inversion H1.
        apply sand2; auto.
        inversion H1.
        apply sand2; auto.
        split.
        exists c1; auto.
        exists c2; auto.
      (* SMerge *)
      - inversion H.
        inversion H0; subst.
        split.
        exists c1; auto.
        exists c2; auto.
        (* SAnno *)
        (* - inversion H. *)
        (*   inversion H0; subst. *)
        (*   split. *)
        (*   exists c1. auto. *)
        (*   exists c2. auto. *)
    Qed.

    Lemma trans : forall t2 t1 t3, Sub t1 t2 -> Sub t2 t3 -> Sub t1 t3.
    Proof.
      intros t2.
      induction t2; intros.
      (* Case SStar *)
      - induction t3; try (inversion H0; inversion H1); auto; subst.
        apply sand3.
        apply IHt3_1.
        exists c1; auto.
        apply IHt3_2.
        exists c2; auto.
      (* Case SBVar *)
      - induction t3; try (inversion H0; inversion H1); auto; subst.
        auto.
        apply sand3.
        apply IHt3_1.
        exists c1; auto.
        apply IHt3_2.
        exists c2; auto.
      (* Case SFVar *)
      - induction t3; try (inversion H0; inversion H1); auto; subst.
        auto.
        apply sand3.
        apply IHt3_1.
        exists c1; auto.
        apply IHt3_2.
        exists c2; auto.
      (* Case SLam *)
      - induction t1; try (inversion H; inversion H1); auto; subst.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply slam.
        apply IHt2.
        exists c; auto.
        exists c0; auto.
        apply sand3.
        apply IHt3_1.
        exists c1; auto.
        intros.
        apply IHt1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply IHt3_2.
        exists c2; auto.
        intros.
        apply IHt1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply sand1.
        apply IHt1_1.
        exists c; auto.
        apply sand2.
        apply IHt1_2.
        exists c; auto.
      (* SApp *)
      - induction t1; try (inversion H; inversion H1); auto; subst.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply sapp.
        apply IHt2_1.
        exists x; auto.
        exists x0; auto.
        apply sand3.
        apply IHt3_1.
        exists c1; auto.
        intros.
        apply IHt1_1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        intros.
        apply IHt1_2 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply IHt3_2.
        exists c2; auto.
        intros.
        apply IHt1_1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        intros.
        apply IHt1_2 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply sand1.
        apply IHt1_1.
        exists c; auto.
        apply sand1.
        apply IHt1_1.
        exists c; auto.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply sand2.
        apply IHt1_2.
        exists c; auto.
        apply sand2.
        apply IHt1_2.
        exists c; auto.
      (* SCastdn *)
      - induction t1; try (inversion H; inversion H1); auto; subst.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply scastdn.
        apply IHt2.
        exists x; auto.
        exists x0; auto.
        apply sand3.
        apply IHt3_1.
        exists c1; auto.
        intros.
        apply IHt1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply IHt3_2.
        exists c2; auto.
        intros.
        apply IHt1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply sand1.
        apply IHt1_1.
        exists c; auto.
        apply sand2.
        apply IHt1_2.
        exists c; auto.
      (* SCastup *)
      - induction t1; try (inversion H; inversion H1); auto; subst.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply scastup.
        apply IHt2.
        exists x; auto.
        exists x0; auto.
        apply sand3.
        apply IHt3_1.
        exists c1; auto.
        intros.
        apply IHt1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply IHt3_2.
        exists c2; auto.
        intros.
        apply IHt1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply sand1.
        apply IHt1_1.
        exists c; auto.
        apply sand2.
        apply IHt1_2.
        exists c; auto.
      (* SPi *)
      - induction t1; try (inversion H; inversion H1); auto; subst.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply spi.
        apply IHt2_1.
        exists c0; auto.
        exists c1; auto.
        apply IHt2_2.
        exists c2; auto.
        exists c3; auto.
        apply sand3.
        apply IHt3_1.
        exists c0; auto.
        intros.
        apply IHt1_1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        intros.
        apply IHt1_2 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        apply IHt3_2.
        exists c3; auto.
        intros.
        apply IHt1_1 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        intros.
        apply IHt1_2 in H3.
        apply invAnd in H3.
        inversion H3; auto.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply sand1.
        apply IHt1_1.
        exists c; auto.
        apply sand1.
        apply IHt1_1.
        exists c; auto.
        induction t3; try (inversion H0; inversion H2); auto; subst.
        apply sand2.
        apply IHt1_2.
        exists c; auto.
        apply sand2.
        apply IHt1_2.
        exists c; auto.
      (* SAnd *)
      - assert (Sub t1 t2_1 /\ Sub t1 t2_2).
        apply invAnd; auto.
        destruct H1.
        induction t3.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        apply IHt2_1; auto.
        exists c; auto.
        apply IHt2_2; auto.
        exists c; auto.
        inversion H0.
        inversion H3; subst.
        assert (Sub t2_1 (SAnd t3_1 t3_2)).
        exists c; auto.
        apply invAnd in H4.
        inversion H4.
        apply sand3.
        apply IHt2_1; auto.
        apply IHt2_1; auto.
        assert (Sub t2_2 (SAnd t3_1 t3_2)).
        exists c; auto.
        apply invAnd in H4.
        inversion H4.
        apply sand3.
        apply IHt2_2; auto.
        apply IHt2_2; auto.

        assert (Sub (SAnd t2_1 t2_2) t3_1).
        exists c1; auto.
        apply IHt3_1 in H4.

        assert (Sub (SAnd t2_1 t2_2) t3_2).
        exists c2; auto.
        apply IHt3_2 in H5.
        apply sand3; auto.

        inversion H0.
        inversion H3; subst.

        assert (Sub t2_1 (SMerge t3_1 t3_2)).
        exists c; auto.
        apply IHt2_1; auto.
        assert (Sub t2_2 (SMerge t3_1 t3_2)).
        exists c; auto.
        apply IHt2_2; auto.

      (* inversion H3; subst. *)
      (* inversion H0. *)
      (* apply IHt2_1. auto. *)
      (* exists c. auto. *)
      (* apply IHt2_2. auto. *)
      (* exists c. auto. *)

      (* SMerge *)

      - induction t1; try (inversion H; inversion H1); auto; subst.
        destruct t3; try (inversion H0; inversion H2); auto; subst.
        assert (Sub t1_1 (SMerge t2_1 t2_2)).
        exists c; auto.
        apply IHt1_1 in H3.
        apply sand1; auto.
        apply sand1.
        exists c; auto.

        destruct t3; try (inversion H0; inversion H2); auto; subst.
        assert (Sub t1_2 (SMerge t2_1 t2_2)).
        exists c; auto.
        apply IHt1_2 in H3.
        apply sand2; auto.
        apply sand2.
        exists c; auto.

        (* SAnno *)
        (* - induction t1; try (inversion H; inversion H1); auto; subst. *)
        (*   inversion H. *)
        (*   assert (Sub t1_1 (SAnno t2_1 t2_2)). *)
        (*   exists c. *)
        (*   assumption. *)
        (*   apply IHt1_1 in H3. *)
        (*   apply sand1. *)
        (*   assumption. *)

        (*   assert (Sub t1_2 (SAnno t2_1 t2_2)). *)
        (*   exists c. *)
        (*   assumption. *)
        (*   apply IHt1_2 in H2. *)
        (*   apply sand2. *)
        (*   assumption. *)
        (*   induction t3; try (inversion H0; inversion H2); subst; auto. *)
        (*   assert (Sub (SAnno t1_1 t2_2) t3_1). *)
        (*   apply IHt3_1. *)
        (*   exists c1. *)
        (*   assumption. *)
        (*   intros. *)
        (*   apply IHt1_1 in H3. *)
        (*   apply invAnd in H3. *)
        (*   inversion H3. *)
        (*   assumption. *)
        (*   intros. *)
        (*   apply IHt1_2 in H3. *)
        (*   apply invAnd in H3. *)
        (*   inversion H3. *)
        (*   assumption. *)

        (*   assert (Sub (SAnno t1_1 t2_2) t3_2). *)
        (*   apply IHt3_2. *)
        (*   exists c2. *)
        (*   assumption. *)
        (*   intros. *)
        (*   apply IHt1_1 in H4. *)
        (*   apply invAnd in H4. *)
        (*   inversion H4. *)
        (*   assumption. *)
        (*   intros. *)
        (*   apply IHt1_2 in H4. *)
        (*   apply invAnd in H4. *)
        (*   inversion H4. *)
        (*   assumption. *)

        (*   apply sand3; assumption. *)

        (*   apply sanno. *)
        (*   apply IHt2_1. *)
        (*   exists x. *)
        (*   assumption. *)
        (*   exists x0. *)
        (*   assumption. *)
    Qed.

End SubTyping.