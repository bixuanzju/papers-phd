Require Import definitions.
Require Import subtyping.
Require Import typing.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.


Module Uniqueness
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.

  Module N := SubTyping VarTyp set.
  Export N.

  Module S := Typing VarTyp set.
  Export S.


  Definition almost_unique (A B : SExp) (d : Dir) : Prop :=
    match d with
      | Inf => A = B
      | Chk => True (* Is this result useful for checking: exists C, Sub C A /\ Sub C B*)
    end.

  Lemma in_dom :
    forall (G: context SExp) x T, ok G -> List.In (x, T) G -> In x (dom G).
  Proof.
    intros.
    induction G.
    inversion H0.
    destruct a.
    inversion H; subst.
    unfold dom.
    simpl.
    fold (dom (A:=SExp)).
    apply add_spec.
    intuition.
    inversion H0; subst.
    inversion H2; subst.
    left.
    reflexivity.
    right.
    auto.
  Qed.

  Lemma ok_unique_type :
    forall (Gamma: context SExp) x A B,
      ok Gamma -> List.In (x, A) Gamma /\ List.In (x, B) Gamma -> A = B.
  Proof.
    intros.
    induction H.
    inversion H0.
    inversion H.
    inversion H0.
    unfold extend in H2.
    simpl in H2.
    unfold extend in H3.
    simpl in H3.
    intuition.
    - inversion H0; subst.
      inversion H2; subst.
      auto.
    - inversion H0; subst.
      assert (In x (dom E)).
      apply in_dom in H2.
      auto.
      auto.
      intuition.
    - inversion H2; subst.
      assert (In x (dom E)).
      apply in_dom in H0.
      auto.
      auto.
      intuition.
  Qed.

  Lemma typ_unique :
    forall Gamma e d t1 E1, has_type_source Gamma e d t1 E1 ->
                            forall t2 E2, has_type_source Gamma e d t2 E2 -> almost_unique t1 t2 d.
    intros Gamma e d t1 E1 H.
    induction H; intros; unfold almost_unique.
    - inversion H0.
      auto.
    - inversion H1; subst.
      rewrite (ok_unique_type _ _ _ _ H (conj H0 H5)).
      reflexivity.
    - inversion H0; subst.
      reflexivity.
    - inversion H1; subst.
      apply IHhas_type_source1 in H.
      apply IHhas_type_source1 in H5.
      injection H5.
      intros.
      rewrite H2.
      reflexivity.
    - inversion H2; subst.
      reflexivity.
    - inversion H1; subst.
      reflexivity.
    - inversion H1; subst.
      apply IHhas_type_source1 in H5.
      apply IHhas_type_source2 in H6.
      inversion H5.
      inversion H6.
      auto.
    - auto.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma typ_inf_unique :
    forall Gamma e t1 E1, has_type_source Gamma e Inf t1 E1 ->
                          forall t2 E2, has_type_source Gamma e Inf t2 E2 -> t1 = t2.
    intros.
    pose (@typ_unique _ _ _ _ _ H _ _ H0).
    simpl in a.
    auto.
  Qed.

End Uniqueness.
