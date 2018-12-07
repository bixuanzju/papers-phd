Require Import definitions.
Require Import typing.
Require Import utility.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module Properties
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.

  Module M' := Typing VarTyp set.
  Export M'.

  (* Tactics dealing with fresh variables, taken from STLC_Tutorial *)

  Ltac gather_vars_with F :=
    let rec gather V :=
        (match goal with
           | H:?S
             |- _ =>
             let FH := constr:(F H) in
             match V with
               | empty => gather FH
               | context [FH] => fail 1
               | _ => gather (union FH V)
             end
           | _ => V
         end)
    in
    let L := gather (empty : vars) in
    eval simpl in L.


  Ltac gather_vars :=
    let A := gather_vars_with (fun x : vars => x) in
    let B := gather_vars_with (fun x : var => singleton x) in
    let D := gather_vars_with (fun (x : context TExp) => dom x) in
    let F := gather_vars_with (fun x : TExp => fv x) in
    constr:(union A (union B (union D F))).

  Ltac beautify_fset V :=
    let rec go Acc E :=
        (match E with
           | union ?E1 ?E2 => let Acc1 := go Acc E1 in
                              go Acc1 E2
           | empty => Acc
           | ?E1 => match Acc with
                      | empty => E1
                      | _ => constr:(union Acc E1)
                    end
         end)
    in
    go (empty : vars) V.

  Parameter var_fresh : forall L : vars, {x : var | not (In x L) }.

  Ltac pick_fresh_gen L Y :=
    let Fr := fresh "Fr" in
    let L := beautify_fset L in
    destruct (var_fresh L) as (Y, Fr).

  Ltac pick_fresh x :=
    let L := gather_vars in (pick_fresh_gen L x).

  Ltac apply_fresh_base_simple lemma gather :=
    let L0 := gather in
    let L := beautify_fset L0 in
    first
      [ apply (lemma L) | eapply (lemma L) ].

  Ltac intros_fresh x :=
    first
      [ let Fr := fresh "Fr" x in
        intros x Fr
      | let x2 :=
            (match goal with
               | |- ?T -> _ =>
                 match T with
                   | var => fresh "y"
                   | vars => fresh "ys"
                   | list var => fresh "ys"
                   | _ => fresh "y"
                 end
             end)
        in
        let Fr := fresh "Fr" x2 in
        intros x2 Fr ].

  Fixpoint fresh (L : vars) (n : nat) (xs : list var) : Prop :=
    match xs with
      | nil => match n with
                 | 0 => True
                 | S _ => False
               end
      | (x :: xs')%list =>
        match n with
          | 0 => False
          | S n' => (not (In x L)) /\ fresh (union L (singleton x)) n' xs'
        end
    end.

  Ltac apply_fresh_base lemma gather var_name :=
    apply_fresh_base_simple lemma gather;
    try
      match goal with
        | |- _ -> not (In _ _) -> _ => intros_fresh var_name
        | |- _ -> fresh _ _ _ -> _ => intros_fresh var_name
      end.

  Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
    apply_fresh_base T gather_vars x.

  Lemma extend_gamma : forall G E T x t,
      has_type_target G E T ->
      wfs2 (extend x t G) ->
      has_type_target (extend x t G) E T.
  Proof.
    intros.
    compute.
    induction H; intuition.
    - apply Ty2Star; auto.
    - apply Ty2Var; auto; apply in_cons; auto.
    - apply Ty2Lam with (L:=L).
      intros.
      apply H1 in H2.
      (* stuck here *)
      admit.
      admit.
    - apply Ty2Mu with (L:=L).
      intros.
      admit.
      admit.
    - apply Ty2App with (A:=A); auto.
    - apply Ty2Pi with (L:=L).
      auto.
      intros.
      (* pose (H1 H4). *)
      (* apply H1 in H4. *)
      admit.
    - admit.
    - admit.
  Admitted.

  Lemma typing_wfs : forall G E T,
      has_type_target G E T -> wfs2 G
  with weaken_wfs : forall G x t,
      wfs2 (extend x t G) -> wfs2 G.

  Proof.
    intros.
    induction H; auto.
    pick_fresh y.
    assert (~ In y L).
    (* apply not_in_L x *)
    admit.
    pose (H0 y H1).
    apply weaken_wfs in w; auto.
    intros.
    inversion H; subst.
    apply typing_wfs in H4; auto.
  Admitted.

  Lemma in_gamma : forall G x t,
      wfs2 G -> List.In (x, t) G ->
      has_type_target G t TStar.
  Proof.
    intros.
    induction G.
    inversion H0.
    destruct a.
    inversion H0.
    rewrite H1.
    rewrite H1 in H.
    inversion H; subst.
    apply extend_gamma.
    auto.
    compute.
    auto.
    assert (wfs2 G).
    apply weaken_wfs with (x:=v)(t:=t1).
    compute.
    auto.
    intuition.
    pose (extend_gamma _ _ _ _ _ H4 H).
    auto.
  Qed.

  Lemma term_well_typed : forall Gamma A B,
      has_type_target Gamma A B ->
      has_type_target Gamma B TStar.
  Proof.
    intros.
    induction H; auto.
    - apply Ty2Star; auto.
    - induction H.
      inversion H0.
      assert (wfs2 (extend x0 U E)).
      compute.
      apply wfs2_cons; auto.
      induction H0.
      inversion H0.
      rewrite <- H5.
      rewrite <- H4.
      apply extend_gamma; auto.
      simpl in H0.
      apply in_gamma with (x:=x); auto.
      apply in_cons; auto.
    -
      pick_fresh y.
      assert (~ In y L).
      admit.
      pose (H y H1).
      apply typing_wfs in h.
      inversion h; subst.
      clear Fr.
      (* stuck here *)
      admit.
      (* pose (H0 y H1). *)
      (* inversion e0. *)
      (* assert (forall z, ~ In z L -> has_type_source (extend z A Gamma) (open_source B (DFVar z)) DStar x). *)
      (* intros. *)
      (* pose (H0 z H3). *)
      (* inversion e1. *)
      (* inversion H0. *)
      (* pose (TyPi _ _ _ _ _ _ H6 H0). *)
    -
      inversion IHhas_type_target1.
      inversion IHhas_type_target2.
      inversion H1; subst.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
  Admitted.

End Properties.