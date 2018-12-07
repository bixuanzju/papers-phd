Require Import definitions.
Require Import subtyping.
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
    let C := gather_vars_with (fun (x : context DExp) => dom x) in
    let D := gather_vars_with (fun (x : context TExp) => dom x) in
    let E := gather_vars_with (fun x : DExp => fv_source x) in
    let F := gather_vars_with (fun x : TExp => fv x) in
    constr:(union A (union B (union C (union D (union E F))))).

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


  Lemma extend_gamma : forall G E T e x t,
                         has_type_source G E T e -> wfs (extend x t G) -> has_type_source (extend x t G) E T e.
  Proof.
    intros.
    compute.
    induction H; intuition.
    - apply TyLam with (L:=L).
      intros.
      apply H1 in H2.
      (* stuck here *)
      admit.
      admit.
    - apply TyApp with (A:=A); auto.
    - apply TyPi with (L:=L).
      auto.
      intros.
      (* pose (H1 H4). *)
      (* apply H1 in H4. *)
      admit.
    - admit.
    - admit.
    - apply TySub with (A':=A')(B:=B); auto.
    - apply TyInter1 with (A2:=A2); auto.
    - apply TyInter2 with (A1:=A1); auto.
  Admitted.


  Lemma typing_wfs : forall G E T E',
                       has_type_source G E T E' -> wfs G
                       with weaken_wfs : forall G x t,
                                           wfs (extend x t G) -> wfs G.

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
                     wfs G -> List.In (x, t) G -> exists e, has_type_source G t DStar e.
  Proof.
    intros.
    induction G.
    inversion H0.
    destruct a.
    inversion H0.
    rewrite H1.
    rewrite H1 in H.
    inversion H; subst.
    exists e.
    apply extend_gamma.
    auto.
    compute.
    auto.
    assert (wfs G).
    apply weaken_wfs with (x:=v)(t:=d).
    compute.
    auto.
    intuition.
    inversion H4.
    exists x0.
    assert (wfs (extend v d G)).
    auto.
    pose (extend_gamma _ _ _ _ _ _ H3 H5).
    auto.
  Qed.


  Lemma term_well_typed : forall Gamma A B E,
                            has_type_source Gamma A B E -> exists B', has_type_source Gamma B DStar B'.
  Proof.
    intros.
    induction H; auto.
    -
      exists DStar.
      auto.
    - induction H.
      inversion H0.
      assert (wfs (extend x0 U E)).
      compute.
      apply wfs_cons with (e:=e); auto.
      induction H0.
      inversion H0.
      exists e.
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
      inversion IHhas_type_source1.
      inversion IHhas_type_source2.
      inversion H1; subst.
      admit.
      admit.
      admit.
      admit.
    - exists C'.
      auto.
    - exists B'.
      auto.
    - admit.
    - inversion IHhas_type_source1.
      inversion IHhas_type_source2.
      exists (DAnd x x0).
      auto.
    - inversion IHhas_type_source.
      inversion H0; subst.
      exists A'; auto.
      admit.
      admit.
      admit.
    -
      admit.
      (* inversion H0; subst. *)
      (* exists A'. *)
      (* auto. *)
      (* admit. *)
  Admitted.


  Lemma typing_wfs_2 : forall G E T E',
                         has_type_source2 G E T E' -> wfs2 G
                         with weaken_wfs_2 : forall G x t, wfs2 (extend x t G) -> wfs2 G.
  Proof.
    intros.
  Admitted.


  Inductive trans_ctx : context DExp -> context DExp -> Prop :=
  | trans_nil : trans_ctx nil nil
  | trans_cons : forall sctx tctx x T t,
      trans_ctx sctx tctx ->
      has_type_source sctx T DStar t ->
      trans_ctx ((x,T) :: sctx) ((x,t) :: tctx).


  Require Import Program.Equality.


  Lemma wfs_trans : forall G, wfs G -> wfs2 G
    with type_trans : forall G T T', has_type_source G T DStar T' -> exists t, has_type_source2 G T' DStar t.
  Proof.
    (* First one *)
    intros.
    induction G; auto.
    (* Second one *)
    intros.
    dependent induction H.
    - exists TStar.
      auto.
    - exists (TFVar x).
      auto.
    - pose (TyApp _ _ _ _ _ _ _ H H0).
      rewrite x in h.
      apply type_trans in h; auto.
    - pose (TyPi _ _ _ _ _ _ H H0).
      apply type_trans in h; auto.
    - pose (TyAnd _ _ _ _ _ H H0).
      apply type_trans in h; auto.
    - admit.
    - admit.
    - pose (TySub _ _ _ _ _ _ H H0).
      apply type_trans in h; auto.
    - pose (TyMerge1 _ _ _ E2 _ H).
      apply type_trans in h; auto.
    - apply TyMerge2 with (E1:=E1) in H.
      apply type_trans in H; auto.
    - apply TyInter1 in H.
      apply type_trans in H; auto.
    - apply TyInter2 in H.
      apply type_trans in H; auto.
  Admitted.


  Lemma preserve : forall Gamma A B A' B',
                     has_type_source Gamma A B A' -> has_type_source Gamma B DStar B' -> exists e, has_type_source2 Gamma A' B' e.
  Proof.
    intros.
    induction H.
    -
      inversion H0; subst.
      exists TStar.
      apply Ty2Star.
      auto.
    -
      exists (TFVar x).
      auto.
    -
      pick_fresh x.
      assert (~ In x L).
      admit.
      pose (H0 x H1).
      inversion e.
      exists (TLam (close x x0)).
      apply_fresh Ty2Lam as x.
      admit.
    -
      inversion IHhas_type_source1.
      inversion IHhas_type_source2.
      exists (TApp x x0).
      (* apply Ty2App. *)
      admit.
    -
      inversion IHhas_type_source.

End Properties.