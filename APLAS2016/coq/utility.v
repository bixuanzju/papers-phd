Require Import definitions.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module Util
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.

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

End Util.