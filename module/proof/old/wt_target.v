Set Implicit Arguments.


Require Import definitions.
(* Require Import subtyping. *)
Require Import typing.
Require Import LibLN.

Require Import Coq.Arith.EqNat.
Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.
Require Import MSetProperties.
Require Import Coq.Init.Specif.



(*

Issues

[ ] elab_unique (uniqueness of translation, not true for now)
[ ] red_preserve (source reduction and uniqueness)
[ ] opt_subst_commute1 (opt problem)
[ ] trans_wf (again coq doesn't know if it terminates)
[x] typing_substitution (complete)


Discuss
- applyS is wrong
- issue in pi case
- subtyping casts seems incorrect (castdn is wrong)
- the "main" lemma seem not correct (A <| B <: C |> A' where A is typable in old, A' is in new)
- red_star still needed in proof of app_lemma (casts case)

 *)

Module WTTarget
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

  (* Module M := ExprDefs VarTyp set. *)
  (* Export M. *)

  (* Module N := SubTyping VarTyp set. *)
  (* Export N. *)



  Module M := Typing VarTyp set.
  Export M.


  Module MSetProperties := WPropertiesOn(VarTyp)(M).

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


  Lemma dom_union : forall (A : Type) (E G : context A) x,
      In x (dom (E ++ G)) <-> In x (union (dom E) (dom G)).
  Proof.
    intros.
    gen G.
    induction E; intros; simpl.
    splits*.

    unfold "<->".
    splits*; intros.


    (* -> *)
    apply add_spec in H.
    inversion* H.

    apply union_spec; left.
    apply add_spec; left; auto.

    apply IHE in H0.
    apply union_spec in H0.
    inversion H0.

    apply union_spec; left.
    apply add_spec; right; auto.

    apply union_spec; right; auto.


    (* <- *)


    apply union_spec in H.
    inversion H.
    apply add_spec in H0.
    inversion H0.
    apply add_spec; left; auto.

    apply add_spec; right.
    apply IHE.
    apply union_spec; left; auto.

    apply add_spec; right.
    apply IHE.
    apply union_spec; right; auto.
  Qed.



  Lemma dom_map_id : forall (A B : Type) (E : context A) (f : A -> B),
      dom E = dom (mapctx f E).
  Proof.
    unfold mapctx.
    intros.
    induction E; auto.
    simpl.
    rewrite* IHE.
  Qed.

  Ltac not_in_L x :=
  repeat rewrite dom_union; repeat rewrite M.union_spec;
  repeat match goal with
    | H: M.In x M.empty |- _ => inversion H
    | H:_ |- context [M.In x (dom nil)] => simpl
    | H:_ |- context [M.In x (dom ((?v, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H: _ |- context [M.In ?v (dom ((x, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H1: ~ ?l, H2: ?l |- _ => contradiction
    | H: ~ M.In ?y (M.singleton x) |- not (VarTyp.eq x ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; assumption
    | H: ~ M.In x (M.singleton ?y) |- not (VarTyp.eq x ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; unfold not; intros; apply H; symmetry; assumption
    | H: ~ M.In x (M.add ?v M.empty) |- _ => rewrite <- MSetProperties.singleton_equal_add in H
    | H: not (M.In x (dom ?l)) |- _ => rewrite dom_union in H; simpl in H
    | H: not (M.In x (M.union ?l1 ?l2)) |- _ =>
      rewrite M.union_spec in H
    | H: not (M.In x ?l3 \/ ?l) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (?l \/ M.In x ?l3) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (M.In x ?l1) |- not (M.In x ?l1) => assumption
    | H:_ |- ~ (x == ?v \/ M.In ?v ?l) => unfold not; intro HInv; inversion HInv as [HH | HH]
    | H:_ |- not (?A \/ ?B) => apply and_not_or; split
    (* | H1: ~ M.In x (M.singleton ?v), H2: ?v == x |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; assumption *)
    (* | H1: ~ M.In x (M.singleton ?v), H2: x == ?v |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; symmetry; assumption *)
    | H: not (M.In x ?l1) |- not (M.In x ?l2) =>
      unfold not; intros; apply H; repeat rewrite M.union_spec; auto 10
  end.


  Inductive trans_ctx : context DExp -> context TExp -> Prop :=
  | trans_nil : trans_ctx nil nil
  | trans_cons : forall sctx tctx x T t,
      trans_ctx sctx tctx ->
      has_type_source2 sctx T DStar t ->
      trans_ctx ((x,T) :: sctx) ((x,t) :: tctx).




  Lemma trans_dom : forall Gamma Gamma',
      trans_ctx Gamma Gamma' -> dom Gamma = dom Gamma'.
  Proof.
    intros Gamma Gamma' Ctx.
    induction Ctx; auto.
    simpl.
    rewrite IHCtx; auto.
  Qed.

  Inductive has_cano : DExp -> Prop :=
  | HStar : has_cano DStar
  | HPi : forall A B, has_cano (DPi A B)
  | HAnd : forall A B, has_cano (DAnd A B).

  Hint Constructors has_cano.

  (* New version along with typing evidence *)
  (* Isn't that a slim version of typing? *)
  Inductive P (Ctx : context DExp) : DExp -> DExp -> TExp -> Prop :=
  | PStar : P Ctx DStar DStar TStar
  (* | PVar : forall x ty, List.In (x, ty) Ctx -> P Ctx (DFVar x) ty (TFVar x) *)
  (* | PLam : forall A B E e, P Ctx (DLam E) (DPi A B) (TLam e) *)
  (* | PApp : forall (E1 E2 : DExp) B E2 e1 e2, P Ctx (DApp E1 E2) (open_source B E2) (TApp e1 e2) *)
  | PPi : forall A B a b L,
      has_type_source2 Ctx A DStar a ->
      (forall x, not (In x L) -> has_type_source2 (extend x A Ctx) (open_source B (DFVar x)) DStar (open b (TFVar x))) ->
      P Ctx (DPi A B) DStar (TPi a b)
  (* | PCastdn : forall A C a, *)
  (*     P Ctx (DCastdn A) C (TCastdn a) *)
  (* | PCastup : forall A B a, *)
      (* P Ctx (DCastup A) B (TCastup a) *)
  | PAnd : forall A B a b,
      has_type_source2 Ctx A DStar a ->
      has_type_source2 Ctx B DStar b ->
      P Ctx (DAnd A B) DStar (TProd a b)
  | Step : forall A B E e1 e2,
      P Ctx E A e1 -> P Ctx E B e2 -> P Ctx E (DAnd A B) (TPair e1 e2).

  Hint Constructors P.


  Lemma prop_cano : forall Gamma A B e,
      has_cano A -> has_type_source2 Gamma A B e -> P Gamma A B e.
  Proof.

    introv IH IHTy.
    induction IHTy; eauto; try (inversion IH; fail).

    pose (IHP := IHIHTy IH).
    inverts* IHP.
    pose (IHP := IHIHTy IH).
    inverts* IHP.
  Qed.


  (* Lemma prop_and : forall Gamma E A B e (a b : TExp), *)
  (*     has_type_source2 Gamma E (DAnd A B) e -> exists a b, e = TPair a b. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply prop_cano in H. *)
  (*   inversion H; subst. *)
  (*   exists e1 e2; auto. *)


(** ** Inversion Lemmas for Typing *)

  Lemma typing_star_inv : forall Gamma e,
      has_type_source2 Gamma DStar DStar e -> e = TStar.
  Proof.
    intros.
    apply prop_cano in H; inversion H; auto.
  Qed.

  Lemma typing_and_inv : forall Gamma A B e,
      has_type_source2 Gamma (DAnd A B) DStar e ->
      exists a b, e = TProd a b /\ has_type_source2 Gamma A DStar a /\ has_type_source2 Gamma B DStar b.
  Proof.
    intros.
    apply prop_cano in H.
    inversion H; subst.
    exists a b; auto.
    auto.
  Qed.

  Lemma typing_pi_inv : forall Gamma A B e,
      has_type_source2 Gamma (DPi A B) DStar e ->
      exists a b, e = TPi a b /\ has_type_source2 Gamma A DStar a /\
             (exists L, forall x, not (In x L) -> has_type_source2 (extend x A Gamma) (open_source B (DFVar x)) DStar (open b (TFVar x))).
  Proof.
    intros.
    apply prop_cano in H.
    inversion H; subst.
    exists a; exists b.
    split; auto.
    split; auto.
    exists L; intros; auto.
    auto.
  Qed.


(* ********************************************************************** *)



  (*

x : * & * |- x : * ~> fst x
x : * & * |- x : * ~> snd x



   *)




  (* False for the moment *)
  Axiom elab_unique : forall Gamma A C1 C2 t1 t2,
      has_type_source2 Gamma A C1 t1 ->
      has_type_source2 Gamma A C2 t2 ->
      t1 = t2.


  Lemma singleton_neq : forall x y, ~ (In x (singleton y)) -> ~ (x = y).
  Proof.
    intros.

    intros IH.
    apply H.
    apply singleton_spec; auto.
  Qed.


  (** Substitution for a fresh name is identity. *)

  Lemma subst_fresh_s : forall x e u,
      ~ (In x (fv_source e)) -> subst_source x u e = e.
  Proof.
    intros.
    induction e; simpls; fequals*;

    try (match goal with
         | [ H1: _ -> subst_source _ _ ?X = ?X |- subst_source ?Y _ ?X = ?X ] => apply H1; not_in_L Y
         end).

    cases_if*.
    apply eqb_eq in H0.
    apply singleton_neq in H.
    subst.
    contradiction H; auto.

  Qed.


  Lemma subst_fresh : forall x e u,
      ~ (In x (fv e)) -> subst x u e = e.
  Proof.
    intros.
    induction e; simpls; fequals*;
      try (match goal with
           | [ H1: _ -> subst _ _ ?X = ?X |- subst ?Y _ ?X = ?X ] => apply H1; not_in_L Y
           end).

    cases_if*.
    apply eqb_eq in H0.
    apply singleton_neq in H.
    subst.
    contradiction H; auto.
  Qed.

  (** Substitution on indices is identity on well-formed terms. *)


  Lemma open_rec_term_core :forall e j v i u,
      i <> j ->
      open_rec j v e = open_rec i u (open_rec j v e) -> e = open_rec i u e.
  Proof.
    induction e; introv Neq Equ;
      simpl in *; inversion* Equ; f_equal*.
    cases_if*.
    cases_if*.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H1.
    rewrite H in Neq.
    rewrite H1 in Neq.
    contradict Neq; auto.
    simpl in Equ.
    rewrite H in Equ; auto.

  Qed.


  Lemma open_rec_sterm_core :forall e j v i u,
      i <> j ->
      open_rec_source j v e = open_rec_source i u (open_rec_source j v e) -> e = open_rec_source i u e.
  Proof.
    induction e; introv Neq Equ;
      simpl in *; inversion* Equ; f_equal*.
    cases_if*.
    cases_if*.
    apply Nat.eqb_eq in H.
    apply Nat.eqb_eq in H1.
    rewrite H in Neq.
    rewrite H1 in Neq.
    contradict Neq; auto.
    simpl in Equ.
    rewrite H in Equ; auto.

  Qed.



  Lemma open_rec_term : forall t u,
      term t -> forall k, t = open_rec k u t.
  Proof.
    induction 1; intros; simpl; f_equal*.

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_term_core t1 0 (TFVar x)); auto.
    apply H0.
    not_in_L x.

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_term_core t2 0 (TFVar x)); auto.
    apply H1.
    not_in_L x.
  Qed.

  Lemma open_rec_sterm : forall t u,
      sterm t -> forall k, t = open_rec_source k u t.
  Proof.
    induction 1; intros; simpl; f_equal*.

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_sterm_core t1 0 (DFVar x)); auto.
    apply H0.
    not_in_L x.

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_sterm_core t2 0 (DFVar x)); auto.
    apply H1.
    not_in_L x.
  Qed.

  Lemma subst_open_s : forall x u t1 t2,
      sterm u ->
      subst_source x u (open_source t1 t2) = open_source (subst_source x u t1) (subst_source x u t2).
  Proof.
    intros. unfold open_source. generalize 0.
    induction t1; intros; simpl; f_equal*.
    destruct (Nat.eqb n0 n); auto.
    cases_if*.
    apply* open_rec_sterm.
    auto.
  Qed.


  Lemma subst_open : forall x u t1 t2,
      term u ->
      subst x u (open t1 t2) = open (subst x u t1) (subst x u t2).
  Proof.
    intros. unfold open. generalize 0.
    induction t1; intros; simpl; f_equal*.
    destruct (Nat.eqb n0 n); auto.
    cases_if*.
    apply* open_rec_term.
    auto.
  Qed.

  Lemma subst_open_var_s : forall x y u e,
      y <> x -> sterm u ->
      open_source (subst_source x u e) (DFVar y) = subst_source x u (open_source e (DFVar y)).
  Proof.
    introv Neq Wu. rewrite* subst_open_s.
    simpl.
    cases_if*.
    apply eqb_eq in H.
    contradiction.
  Qed.


  Lemma subst_open_var : forall x y u e,
      y <> x -> term u ->
      open (subst x u e) (TFVar y) = subst x u (open e (TFVar y)).
  Proof.
    introv Neq Wu. rewrite* subst_open.
    simpl.
    cases_if*.
    apply eqb_eq in H.
    contradiction.
  Qed.


  Lemma subst_intro_s : forall x t u,
      ~ (In x (fv_source t)) -> sterm u ->
      open_source t u = subst_source x u (open_source t (DFVar x)).
  Proof.
    introv Fr Wu. rewrite* subst_open_s.
    rewrite* subst_fresh_s. simpl.
    assert (eqb x x = true).
    rewrite eqb_eq.
    reflexivity.
    rewrite H; auto.
  Qed.

  Lemma subst_intro : forall x t u,
      ~ (In x (fv t)) -> term u ->
      open t u = subst x u (open t (TFVar x)).
  Proof.
    introv Fr Wu. rewrite* subst_open.
    rewrite* subst_fresh. simpl.
    assert (eqb x x = true).
    rewrite eqb_eq.
    reflexivity.
    rewrite H; auto.
  Qed.


  (* do we need x <> y in the conclusion? *)
  Lemma binds_push_inv : forall (A : Type) x y (U : A) V E,
      List.In (x, U) (extend y V E) -> x = y /\ U = V \/ List.In (x, U) E.
  Proof.
    intros.

    apply in_inv in H.
    inversion H.
    inversion H0; auto.
    right; auto.
  Qed.





  Definition contains_terms (E : context DExp) :=
    forall x U, List.In (x,U) E -> sterm U.


  Lemma term_opt1 : forall e,
      term e -> term (opt (TFst e)).
  Proof.
    intros.
    induction H; try (apply term_fst); auto.


    apply_fresh term_lam as y.
    apply H.
    not_in_L y.


    apply_fresh term_pi as y; auto.
    apply H0.
    not_in_L y.
  Qed.



  Lemma term_opt2 : forall e,
      term e -> term (opt (TSnd e)).
  Proof.
    intros.
    induction H; try (apply term_snd); auto.


    apply_fresh term_lam as y.
    apply H; not_in_L y.

    apply_fresh term_pi as y; auto.
    apply H0; not_in_L y.
  Qed.


  (** Terms are stable by substitution *)

  Lemma subst_term_s : forall t z u,
      sterm u -> sterm t -> sterm (subst_source z u t).
  Proof.
    induction 2; simple*.
    case_if*.
    apply_fresh sterm_lam as y. rewrite* subst_open_var_s.
    apply H1.
    not_in_L y.
    not_in_L y.
    apply singleton_neq; auto.


    apply_fresh sterm_pi as y; auto. rewrite* subst_open_var_s.
    apply H2.
    not_in_L y.
    not_in_L y.
    apply singleton_neq; auto.
  Qed.



  (** Terms are stable by open *)

  Lemma open_term_s : forall v u,
      body_source v -> sterm u -> sterm (open_source v u).
  Proof.
    intros.
    destruct H.
    pick_fresh y.
    rewrite (@subst_intro_s y); auto; not_in_L y.
    apply subst_term_s; auto.
  Qed.




  (** The value predicate only holds on locally-closed terms. *)

  Lemma svalue_regular : forall e,
      svalue e -> sterm e.
  Proof.
    introv TyV.
    induction TyV; auto.
  Qed.


  Lemma red_regular : forall e1 e2,
    sred e1 e2 -> sterm e1 /\ sterm e2.
  Proof.
    introv TyR.
    induction* TyR.

    (* beta *)
    split.
    apply sterm_app; auto.
    apply svalue_regular in H0; auto.
    apply svalue_regular in H0.
    inversion H; subst.
    apply open_term_s; auto.
    unfold body_source.
    exists L; auto.

    (* app2 *)
    split;
    apply svalue_regular in H;
    apply sterm_app; auto;
    destructs* IHTyR.

    (* castelem *)
    split; apply svalue_regular in H; auto.

    (* merge1 *)
    split;
    apply svalue_regular in H; destructs* IHTyR.




  Qed.










  Lemma regular_typing : forall Gamma A B e,
      has_type_source2 Gamma A B e -> wfs2 Gamma /\ contains_terms Gamma /\ sterm A /\ sterm B /\ term e.
  Proof.
    apply typing_induct with
    (P0 := fun Gamma (_ : wfs2 Gamma) => wfs2 Gamma /\ contains_terms Gamma);
      unfolds contains_terms; intros; splits*.


    (* lam *)
    apply_fresh sterm_lam as y.
    assert (~ In y L).
    not_in_L y.
    pose (IH := H0 y H1).
    destructs* IH.
    apply_fresh term_lam as y.
    assert (~ In y L).
    not_in_L y.
    apply H0; auto.


    (* app *)
    destructs* H.
    destructs* H0.
    inversion* H3; subst.
    pick_fresh y.
    assert (~ In y L).
    not_in_L y.
    rewrite subst_intro_s with (x := y).
    apply subst_term_s; auto.
    pose (H12 _ H9); auto.
    not_in_L y.
    auto.

    (* Pi *)
    apply_fresh sterm_pi as y.
    destructs* H.
    assert (~ In y L).
    not_in_L y.
    apply H0; auto.
    apply_fresh term_pi as y.
    destructs* H.
    assert (~ In y L).
    not_in_L y.
    apply H0; auto.

    (* Inter1 *)
    destructs* H; inversion* H2.
    apply term_opt1; auto.
    destructs* H.

    (* Inter2 *)
    destructs* H; inversion* H2.
    apply term_opt2; auto.
    destructs* H.


    (* wfs nil *)
    intros.
    inversion H.


    (* wfs cons *)
    intros.
    destruct (binds_push_inv H0) as [[? ?]|?]; subst*.


  Qed.

  Lemma weaken_wfs : forall G x t, wfs2 (extend x t G) -> wfs2 G.
  Proof.
    intros.
    inversion H; subst.
    apply regular_typing in H4.
    destruct H4; auto.
  Qed.




  (*

Counter example:

[x/(*,*)] (opt (fst x))   =    fst (*, *)

opt (fst ([x/(*,*)] x))   =    *


when e is a variable x, u is a pair.

   *)


  Lemma opt_subst_commute1 : forall x u e,
      subst x u (opt (TFst e)) = opt (TFst (subst x u e)).
  Proof.
  Admitted.


  Lemma opt_subst_commute2 : forall x u e,
      subst x u (opt (TSnd e)) = opt (TSnd (subst x u e)).
  Proof.
  Admitted.



  Lemma subst_value : forall x u e,
      svalue e ->
      sterm u ->
      svalue (subst_source x u e).
  Proof.
    introv Val.
    induction Val; intros; simpl; auto.


    inversion H; subst.
    apply svalue_lam.
    apply_fresh sterm_lam as y.
    rewrite subst_open_var_s; auto.
    apply subst_term_s; auto.
    apply H2.
    not_in_L y.
    not_in_L y.
    apply singleton_neq; auto.



    inversion H; subst.
    apply svalue_pi.
    apply_fresh sterm_pi as y.
    apply subst_term_s; auto.
    rewrite subst_open_var_s; auto.
    apply subst_term_s; auto.
    apply H4.
    not_in_L y.
    not_in_L y.
    apply singleton_neq; auto.


    inversion H; subst.
    apply svalue_inter.
    apply sterm_inter; apply subst_term_s; auto.


  Qed.

  Lemma red_subst : forall x A B C,
      B ~~> C ->
      sterm A ->
      subst_source x A B ~~> subst_source x A C.
  Proof.
    intros. gen x A.
    induction H; intros; simpl; auto.
    rewrite subst_open_s.
    apply sred_beta.
    pose (subst_term_s x H1 H); auto.
    apply subst_value; auto.
    auto.


    apply sred_app1.
    apply subst_term_s; auto.
    auto.

    apply sred_app2.
    apply subst_value; auto.
    auto.

    apply sred_castelem.
    apply subst_value; auto.

    apply sred_merge1; auto.
    apply subst_term_s; auto.

    apply sred_merge2; auto.
    apply subst_value; auto.


    apply sred_unmerge1; auto.
    apply subst_term_s; auto.
    apply subst_term_s; auto.


    apply sred_unmerge2; auto.
    apply subst_term_s; auto.
    apply subst_term_s; auto.

  Qed.


  Lemma typing_weaken : forall G E F e T c,
      has_type_source2 (G ++ E ) e T c ->
      wfs2 (G ++ F ++ E) ->
      has_type_source2 (G ++ F ++ E ) e T c.
  Proof.
    introv Typ. gen_eq Env: (G ++ E). gen G.
    induction Typ; introv EQ W; subst; eauto.


    (* var *)
    apply* Ty2Var; auto.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app.
    left; auto.
    apply in_or_app.
    right; apply in_or_app; right; auto.

    (* lam *)
    apply_fresh Ty2Lam as y.
    pose (IHTyp G); auto.
    assert (~ In y L).
    not_in_L y.
    pose (IH := H0 y H1 (extend y A G)).
    apply IH; auto.

    pose (IHPi := IHTyp G Logic.eq_refl W).
    destruct (typing_pi_inv IHPi) as [? [? [? [HH ?]]]].

    simpl.
    apply wfs2_cons with (e := x); auto.
    not_in_L y.
    apply dom_union in H4.
    apply union_spec in H4.
    inversion H4; contradiction.

    (* pi *)
    apply_fresh Ty2Pi as y.
    apply IHTyp; auto.
    assert (~ In y L).
    not_in_L y.
    pose (IH := H0 y H1 (extend y A G)).
    apply IH; auto.

    pose (IHA := IHTyp G Logic.eq_refl W).
    simpl.
    apply wfs2_cons with (e := t1); auto.
    not_in_L y.
    apply dom_union in H4.
    apply union_spec in H4.
    inversion H4; contradiction.
  Qed.



  Ltac cross :=
    rewrite subst_open_var_s; try cross.

  Tactic Notation "cross" "*" :=
    cross; autos*.


  Lemma typing_substitution : forall E F A B T T' a b x,
      has_type_source2 E A T' a ->
      has_type_source2 (F ++ (extend x T' E)) B T b ->
      has_type_source2 (mapctx (subst_source x A) F ++ E) (subst_source x A B) (subst_source x A T) (subst x a b).
  Proof.
    introv Typv Typt.
    gen_eq G: (F ++ (extend x T' E)). gen F.

    apply typing_induct with
    (P := fun (G:context DExp) B T b (Typt : has_type_source2 G B T b) =>
            forall F, G = F ++ extend x T' E ->
                 has_type_source2 (mapctx (subst_source x A) F ++ E) (subst_source x A B) (subst_source x A T) (subst x a b))
      (P0 := fun (G:context DExp) (W:wfs2 G) =>
               forall F, G = F ++ extend x T' E ->
                    wfs2 (mapctx (subst_source x A) F ++ E));
      intros; subst; simpls subst.

    (* Star *)
    autos.

    (* Var *)
    simpl.
    case_if*.
    apply eqb_eq in H0.
    subst.
    assert (ty = T').
    (* look at i *)
    admit.
    subst.
    rewrite* subst_fresh_s.
    apply (typing_weaken nil E (mapctx (subst_source x A) F) Typv).
    simpl.
    apply H; auto.

    (* look at w *)
    admit.

    apply~ Ty2Var.

    assert (List.In (x0, ty) E).
    (* derive from i and H0 *)
    admit.

    rewrite* subst_fresh_s.

    apply in_or_app; auto.


    (* should derive from H1 and w *)
    admit.


    (* Lam *)
    simpl.
    apply_fresh Ty2Lam as y; auto.
    assert (~(y = x)).
    apply singleton_neq.
    not_in_L y.
    pose (TERM := regular_typing Typv).
    destructs* TERM.

    cross; auto.
    rewrite* subst_open_var.
    assert (~ (In y L)).
    not_in_L y.
    pose (IH := H0 y H7 (extend y A0 F)).
    simpl in IH.
    apply IH; auto.


    (* App *)
    rewrite* subst_open_s.
    simpl.
    simpl in H.
    eapply Ty2App.
    pose (IHApp := H F).
    apply IHApp; auto.
    pose (IHApp := H0 F).
    apply IHApp; auto.
    pose (Re := regular_typing Typv).
    destructs Re; auto.

    (* Pi *)
    simpl.
    apply_fresh Ty2Pi as y.
    simpl in H.
    pose (IHPi := H F).
    apply IHPi; auto.
    simpl in H0.

    assert (~ (In y L)).
    not_in_L y.
    pose (IHPi := H0 y H1 (extend y A0 F)).
    simpl in IHPi.
    assert (~ (y = x)).
    apply singleton_neq; not_in_L y.
    rewrite* <- subst_open_var_s in IHPi.
    rewrite* <- subst_open_var in IHPi.
    pose (Re := regular_typing Typv).
    destructs* Re.
    pose (Re := regular_typing Typv).
    destructs* Re.

    (* And  *)
    simpl.
    apply Ty2And.
    simpl in H.
    apply H; auto.
    simpl in H0.
    apply H0; auto.

    (* CastDown *)
    simpl.
    eapply Ty2CastDown; auto.
    apply regular_typing in Typv.
    destructs Typv.
    apply red_subst; auto.

    (* CastUp *)
    simpl.
    eapply Ty2CastUp; auto.
    apply regular_typing in Typv.
    destructs Typv.
    apply red_subst; auto.


    (* Merge1 *)
    simpl.
    apply Ty2Merge1; auto.
    apply subst_term_s; auto.
    destructs* (regular_typing Typv).

    (* Merge2 *)
    simpl.
    apply Ty2Merge2; auto.
    apply subst_term_s; auto.
    destructs* (regular_typing Typv).

    (* Inter *)
    simpl.
    apply Ty2Inter; auto.


    (* Inter1 *)
    simpl in H.
    pose (IHI := H F Logic.eq_refl).
    apply Ty2Inter1 in IHI.
    rewrite* <- opt_subst_commute1 in IHI.


    (* Inter2 *)
    simpl in H.
    pose (IHI := H F Logic.eq_refl).
    apply Ty2Inter2 in IHI.
    rewrite* <- opt_subst_commute2 in IHI.

    (* wfs2 nil *)
    destruct F.
    simpl in H.
    inversion H.
    inversion H.

    (* wfs2 cons *)
    induction F.
    simpl.
    pose (IH := regular_typing Typv).
    destructs* IH.

    clear IHF.
    assert (E0 = F ++ extend x T' E).
    simpl in H0.
    inversion H0; auto.


    subst.
    (* rewrite H1 in *. *)
    (* simpl in H0. *)
    inversion H0.
    subst.
    (* rewrite H3. *)
    pose (IH := H F Logic.eq_refl).
    simpl.
    eapply wfs2_cons.
    not_in_L x0.
    rewrite <- dom_map_id in H3.
    contradiction.
    apply add_spec; right; auto.


    auto.

    auto.

  Qed.


  Lemma type_subst : forall Gamma x A B E2 b0 e2 e,
      ~ (In x (fv b0)) ->
      ~ (In x (fv_source B)) ->
      has_type_source2 Gamma E2 A e2 ->
      has_type_source2 (extend x A Gamma) (open_source B (DFVar x)) DStar (open b0 (TFVar x)) ->
      has_type_source2 Gamma (open_source B E2) DStar e ->
      e = open b0 e2.
  Proof.
    intros.

    assert (has_type_source2 Gamma (open_source B E2) DStar (open b0 e2)).


    pose (IH := typing_substitution nil x H1 H2).
    simpl in IH.

    assert (open_source B E2 = subst_source x E2 (open_source B (DFVar x))).
    apply subst_intro_s; auto.
    pose (Trm := regular_typing H1).
    destructs* Trm.

    assert (open b0 e2 = subst x e2 (open b0 (TFVar x))).
    apply subst_intro; auto.
    pose (Trm := regular_typing H1).
    destructs* Trm.
    rewrite H4; rewrite H5; auto.

    eapply elab_unique; eauto.
  Qed.




  Lemma typing_strengthen : forall Gamma C c x,
      has_type_source2 (extend x C Gamma) C DStar c ->
      has_type_source2 Gamma C DStar c.
  Proof.
    intros.
    destruct (regular_typing H).
    inverts H0.
    pose (IH := @typing_weaken nil Gamma ((x,C)::nil) C DStar e).
    simpl in IH.
    destruct (regular_typing H).
    pose (IH' := IH H6 H0).
    lets : elab_unique H IH'.
    rewrite* H3.
  Qed.



  Lemma typing_wf_from_context : forall x U E,
      List.In (x, U) E ->
      wfs2 E ->
      exists i, has_type_source2 E U DStar i.
  Proof.
    introv B W. induction E using env_ind.
    inversion B.

    destruct (binds_push_inv B) as [[? ?]|?]; subst.
    inversion W; subst.
    exists e. apply (typing_weaken nil E ((x0,v)::nil)); auto.

    inversion W; subst.
    destructs (regular_typing H4).
    destruct (IHE H H0) as [i HH].
    exists i.
    apply (typing_weaken nil E ((x0,v)::nil)); auto.
  Qed.



  (*

Counter example:

3,,Int ~~> 3

3,,Int : *

But

3 : * ?


   *)

  (* Lemma red_star : forall E B C b, *)
  (*   B ~~> C -> *)
  (*   has_type_source2 E B DStar b -> *)
  (*   exists c, has_type_source2 E C DStar c. *)
  (* Proof. *)
  (* Admitted. *)


  (* Lemma red_star_rev : forall E B C c, *)
  (*   B ~~> C -> *)
  (*   has_type_source2 E C DStar c -> *)
  (*   exists b, has_type_source2 E B DStar b. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma typing_wf_from_typing : forall E A B e,
      has_type_source2 E A B e ->
      exists e', has_type_source2 E B DStar e'.
  Proof.
    induction 1; auto.

    (* Star *)
    exists TStar; auto.

    (* Var *)
    eapply typing_wf_from_context; eauto.

    (* Pi *)
    exists e; auto.

    (* App *)
    destruct IHhas_type_source2_1 as [e IHPi].
    destruct (typing_pi_inv IHPi) as [a [b [? [? [L IHB]]]]].
    exists (open b e2).
    pick_fresh x.

    destructs* (regular_typing H0).

    rewrite~ (@subst_intro x).
    rewrite~ (@subst_intro_s x).
    apply (@typing_substitution Gamma nil E2 (open_source B (DFVar x)) DStar A e2 (open b (TFVar x))); auto.
    simpl.
    apply IHB.
    not_in_L x.
    not_in_L x.
    not_in_L x.

    (* CastUp *)
    exists* c.


    (* CastDown *)
    exists* b.


    (* And *)
    destruct IHhas_type_source2_1 as [a1 IH1].
    destruct IHhas_type_source2_2 as [a2 IH2].
    exists (TProd a1 a2); auto.


    (* Inter1 *)
    destruct IHhas_type_source2 as [a IH].
    destruct (typing_and_inv IH) as [a1 [? [? [? ?]]]].
    exists a1; auto.


    (* Inter2 *)
    destruct IHhas_type_source2 as [a IH].
    destruct (typing_and_inv IH) as [? [a2 [? [? ?]]]].
    exists a2; auto.
  Qed.



  Lemma ctx_trans : forall Gamma Gamma',
      trans_ctx Gamma Gamma' ->
      forall x t T,
        List.In (x, T) Gamma ->
        has_type_source2 Gamma T DStar t ->
        List.In (x, t) Gamma'.
  Proof.
    intros Gamma Gamma' IH.
    induction IH; intros.
    inversion H.
    apply in_inv in H0.
    (* eapply typing_strengthen in H1. *)

    destruct H0.
    inversion H0; subst.
    apply typing_strengthen in H1.
    pose (elab_unique H H1).
    rewrite e.
    simpl; auto.

    destructs (regular_typing H).

    assert (has_type_source2 sctx T0 DStar t1).
    lets : typing_wf_from_context H0 H2.
    destruct H7.
    pose (@typing_weaken nil sctx ((x,T)::nil) T0 DStar x1 H7).
    simpl in h.
    destruct (regular_typing H1).
    apply h in H8.
    pose (elab_unique H1 H8).
    rewrite* e.

    pose (IHIH _ _ _ H0 H7).
    simpl.
    right; auto.
  Qed.

  Lemma pair_inverse : forall Gamma e t1 t2,
      has_type Gamma e (TProd t1 t2) ->
      has_type Gamma (opt (TFst e)) t1 /\ has_type Gamma (opt (TSnd e)) t2.

  Proof.
    intros.
    split.
    destruct e; inversion H; subst; simpl; try (eapply TyTFst; exact H).
    assumption.

    destruct e; inversion H; subst; simpl; try (eapply TyTSnd; exact H).
    assumption.
  Qed.



  (*

Counter example

Int ,, Bool ~~> Int

T |- Bool : * ~> Bool
-----------------------------
T |- Int ,, Bool : * ~> Bool

T |- Int : * ~> Int

But Bool cannot reduce to Int



   *)


  Lemma red_preserve : forall A B Gamma a b,
      A ~~> B ->
      has_type_source2 Gamma A DStar a ->
      has_type_source2 Gamma B DStar b ->
      red a b.
  Proof.


  Admitted.


  Lemma trans_wf : forall Gamma Gamma',
      trans_ctx Gamma Gamma' -> wfs2 Gamma -> wft Gamma'.

  Proof.
    introv Tyv Typ.

    induction Typ; auto.
    inverts* Tyv.
    inverts* Tyv.

    apply wft_cons.
    admit.

    admit.
  Qed.



  (* Lemma gen_wt_target: forall Gamma Gamma' A B b e, *)
  (*     has_type_source2 Gamma A B e -> *)
  (*     trans_ctx Gamma Gamma' -> *)
  (*     has_type_source2 Gamma B DStar b -> *)
  (*     has_type Gamma' e b. *)
  (* Proof. *)
  (*   introv Typ. *)
  (*   gen Gamma' b. *)
    (*


  Gamma : context DExp
  A, B : DExp
  e : TExp
  Typ : has_type_source2 Gamma A B e
  ============================
   forall (Gamma' : context TExp) (b : TExp),
   trans_ctx Gamma Gamma' -> has_type_source2 Gamma B DStar b -> has_type Gamma' e b


     *)
    (* apply typing_induct with *)
    (* (P := fun (Gamma : context DExp) A B e (Typ : has_type_source2 Gamma A B e) => *)
    (*         forall (Gamma' : context TExp) (b : TExp), *)
    (*           trans_ctx Gamma Gamma' -> has_type_source2 Gamma B DStar b -> has_type Gamma' e b) *)
    (*   (P0 := fun (Gamma : context DExp) (W : wfs2 Gamma) => *)
    (*         forall (Gamma' : context TExp) (b : TExp), *)
    (*           trans_ctx Gamma Gamma' -> has_type_source2 Gamma B DStar b -> wft Gamma'). *)


    (* induction Typ; inverts* Tyv. *)

    (* apply wft_cons. *)
    (* admit. *)

  (* Admitted. *)


  Lemma gen_wt_target: forall Gamma Gamma' A B b e,
      has_type_source2 Gamma A B e ->
        trans_ctx Gamma Gamma' ->
        has_type_source2 Gamma B DStar b ->
        has_type Gamma' e b.
  Proof.
    introv Ty.
    gen Gamma' b.
    (* introv Typa Typb. *)
    (* gen F. *)
    (* apply typing_induct with *)
    (*   (P := fun (E : context DExp) A B a (Typa : has_type_source2 E A B a) => *)
    (*           forall (F : context TExp), trans_ctx E F -> has_type F a b) *)
    (*     (P0 := fun (E : context DExp) (W:wfs2 E) => *)
    (*           forall (F : context TExp), trans_ctx E F -> wft F). *)
    (* apply typing_induct  *)
    (*   (P0 := fun c (_ : wfs2 c) => forall E E', trans_ctx E E' -> wft E'). *)
    induction Ty; introv Ctx TransB.
    (* Star *)
    - asserts_rewrite (b = TStar).
      eapply typing_star_inv; eauto.
      apply TyTStar.
      eapply trans_wf; eauto.

    (* Var *)
    (*

Counter example

y : * & * , x : y |- x : y ~~> x

y : * & * , x : y ~~> y : * x * , x : opt (fst y)

y : * & *, x : y |- y : * ~~> opt (snd y)

But

y : * x * , x : opt (fst y) |/- x : opt (snd y)


     *)
    - apply TyTVar.
      lets : trans_wf Ctx; auto.
      lets : ctx_trans Ctx H0 TransB; auto.

    (* Lam *)
    - pose (IHb := typing_pi_inv TransB).
      destruct IHb as [a0 IHPi'].
      destruct IHPi' as [b0 IHPi].
      destruct IHPi.
      destruct H2.
      rewrite H1 in *.
      inversion H3 as [L1].
      clear H3.
      apply_fresh TyTLam as x.

      assert (~ In x L1).
      not_in_L x.
      pose (IH := H4 x H3).
      apply H0 with (Gamma' := extend x a0 Gamma') (b := (open b0 (TFVar x))) in IH; auto.
      not_in_L x.
      apply trans_cons; auto.

    (* App *)
    - pose (H1 := typing_wf_from_typing Ty1).
      inversion H1.
      clear H1.

      pose (H2 := typing_pi_inv H).
      destruct H2 as [a0 H22].
      destruct H22 as [b0 H2].
      destruct H2.
      destruct H1.
      inversion H2 as [L1].
      rewrite H0 in *.
      clear H0.
      pose (IHTy1' := IHTy1 _ _ Ctx H).
      pose (IHTy2' := IHTy2 _ _ Ctx H1).
      pick_fresh y.
      assert (~ In y L1).
      not_in_L y.

      assert (~ In y (fv_source B)).
      not_in_L y.

      assert (~ In y (fv b0)).
      not_in_L y.


      pose (IH := H3 y H0).
      pose (StrucB := @type_subst _ _ _ _ _ _ _ _ H5 H4 Ty2 IH TransB).
      rewrite StrucB.
      eapply TyTApp.
      exact IHTy1'.
      exact IHTy2'.

    (* Pi *)
    - pose (typing_star_inv TransB).
      rewrite e in *.
      apply TyTPi with (L := union L (dom Gamma)).
      pose (IH := IHTy _ TStar Ctx).
      apply IH; auto.
      apply Ty2Star.

      pose (HH := regular_typing Ty); destruct HH; auto.

      intros.
      assert (~ In x (dom Gamma)).
      not_in_L x.
      assert (~ In x L).
      not_in_L x.
      pose (IH := H0 x H3 (extend x t1 Gamma') TStar).
      apply IH.
      apply trans_cons; auto.
      apply Ty2Star.
      apply wfs2_cons with (e := t1); auto.


    (* And *)
    - pose (E := typing_star_inv TransB).
      pose (WW := regular_typing Ty1); destruct WW as [WFS _].
      rewrite E in *.
      apply TyTProd.
      pose (H := IHTy1 _ TStar Ctx).
      apply H.
      apply Ty2Star; auto.
      pose (H := IHTy2 _ TStar Ctx).
      apply H.
      apply Ty2Star; auto.


    (* cast down *)
    - lets [bb TT] : typing_wf_from_typing Ty1.
      lets : IHTy1 Ctx TT.
      eapply TyTCastDown; eauto.


  (*

Counter example

... |- x : Int,,Bool ~> x   Int,,Bool ~~> Int
------------------------------------
x : Int,,Bool |- castdn x : Int ~> castdn x

... |- Int : * ~~> Int

... | Int,,Bool : * ~~> Bool

By induction

[...] |- x : Bool

But

[...] | castdn x : ?


Seems we need disjointness and uniqueness


   *)

      apply (red_preserve H TT TransB).

    (* cast up *)
    - lets [cc TT] : typing_wf_from_typing Ty1.
      lets : IHTy1 Ctx TT.
      eapply TyTCastUp; eauto.
      apply (red_preserve H TransB TT).



    (* Merge 1 *)
    - pose (IHTy _ _ Ctx TransB); auto.

    (* Merge 2 *)
    - pose (IHTy _ _ Ctx TransB); auto.

    - pose (typing_and_inv TransB).
      destruct e as [a0 ee].
      destruct ee as [b0 e].
      destruct e.
      destruct H0.
      rewrite H in *; clear H.
      pose (IHTy1 _ _ Ctx H0).
      pose (IHTy2 _ _ Ctx H1).
      apply TyTPair; auto.

    (* Inter 1 *)
    - apply typing_wf_from_typing in Ty.
      destruct Ty as [e' Ty1].

      pose (Ty := typing_and_inv Ty1).
      destruct Ty.
      destruct H.
      destruct H.
      destruct H0.

      rewrite H in Ty1.

      pose (Ty2 := IHTy _ _ Ctx Ty1).

      pose (Ty3 := elab_unique TransB H0).
      rewrite Ty3.

      eapply pair_inverse.
      exact Ty2.

    (* Inter 2 *)
    - apply typing_wf_from_typing in Ty.
      destruct Ty as [e' Ty1].

      pose (Ty := typing_and_inv Ty1).
      destruct Ty.
      destruct H.
      destruct H.
      destruct H0.

      rewrite H in Ty1.

      pose (Ty2 := IHTy _ _ Ctx Ty1).

      pose (Ty3 := elab_unique TransB H1).
      rewrite Ty3.

      eapply pair_inverse.
      exact Ty2.
  Qed.
