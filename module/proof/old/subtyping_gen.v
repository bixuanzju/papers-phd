Require Import definitions.
Require Import subtyping.
Require Import typing.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

(* translation of context, declarative version *)

Module Subtyping_gen
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.

  Module N := SubTyping VarTyp set.
  Export N.

  Module S := Typing VarTyp set.
  Export S.

  Inductive trans_ctx : context SExp -> context TExp -> Prop :=
  | trans_nil : trans_ctx nil nil
  | trans_cons : forall sctx tctx x E T t,
                   trans_ctx sctx tctx ->
                   has_type_source sctx E Inf T t ->
                   trans_ctx ((x,T) :: sctx) ((x,t) :: tctx).

  Lemma trans_ctx_dom : forall Gamma gamma,
                          trans_ctx Gamma gamma -> dom Gamma = dom gamma.
  Proof.
    intros Gamma gamma IH.
    induction IH; auto.
    simpl. rewrite IHIH; reflexivity.
  Qed.


  Lemma trans_ctx_preserve_well_formedness : forall Gamma gamma,
                                               ok Gamma -> trans_ctx Gamma gamma -> ok gamma.
  Proof.
    intros Gamma gamma IOk ITrans.
    induction ITrans; auto.
    inversion IOk; subst.
    apply Ok_push; auto.
    apply trans_ctx_dom in ITrans.
    rewrite <- ITrans.
    assumption.
  Qed.


  Lemma star_chk_star : forall t Gamma, has_type_source Gamma SStar Chk SStar t -> t = (TApp (TLam (TBVar 0)) TStar).

  Proof.

    intros.
    inversion H; subst.

    inversion H0; subst.

    inversion H1; subst.

    reflexivity.


  Qed.

  (* induction on the typing seems to lose some information *)

  Theorem subtyping_gen_fun :
    forall A B c,
      sub A B c ->
      forall Gamma gamma t1 t2 d,
        has_type_source Gamma A d SStar t1 ->
        has_type_source Gamma B d SStar t2 ->
        trans_ctx Gamma gamma ->
        has_type gamma c (TPi t1 t2).
  Proof.
    intros A B c ISub.

    induction ISub.

    (* S-Star *)
    - intros.
      inversion H; subst.
      (* H from T-Star *)
      inversion H0; subst.
      (* H0 from T-Star *)
      apply_fresh TyTLam as x.
      (* \x.x : * -> * *)
      unfold open; simpl.
      apply TyTVar.
      apply Ok_push.
      eapply trans_ctx_preserve_well_formedness.
      exact H2.
      assumption.
      intros IH.
      apply Frx.
      apply union_spec.
      right; assumption.
      apply in_eq.
      (* H from T-Sub *)
      inversion H2; subst.
      inversion H3; subst.
      (* H0 from T-Sub *)
      inversion H0; subst.
      inversion H5; subst.
      inversion H6; subst.
      (* \x. x : (\x.x)* -> (\x.x)* *)
      apply_fresh TyTLam as x.
      unfold open; simpl.
      apply TyTVar.
      apply Ok_push.
      eapply trans_ctx_preserve_well_formedness.
      exact H4.
      assumption.
      intros IH.
      apply Frx.
      apply union_spec.
      right; assumption.
      apply in_eq.

    (* fvar <= fvar *)
    - intros.
      inversion H; subst.
      (* H from T-Var *)
      inversion H0; subst.
      (* \x.x : x -> x *)
      apply_fresh TyTLam as x.
      unfold open; simpl.
      apply TyTVar.
      apply Ok_push.
      eapply trans_ctx_preserve_well_formedness.
      exact H3.
      assumption.
      intros IH.
      apply Fry.
      apply union_spec.
      right; assumption.
      apply in_eq.
      (* H from T-Sub *)
      inversion H2; subst.
      (* H0 from T-Sub *)
      inversion H0; subst.
      inversion H4; subst.
      (* Probably we need
         1. uniqueness of type infer
         2. context has different bindings
         3. coersions are unique
       *)
      admit.

    (* bvar <= bvar *)
    - intros.
      (* same as fvar *)
      admit.

    (* II x : A.B <= II x : A' . B' *)
    - intros.
      admit.

    (* \ x . A <= \ x . B *)
    (* Note: lambda case is trivilly true since it can not typed star *)
    - intros.

      inversion H; subst.
      (* H is T-Sub *)
      inversion H2.

    (* AE <= BE *)
    (* This seems impossible, because the hypothesis requires A to be typed star *)
    - intros.

      admit.

    (* castd A <= castd B *)

    (* This is impossible. The hypothesis requires A to be typed star in some
    mode. Imagine A => star, then e is star, t1 is (\x.x) star, so is t2, then
    don't have reduction relation *)
    - intros.
      (* inversion H; subst. *)
      (* apply star_chk_star in H5; subst. *)
      (* (* what gets reduced to (\x.x) star *) *)
      (* inversion H0; subst. *)
      (* apply star_chk_star in H8; subst. *)

      admit.


    (* castu A <= castu B *)
    - intros.
      inversion H; subst.
      (* H is T-CastUp *)
      apply star_chk_star in H5; subst.
      inversion H7; subst.
      unfold open in H4.
      simpl in H4.
      inversion H4.
      inversion H9.
      inversion H9.
      (* T is T-Sub *)
      admit.

    - intros.
      inversion H; subst.
      (* H is T-Inter *)
      (* we have probelm here, the IH require A and C in same modes, while what
      we have is in differnt modes *)
      inversion H0; subst.
