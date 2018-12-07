Require Import STLC_Core_Definitions.
Require Import STLC_Core_Infrastructure.

Require Import LibLN.


Set Implicit Arguments.



(* Our calculus: *)

(* Types *)

Inductive PTyp : Type :=
| PInt : PTyp
| Fun : PTyp -> PTyp -> PTyp
| And : PTyp -> PTyp -> PTyp.

Fixpoint ptyp2styp (t : PTyp) : typ :=
  match t with
  | PInt => typ_int
  | Fun t1 t2 => typ_arrow (ptyp2styp t1) (ptyp2styp t2)
  | And t1 t2 => typ_prod (ptyp2styp t1) (ptyp2styp t2)
  end.


(* Subtyping relation *)

Inductive Ordinary : PTyp -> Prop :=
| AInt : Ordinary PInt
| AFun : forall t1 t2, Ordinary (Fun t1 t2).

Hint Constructors Ordinary.

Inductive sub : PTyp -> PTyp -> trm -> Prop :=
| SInt : sub PInt PInt (trm_abs (trm_bvar 0))
| SFun : forall A1 A2 B1 B2 E1 E2,
    sub B1 A1 E1 ->
    sub A2 B2 E2 ->
    sub (Fun A1 A2) (Fun B1 B2)
        (trm_abs (trm_abs (trm_app E2 (trm_app (trm_bvar 1) (trm_app E1 (trm_bvar 0))))))
| SAnd1 : forall A1 A2 A3 E1 E2,
    sub A1 A2 E1 ->
    sub A1 A3 E2 ->
    sub A1 (And A2 A3) (trm_abs (trm_pair (trm_app E1 (trm_bvar 0)) (trm_app E2 (trm_bvar 0))))
| SAnd2 : forall A1 A2 A3 E,
    sub A1 A3 E ->
    Ordinary A3 ->
    sub (And A1 A2) A3 (trm_abs (trm_app E (trm_proj1 (trm_bvar 0))))
| SAnd3 : forall A1 A2 A3 E,
    sub A2 A3 E ->
    Ordinary A3 ->
    sub (And A1 A2) A3 (trm_abs (trm_app E (trm_proj2 (trm_bvar 0)))).
(* | SAnd4 : forall A B C D E F E1 E2, *)
(*     sub A (Fun C D) E1 -> *)
(*     sub B (Fun E F) E2 -> *)
(*     sub (And A B) (Fun (And C E) (And D F)) *)
(*         (trm_abs (trm_abs (trm_pair (trm_app (trm_app E1 (trm_proj1 (trm_bvar 1))) (trm_proj1 (trm_bvar 0))) (trm_app (trm_app E2 (trm_proj2 (trm_bvar 1))) (trm_proj2 (trm_bvar 0)))))). *)

Hint Constructors sub.

Definition Sub A B := exists E, sub A B E.

Definition sint : Sub PInt PInt.
  unfold Sub. exists (trm_abs (trm_bvar 0)). apply SInt.
Defined.

Definition sfun : forall o1 o2 o3 o4,
    Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
  unfold Sub; intros. destruct H as [E1 ?]. destruct H0 as [E2 ?].
  exists (trm_abs (trm_abs (trm_app E2 (trm_app (trm_bvar 1) (trm_app E1 (trm_bvar 0)))))).
  apply* SFun.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
  unfold Sub. intros. destruct H as [E1 ?]. destruct H0 as [E2 ?].
  exists (trm_abs (trm_pair (trm_app E1 (trm_bvar 0)) (trm_app E2 (trm_bvar 0)))).
  apply* SAnd1.
Defined.

Definition sand2_atomic : forall t t1 t2, Sub t1 t -> Ordinary t -> Sub (And t1 t2) t.
  unfold Sub. intros t t1 t2 H H0. destruct H as [E ?].
  exists (trm_abs (trm_app E (trm_proj1 (trm_bvar 0)))).
  apply* SAnd2.
Defined.

Definition sand2 : forall t t1 t2, Sub t1 t -> Sub (And t1 t2) t.
  intro t.
  induction t; intros.
  (* Case PInt *)
  apply* sand2_atomic.
  (* Case Fun *)
  apply* sand2_atomic.
  (* Case And *)
  unfold Sub. unfold Sub in H. destruct H as [E ?]. inverts H.
  assert (Sub (And t0 t3) t1). apply IHt1.
  unfold Sub. exists E1. auto.
  assert (Sub (And t0 t3) t2). apply IHt2.
  unfold Sub. exists E2. auto.
  unfold Sub in H, H0.
  destruct H as [E ?].
  destruct H0 as [E0 ?].
  exists (trm_abs (trm_pair (trm_app E (trm_bvar 0)) (trm_app E0 (trm_bvar 0)))).
  apply* SAnd1.
  inverts H1.
  inverts H1.
Defined.


Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Ordinary t -> Sub (And t1 t2) t.
  unfold Sub. intros t t1 t2 H H0. destruct H as [E ?].
  exists (trm_abs (trm_app E (trm_proj2 (trm_bvar 0)))).
  apply* SAnd3.
Defined.

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And t1 t2) t.
  intro t.
  induction t; intros.
  (* Case PInt *)
  apply* sand3_atomic.
  (* Case Fun *)
  apply* sand3_atomic.
  (* Case And *)
  unfold Sub. unfold Sub in H. destruct H as [E ?]. inverts H.
  assert (Sub (And t0 t3) t1). apply IHt1.
  unfold Sub. exists E1. auto.
  assert (Sub (And t0 t3) t2). apply IHt2.
  unfold Sub. exists E2. auto.
  unfold Sub in H, H0.
  destruct H as [E ?].
  destruct H0 as [E0 ?].
  exists (trm_abs (trm_pair (trm_app E (trm_bvar 0)) (trm_app E0 (trm_bvar 0)))).
  apply* SAnd1.
  inverts H1.
  inverts H1.
Defined.

Hint Resolve sint sfun sand1 sand2 sand3.

Lemma sub_reflex : forall (t1 : PTyp), Sub t1 t1.
Proof.
  induction t1; intros; auto.
Qed.

Lemma sub_trans : forall A B C,
    Sub A B -> Sub B C -> Sub A C.
Proof.
Admitted.

(* Functions on contexts *)

Definition conv_context (ctx : env PTyp) : env typ :=
  map ptyp2styp ctx.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).
Notation "'∥' t '∥'" := (conv_context t) (at level 60).


(* Subtyping rules produce type-correct coercions: Lemma 1 *)
Lemma type_correct_coercions : forall Γ A B E,
    sub A B E ->
    ok Γ ->
    Γ |= E ~: (typ_arrow (|A|) (|B|)).
Proof.
  introv AsubB OK.
  induction AsubB.

  (* Case SInt *)
  - simpl.
    apply_fresh typing_abs.
    unfold open.
    simpl.
    case_if*.
    apply* typing_var.

  (* Case SFun *)
  - apply_fresh typing_abs as x; cbn.
    apply_fresh typing_abs as y; cbn.
    repeat case_if.
    apply typing_app with (S := (| A2 |)).
    rewrite* <- open_rec_term.
    rewrite* <- open_rec_term.
    apply_empty * typing_weaken.
    apply_empty * typing_weaken.
    rewrite* <- open_rec_term.

    apply typing_app with (S := |A1|).
    rewrite* <- open_rec_term.
    apply* typing_var.

    apply typing_app with (S := | B1 |).
    rewrite* <- open_rec_term.
    rewrite* <- open_rec_term.
    apply_empty * typing_weaken.
    apply_empty * typing_weaken.
    rewrite* <- open_rec_term.

    simpl.
    case_if.
    apply* typing_var.

  (* Case SAnd1 *)
  - apply_fresh typing_abs.
    cbn.
    case_if.
    apply typing_pair.
    rewrite* <- open_rec_term.
    apply typing_app with (S := | A1 |).
    apply_empty * typing_weaken.
    apply* typing_var.
    rewrite* <- open_rec_term.
    apply typing_app with (S := | A1 |).
    apply_empty * typing_weaken.
    apply* typing_var.

  (* Case SAnd2 *)
  - apply_fresh typing_abs.
    cbn; case_if.
    apply typing_app with (S := | A1 |).
    rewrite* <- open_rec_term.
    apply_empty * typing_weaken.
    apply typing_proj1 with (S := | A2 |).
    apply* typing_var.

  (* Case SAnd3 *)
  - apply_fresh typing_abs.
    cbn; case_if.
    apply typing_app with (S := | A2 |).
    rewrite* <- open_rec_term.
    apply_empty * typing_weaken.
    apply typing_proj2 with (T := | A1 |).
    apply* typing_var.

  (* Case SAnd4 *)
  (* - apply_fresh typing_abs as x. *)
  (*   cbn; repeat case_if. *)
  (*   apply_fresh typing_abs as y. *)
  (*   cbn; repeat case_if. *)
  (*   repeat rewrite* <- open_rec_term. *)
  (*   simpl in *. *)


  (*   apply typing_pair. *)
  (*   apply typing_app with (S := | C |). *)
  (*   apply typing_app with (S := | A |). *)
  (*   apply_empty * typing_weaken. *)
  (*   apply_empty * typing_weaken. *)
  (*   apply_empty * typing_weaken. *)
  (*   apply typing_proj1 with (S := | B |). *)
  (*   apply* typing_var. *)
  (*   apply typing_proj1 with (S := | E |). *)
  (*   apply* typing_var. *)
  (*   apply typing_app with (S := | E |). *)
  (*   apply typing_app with (S := | B |). *)
  (*   apply_empty * typing_weaken. *)
  (*   apply_empty * typing_weaken. *)
  (*   apply typing_proj2 with (T := | A |). *)
  (*   apply* typing_var. *)
  (*   apply typing_proj2 with (T := | C |). *)
  (*   apply* typing_var. *)
Qed.



(* Disjointness: Implementation *)

Inductive Ortho : PTyp -> PTyp -> Prop :=
| OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
| OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
| OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
| OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
| OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt.

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := not (exists C, Sub A C /\ Sub B C).

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop :=
| WFInt : WFTyp PInt
| WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
| WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2 -> WFTyp (And t1 t2).

Hint Constructors WFTyp.

(* Unique subtype contributor: Lemma 2 *)

Lemma uniquesub : forall A B C,
    OrthoS A B -> Sub (And A B) C -> not (Sub A C /\ Sub B C).
Proof.
  intros. unfold OrthoS in H. unfold not. intros. apply H. exists C. auto.
Qed.

Lemma ortho_sym : forall A B, OrthoS A B -> OrthoS B A.
Proof.
  unfold OrthoS. unfold not. T-sub
  intros. apply H.
  destruct H0. destruct H0.
  exists x.
  split; auto.
Qed.

Lemma sand4_ortho : forall A B C D E F,
    OrthoS A B -> not (Sub A (Fun (And C E) (And D F)) /\ Sub B (Fun E F)) /\ not (Sub A (Fun (And C E) (And D F)) /\ Sub B (Fun C D)).
Proof.
  intros.
  unfold OrthoS in H.
  split.

  intros Contra.
  destruct Contra as [ConA ConB].
  apply H.
  exists (Fun (And C E) F).
  split.
  apply sub_trans with (Fun (And C E) (And D F)); auto.
  assert (Sub (And C E) (And C E)) by apply sub_reflex.
  assert (Sub (And D F) F).
  apply sand3. apply sub_reflex.
  auto.

  apply sub_trans with (Fun E F); auto.
  assert (Sub (And C E) E).
  apply sand3. apply sub_reflex.
  assert (Sub F F) by apply sub_reflex.
  auto.

  intros Contra.
  destruct Contra as [ConA ConB].
  apply H.
  exists (Fun (And C E) D).
  split.
  apply sub_trans with (Fun (And C E) (And D F)); auto.
  assert (Sub (And C E) (And C E)) by apply sub_reflex.
  assert (Sub (And D F) D).
  apply sand2. apply sub_reflex.
  auto.

  apply sub_trans with (Fun C D); auto.
  assert (Sub (And C E) C).
  apply sand2. apply sub_reflex.
  assert (Sub D D) by apply sub_reflex.
  auto.

Qed.

(* Coercive subtyping is coeherent: Lemma 3 *)

Lemma sub_coherent : forall A B C1 C2,
    WFTyp A -> WFTyp B -> sub A B C1 -> sub A B C2 -> C1 = C2.
Proof.
  introv WFA WFB AsubB1. gen C2.
  induction AsubB1; introv AsubB2.

  (* Case: Int <: Int *)
  - inverts* AsubB2.

  (* Case: Fun t1 t2 <: Fun t3 t4 *)
  - inverts AsubB2.
    inverts WFA.
    inverts WFB.
    forwards* : IHAsubB1_1.
    forwards* : IHAsubB1_2.
    subst*.

  (* Case: t <: And t1 t2 *)

  - inverts WFB.
    inverts AsubB2.

    forwards * : IHAsubB1_1 H5.
    forwards * : IHAsubB1_2 H7.
    subst*.

    inverts H0.
    inverts H0.

  (* Case: And t1 t2 <: t (first) *)
  - inverts WFA.
    inverts AsubB2.
    inverts H.

    forwards * : IHAsubB1.
    subst*.

    (* Impossible case by disjointness *)
    unfold OrthoS in H4.
    false.
    apply H4. exists A3. split; [exists* E | exists* E0].


    (* new case : impossible because A1 and A2 are disjoint *)
    (* forwards* [HH ?]: sand4_ortho A1 A2 C D. *)
    (* false. *)
    (* apply HH. *)
    (* split. *)
    (* unfold Sub. exists* E. *)
    (* unfold Sub. exists* E2. *)


  (* Case: And t1 t2 <: t (second) *)
  - inverts WFA.
    inverts AsubB2.
    inverts H.

    unfold OrthoS in H4.
    false*. apply H4. exists A3. split. exists* E0. exists* E.

    forwards * : IHAsubB1.
    subst*.


    (* new case : impossible because A1 and A2 are disjoint *)
    (* lets : ortho_sym H4. *)
    (* forwards* [? HH]: sand4_ortho A2 A1 C D. *)
    (* false. *)
    (* apply HH. *)
    (* split. *)
    (* unfold Sub. exists* E. *)
    (* unfold Sub. exists* E1. *)



  (* New case *)
  (* - inverts WFA. *)
  (*   inverts WFB. *)
  (*   inverts H4. *)
  (*   inverts H5. *)
  (*   inverts AsubB2. *)

  (*   (* Impossible case *) *)
  (*   forwards * [HH ?] : sand4_ortho A B C D. *)
  (*   false. *)
  (*   apply HH. *)
  (*   split. *)
  (*   unfold Sub; exists* E0. *)
  (*   unfold Sub; exists* E2. *)

  (*   (* Impossible case *) *)
  (*   lets : ortho_sym H3. *)
  (*   forwards * [? HH] : sand4_ortho B A C D. *)
  (*   false. *)
  (*   apply HH. *)
  (*   split. *)
  (*   unfold Sub; exists* E0. *)
  (*   unfold Sub; exists* E1. *)

  (*   forwards * : IHAsubB1_1. *)
  (*   forwards * : IHAsubB1_2. *)
  (*   subst*. *)

Qed.


(* Our source language *)
Inductive PExp :=
| PFVar  : var -> PExp
| PBVar  : nat -> PExp
| PLit   : nat -> PExp
| PLam   : PExp -> PExp
| PApp   : PExp -> PExp -> PExp
| PMerge : PExp -> PExp -> PExp
| PAnn   : PExp -> PTyp -> PExp. (* only for the algorithmic version *)

(* Free variables *)

Fixpoint fv_source (pExp : PExp) : vars :=
  match pExp with
  | PFVar v => \{v}
  | PBVar _ => \{}
  | PLit _ => \{}
  | PLam t => fv_source t
  | PApp t1 t2 => (fv_source t1) \u (fv_source t2)
  | PMerge t1 t2 => (fv_source t1) \u (fv_source t2)
  | PAnn t1 A => fv_source t1
  end.


(* Tactics dealing with instantiation of fresh variables, taken from STLC_Tutorial *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun (x : env PTyp) => dom x) in
  let D := gather_vars_with (fun (x : env typ) => dom x) in
  let E := gather_vars_with (fun x : PExp => fv_source x) in
  let F := gather_vars_with (fun (x : trm) => fv x) in
  constr:(A \u B \u C \u D \u E \u F).


Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto_star.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

(* Opening a term "u" with term "t" *)

(** Source language **)
Fixpoint open_rec_source (k : nat) (u : PExp) (t : PExp) {struct t} : PExp  :=
  match t with
  | PBVar i      => if Nat.eqb k i then u else (PBVar i)
  | PFVar x      => PFVar x
  | PLit x       => PLit x
  | PLam t1      => PLam (open_rec_source (S k) u t1)
  | PApp t1 t2   => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | PAnn e t     => PAnn (open_rec_source k u e) t
  end.

Definition open_source t u := open_rec_source 0 u t.



(* Declarative type system *)

Inductive has_type_source : env PTyp -> PExp -> PTyp -> trm -> Prop :=
| TyVar : forall Γ x ty,
    ok Γ ->
    binds x ty Γ ->
    WFTyp ty ->
    has_type_source Γ (PFVar x) ty (trm_fvar x)
| TyLit : forall Γ x, ok Γ -> has_type_source Γ (PLit x) PInt (trm_lit x)
| TyLam : forall L Γ t t' A B,
    (forall x, x \notin L ->
          has_type_source (Γ & x ~ A) (open_source t (PFVar x)) B (t' ^ x)) ->
    WFTyp A ->
    has_type_source Γ (PLam t) (Fun A B) (trm_abs t')
| TyApp : forall Γ A B t1 t2 t1' t2',
    has_type_source Γ t1 (Fun A B) t1' ->
    has_type_source Γ t2 A t2' ->
    has_type_source Γ (PApp t1 t2) B (trm_app t1' t2')
| TyMerge : forall Γ A B t1 t2 t1' t2',
    has_type_source Γ t1 A t1' ->
    has_type_source Γ t2 B t2' ->
    OrthoS A B ->
    has_type_source Γ (PMerge t1 t2) (And A B) (trm_pair t1' t2')
| TySub : forall Γ t A B c t',
    has_type_source Γ t A t' ->
    sub A B c ->
    WFTyp B ->
    has_type_source Γ t B (trm_app c t').

Hint Constructors has_type_source.


Inductive PTerm : PExp -> Prop :=
| PTerm_Var : forall x,
    PTerm (PFVar x)
| PTerm_Lit : forall n,
    PTerm (PLit n)
| PTerm_Lam : forall L t1,
    (forall x, x \notin L -> PTerm (open_source t1 (PFVar x))) ->
    PTerm (PLam t1)
| PTerm_App : forall t1 t2,
    PTerm t1 ->
    PTerm t2 ->
    PTerm (PApp t1 t2)
| PTerm_Merge : forall t1 t2,
    PTerm t1 ->
    PTerm t2 ->
    PTerm (PMerge t1 t2)
| PTerm_Ann : forall e t,
    PTerm e ->
    PTerm (PAnn e t).

Hint Constructors PTerm.

Lemma ok_map : forall Γ, ok Γ -> ok (∥ Γ ∥).
Proof.
  intros.
  induction H.
Admitted.


(*

If r <: t1 -> t2
Then there exists r1 and r2, such that t1 <: r1 and r2 <: t2


 *)


Lemma sub_function : forall t1 t2 r e,
    sub r (Fun t1 t2) e ->
    exists r1 r2 e' e'', sub t1 r1 e' /\ sub r2 t2 e''.
Proof.
  introv Sub.
  gen_eq G: (Fun t1 t2). gen t1 t2.
  induction Sub; introv Eq; inverts Eq.


  (* A1 -> A1 <: t1 -> t2 *)
  - exists* A1 A2 E1 E2.


  (* A1 & A2 <: t1 -> t2 (1) *)
  - apply* IHSub.


  (* A1 & A2 <: t1 -> t2 (2) *)
  - apply* IHSub.


Qed.



(* Type preservation: Theorem 1 *)
Lemma type_preservation : forall Γ e A E,
    has_type_source Γ e A E -> ∥ Γ ∥ |= E ~: | A |.
Proof.
  introv Typ.
  induction Typ.
Admitted.




(* Coherence

Refer to "Inheritance as Implicit Conversion" Lemma 12


Counter example


(3,,'c') : int & char ~~> (3,'c')      ('d',,true) : bool  ~~> true
-------------------------------------------------
(3,,'c') ,, ('d',,true) : (int & char) & bool  ~~> ((3,'c'),true)            (int & char) & bool <: char  ~~>  \x . snd(fst x)
-----------------------------------------------------------------------------------------------------------------  T-sub
(3,,'c') ,, ('d',,true) : char  ~~> 'c'





(3,,'c') : int ~~> 3      ('d',,true) : char & bool  ~~> ('d', true)
-------------------------------------------------
(3,,'c') ,, ('d',,true) : int & (char & bool)  ~~> (3,('d',true))            int & (char & bool) <: char  ~~>  \x . fst(snd x)
----------------------------------------------------------------------------------------------------------------- T-sub
(3,,'c') ,, ('d',,true) : char  ~~> 'd'





 *)


Lemma typ_coherence : forall Γ e A E1 E2,
    has_type_source Γ e A E1 ->
    has_type_source Γ e A E2 ->
    equiv E1 E2.

Proof.
  introv Elab1. gen E2.
  induction Elab1; introv Elab2.

  (* Var *)
  - right.


    inverts* Elab2.

Admitted.
