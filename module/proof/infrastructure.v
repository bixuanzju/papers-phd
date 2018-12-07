Set Implicit Arguments.
Require Import LibLN definitions.
Require Import List.


Hint Constructors elab_typing_alg awfs.
Scheme elab_induct := Induction for elab_typing_alg Sort Prop with wf_induct := Induction for awfs Sort Prop.
Scheme typing_induct := Induction for has_type Sort Prop with wf_induct2 := Induction for wft Sort Prop.



(* ********************************************************************** *)
(** Computing free variables of a term *)

Fixpoint fv_source (e : DExp) : vars :=
  match e with
  | DStar => \{}
  | DBVar _ => \{}
  | DFVar x => \{x}
  | DLam t => fv_source t
  | DApp t1 t2 => (fv_source t1) \u (fv_source t2)
  | DCastdn e => fv_source e
  | DCastup e => fv_source e
  | DPi t1 t2 => (fv_source t1) \u (fv_source t2)
  | DAnd t1 t2 => (fv_source t1) \u (fv_source t2)
  | DMerge t1 t2 => (fv_source t1) \u (fv_source t2)
  | DAnn t1 t2 => (fv_source t1) \u (fv_source t2)
  end.

Fixpoint fv (tExp : TExp) : vars :=
  match tExp with
  | TStar => \{}
  | TBVar _ => \{}
  | TFVar x => \{x}
  | TLam t => fv t
  | TApp t1 t2 => (fv t1) \u (fv t2)
  | TCastdn e => fv e
  | TCastup e => fv e
  | TPi t1 t2 => (fv t1) \u (fv t2)
  | TProd t1 t2 => (fv t1) \u (fv t2)
  | TPair e1 e2 => (fv e1) \u (fv e2)
  | TFst e => fv e
  | TSnd e => fv e
  end.

(* ********************************************************************** *)
(** Substitution for a name *)

Fixpoint subst_source (z : var) (u : DExp) (t : DExp) {struct t} : DExp :=
  match t with
  | DStar => DStar
  | DBVar i => DBVar i
  | DFVar x => If x = z then u else (DFVar x)
  | DLam t => DLam (subst_source z u t)
  | DApp t1 t2 => DApp (subst_source z u t1) (subst_source z u t2)
  | DCastdn t => DCastdn (subst_source z u t)
  | DCastup t => DCastup (subst_source z u t)
  | DPi t1 t2 => DPi (subst_source z u t1) (subst_source z u t2)
  | DAnd t1 t2 => DAnd (subst_source z u t1) (subst_source z u t2)
  | DMerge t1 t2 => DMerge (subst_source z u t1) (subst_source z u t2)
  | DAnn t1 t2 => DAnn (subst_source z u t1) (subst_source z u t2)
  end.

Notation "[ z ~> u ] t" := (subst_source z u t) (at level 68).


Fixpoint subst (z : var) (u : TExp) (t : TExp) {struct t} : TExp :=
  match t with
  | TStar => TStar
  | TBVar i => TBVar i
  | TFVar x => If x = z then u else (TFVar x)
  | TLam t => TLam (subst z u t)
  | TApp t1 t2 => TApp (subst z u t1) (subst z u t2)
  | TCastdn t => TCastdn (subst z u t)
  | TCastup t => TCastup (subst z u t)
  | TPi t1 t2 => TPi (subst z u t1) (subst z u t2)
  | TProd t1 t2 => TProd (subst z u t1) (subst z u t2)
  | TPair t1 t2 => TPair (subst z u t1) (subst z u t2)
  | TFst t => TFst (subst z u t)
  | TSnd t => TSnd (subst z u t)
  end.

Notation "[ z |~> u ] t" := (subst z u t) (at level 68).


Definition contains_terms E :=
  forall x U, binds x U E -> sterm U.


Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun (x : sctx) => dom x) in
  let D := gather_vars_with (fun (x : ctx) => dom x) in
  let E := gather_vars_with (fun x : DExp => fv_source x) in
  let F := gather_vars_with (fun x : TExp => fv x) in
  let G := gather_vars_with (fun (x : sctx) => fold_vars fv_source x) in
  let H := gather_vars_with (fun (x : ctx) => fold_vars fv x) in

  constr:(A \u B \u C \u D \u E \u F \u G \u H).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

Ltac exists_fresh :=
  let L := gather_vars_with (fun x : vars => x) in exists L.



(* ********************************************************************** *)
(** ** Lemmas *)

(* ********************************************************************** *)
(** Properties of substitutions *)

Section SubstProperties.

  Lemma open_rec_term_core :forall e j v i u,
      i <> j ->
      open_rec j v e = open_rec i u (open_rec j v e) -> e = open_rec i u e.
  Proof.
    induction e; introv Neq Equ;
      simpl in *; inversion* Equ; f_equal*.
    case_nat*. case_nat*.
  Qed.


  Lemma open_rec_sterm_core :forall e j v i u,
      i <> j ->
      {j ~> v}e = {i ~> u}({j ~> v}e) -> e = {i ~> u}e.
  Proof.
    induction e; introv Neq Equ;
      simpl in *; inversion* Equ; f_equal*.
    case_nat*. case_nat*.
  Qed.


  Lemma open_rec_term : forall t u,
      term t -> forall k, t = open_rec k u t.
  Proof.
    induction 1; intros; simpl; f_equal*.

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_term_core t1 0 (TFVar x)).

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_term_core t2 0 (TFVar x)).
  Qed.

  Lemma open_rec_sterm : forall t u,
      sterm t -> forall k, t = {k ~> u}t.
  Proof.
    induction 1; intros; simpl; f_equal*.

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_sterm_core t1 0 (DFVar x)).

    unfolds open_source. pick_fresh x.
    apply* (@open_rec_sterm_core t2 0 (DFVar x)).
  Qed.

  (** Substitution for a fresh name is identity. *)

  Lemma subst_fresh_s : forall x t u,
        x \notin fv_source t -> [x ~> u] t = t.
  Proof.
    intros. induction t; simpls; fequals*.
    case_var*.
  Qed.

  Lemma subst_fresh : forall x t u,
      x \notin fv t -> [x |~> u] t = t.
  Proof.
    intros. induction t; simpls; fequals*.
    case_var*.
  Qed.


  (** Substitution distributes on the open operation. *)

  Lemma subst_open_s : forall x u t1 t2,
      sterm u ->
      [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
  Proof.
    intros. unfold open_source. generalize 0.
    induction t1; intros; simpl; f_equal*.
    case_nat*. case_var*. apply* open_rec_sterm.
  Qed.

  Lemma subst_open : forall x u t1 t2,
      term u ->
      subst x u (open t1 t2) = open (subst x u t1) (subst x u t2).
  Proof.
    intros. unfold open. generalize 0.
    induction t1; intros; simpl; f_equal*.
    case_nat*. case_var*. apply* open_rec_term.
  Qed.

  (** Substitution and open_var for distinct names commute. *)

  Lemma subst_open_var_s : forall x y u e,
      y <> x -> sterm u ->
      ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
  Proof.
    introv Neq Wu. rewrite* subst_open_s.
    simpl. case_var*.
  Qed.

  Lemma subst_open_var : forall x y u e,
      y <> x -> term u ->
      open (subst x u e) (TFVar y) = subst x u (open e (TFVar y)).
  Proof.
    introv Neq Wu. rewrite* subst_open.
    simpl. case_var*.
  Qed.


  (** Opening up an abstraction of body t with a term u is the same as opening
      up the abstraction with a fresh name x and then substituting u for x. *)

  Lemma subst_intro_s : forall x t u,
      x \notin (fv_source t) -> sterm u ->
      t ^^ u = [x ~> u](t ^ x).
  Proof.
    introv Fr Wu. rewrite* subst_open_s.
    rewrite* subst_fresh_s. simpl. case_var*.
  Qed.

  Lemma subst_intro : forall x t u,
      x \notin (fv t) -> term u ->
      open t u = subst x u (open t (TFVar x)).
  Proof.
    introv Fr Wu. rewrite* subst_open.
    rewrite* subst_fresh. simpl. case_var*.
  Qed.

End SubstProperties.


(** Terms are stable by substitution *)

Lemma subst_term_s : forall t z u,
    sterm u -> sterm t -> sterm ([z ~> u] t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* sterm_lam as y. rewrite* subst_open_var_s.
  apply_fresh* sterm_pi as y. rewrite* subst_open_var_s.
Qed.

Lemma subst_term : forall t z u,
    term u -> term t -> term ([z |~> u] t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* term_lam as y. rewrite* subst_open_var.
  apply_fresh* term_pi as y. rewrite* subst_open_var.
Qed.



(** Terms are stable by open *)

Lemma open_term_s : forall v u,
    body_source v -> sterm u -> sterm (v ^^ u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@subst_intro_s y). apply* subst_term_s.
Qed.

Hint Resolve subst_term_s open_term_s.


(* ********************************************************************** *)
(** ** Regularity: relations are restricted to terms *)

Lemma svalue_regular : forall e,
    svalue e -> sterm e.
Proof.
  introv TyV; induction* TyV.
Qed.

Hint Extern 1 (sterm ?t) =>
match goal with
| H: svalue t |- _ => apply (svalue_regular H)
end.


Lemma red_regular : forall e1 e2,
    e1 ~~> e2 -> sterm e1 /\ sterm e2.
Proof.
  introv TyR.
  induction* TyR.

  (* beta *)
  split.
  apply* sterm_app.
  inversion H; subst.
  apply* open_term_s.
  unfold body_source.
  exists* L.

Qed.

Hint Extern 1 (sterm ?t) =>
match goal with
| H: sred t _ |- _ => apply (proj1 (red_regular H))
| H: sred _ t |- _ => apply (proj2 (red_regular H))
end.


Ltac cross :=
  rewrite subst_open_var_s; try cross.

Tactic Notation "cross" "*" :=
  cross; autos*.

Lemma regular_subtyping : forall S1 S2 e A B e',
    sub S1 S2 e A B e' -> term e /\ term e'.
Proof.
  induction 1 using sub_ind'; auto_star.
  (* pi *)
  split.
  pick_fresh x.
  forwards* : H0 x.
  destructs H1.
  inversions* H2.

  apply_fresh* term_lam as y.
  forwards* : H0 y.

  pick_fresh x.
  forwards* [Te Te'] : H0 x.
  split.
  inversions* Te.
  apply* term_castup.

  inversions* IHsub.
  splits*.
  inversions* H1.

  inversions* IHsub.
  splits*.
  inversions* H1.
Qed.

Hint Extern 1 (term ?t) => match goal with
  | H: sub _ _ t _ _ _ |- _ => apply (proj1 (regular_subtyping H))
  | H: sub _ _ _ _ _ t |- _ => apply (proj2 (regular_subtyping H))
  end.

Lemma regular_subM : forall S1 S2 A B c,
    subM S1 S2 A B c -> sterm A /\ sterm B.
Proof.
  induction 1 using subM_ind'; auto_star.
  (* pi *)
  - split.
    apply_fresh* sterm_pi as x.
    forwards * : H0 x.

    apply_fresh* sterm_pi as x.
    forwards * : H0 x.

  (* lam *)
  - split.
    apply_fresh* sterm_lam as x.
    forwards * : H0 x.
    apply_fresh* sterm_lam as x.
    forwards * : H0 x.

Qed.

Lemma regular_usubM : forall S1 S2 A B,
    usubM S1 S2 A B -> sterm A /\ sterm B.
Proof.
  induction 1; auto_star.
  (* pi *)
  - split.
    apply_fresh* sterm_pi as x.
    forwards * : H0 x.

    apply_fresh* sterm_pi as x.
    forwards * : H0 x.

  (* lam *)
  - split.
    apply_fresh* sterm_lam as x.
    forwards * : H0 x.
    apply_fresh* sterm_lam as x.
    forwards * : H0 x.

Qed.


Hint Extern 1 (sterm ?t) => match goal with
  | H: sub _ _ t _ _ |- _ => apply (proj1 (regular_subtyping H))
  | H: sub _ _ _ t _ |- _ => apply (proj2 (regular_subtyping H))
  end.



(* ********************************************************************** *)
(** ** Inversion Lemmas for Typing *)

Lemma elab_star_inv : forall Γ Mode b,
    elab_typing_alg Γ DStar Mode DStar b -> b = TStar.
Proof.
  intros.
  destruct Mode.
  inversions* H.

  inversions H.
  inversions H1.
  inversions* H2.
Qed.

Lemma elab_pi_inv : forall Γ A B e Mode,
    elab_typing_alg Γ (DPi A B) Mode DStar e -> exists a b,
      e = TPi a b /\ elab_typing_alg Γ A Chk DStar a /\
      exists L, forall x, x \notin L ->
                elab_typing_alg (Γ & x ~ A) (B ^ x) Chk DStar (b $ x).
Proof.
  intros.
  destruct Mode.
  inversions H.
  exists* t1 t2.

  inversions H.
  inversions H1.
  inversions H2.
  exists* t1 t2.
Qed.

Lemma elab_and_inv : forall Γ A B e Mode,
    elab_typing_alg Γ (DAnd A B) Mode DStar e ->
    exists a b, e = TProd a b /\ elab_typing_alg Γ A Chk DStar a /\ elab_typing_alg Γ B Chk DStar b.
Proof.
  intros.
  destruct Mode.
  inversions* H.

  inversions H.
  inversions H1.
  inversions* H2.
Qed.


(* ********************************************************************** *)

Lemma sub_shape : forall S1 S2 A B c,
    subM S1 S2 A B c -> coShape c.
Proof.
  induction 1 using subM_ind'; auto.
  pick_fresh x.
  forwards* [? ?] : H x. clear H. subst.
  lets* : H0 x.
  pick_fresh x.
  lets* : H0 x.
Qed.

Hint Extern 1 (coShape ?t) =>
match goal with
| H: subM _ _ _ _ t |- _ => apply* sub_shape
end.


(** Open_var with fresh names is an injective operation *)

Lemma open_var_inj : forall x t1 t2,
  x \notin (fv t1) -> x \notin (fv t2) ->
  (t1 $ x = t2 $ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

(** Close var commutes with open with some freshness conditions,
  this is used in the proofs of [close_var_body] and [close_var_open] *)

Lemma close_var_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (fv t1) ->
    {i |~> TFVar y} ({j |~> TFVar z} (close_var_rec j x t1) )
  = {j |~> TFVar z} (close_var_rec j x ({i |~> TFVar y}t1) ).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ].
  case_var*. simpl. case_nat*.
Qed.

(** Close var is the right inverse of open_var *)

Lemma close_var_open : forall x t,
  term t -> t = (close_var x t) $ x.
Proof.
  introv W. unfold close_var, open. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
  let L := gather_vars in match goal with |- _ = ?t =>
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open. rewrite* close_var_rec_open.
Qed.

Lemma close_var_fresh : forall x t,
  x \notin fv (close_var x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple*.
Qed.

Lemma close_var_rec_fv : forall x t i,
    x \notin fv t ->
    close_var_rec i x t = t.
Proof.
  induction t; simpl; intros; try solve [ f_equal* ].
  case_var*.
Qed.

Lemma close_source_rec_fv : forall x t i,
    x \notin fv_source t ->
    close_source_rec i x t = t.
Proof.
  induction t; simpl; intros; try solve [ f_equal* ].
  case_var*.
Qed.


Lemma close_var_fv : forall x y t,
    x <> y ->
    x \notin fv t ->
    x \notin fv (close_var y t).
Proof.
  introv Neq Fr. unfold close_var. generalize 0. gen Neq Fr.
  induction t; intros Neq Fr k; simpls; notin_simpl; auto.

  case_var*.
  simpl.
  apply notin_empty.
Qed.

Lemma close_var_subst : forall x y t a,
    x <> y -> y \notin fv a ->
    [x |~> a] (close_var y t) = close_var y ([x |~> a] t).
Proof.
  introv Neq Fr. unfold close_var. generalize 0. gen Neq Fr.
  induction t; simpl; intros Neq Fr i; fequal~.
  case_var~; simpl.
  case_var~. simpl. case_var~.
  case_var~. rewrite* close_var_rec_fv.
  simpl. case_var*.
Qed.

Lemma close_var_rename : forall y x t,
  y \notin fv t ->
  close_var y ([x |~> TFVar y]t) = close_var x t.
Proof.
  introv Fr. unfold close_var. generalize 0. gen Fr.
  induction t; simpl; intros Fr i; fequals~.
  case_var; simpl; case_var~.
Qed.



Lemma close_open_term : forall a x y,
    term a -> x <> y -> term (close_var x a $ y).
Proof.
  introv Trm. unfold close_var, open. gen x y. generalize 0.
  induction Trm; intros; simpls; f_equal*.

  (* Var *)
  - case_var; simpls*. case_nat*.

  (* Lam *)
  - apply_fresh term_lam as z.
    unfolds open.
    rewrite* close_var_rec_open.

  (* Pi *)
  - apply_fresh* term_pi as z.
    unfolds open.
    rewrite* close_var_rec_open.
Qed.

Lemma coercion_regular : forall c a,
    coShape c -> term a -> term (c a).
Proof.
  introv Shape. gen a. induction Shape; intros; auto.

  (* Pi *)
  - apply_fresh term_lam as x.
    apply* close_open_term.
Qed.

Lemma coercion_fv : forall c x e,
    coShape c ->
    x \notin fv e ->
    x \notin fv (c e).
Proof.
  introv Shape. gen e. induction Shape; intros; simpls*.

  tests : (x = x0).
  apply close_var_fresh.

  apply* close_var_fv.
  apply* IHShape2.
  simpl.
  rewrite notin_union.
  splits*.
  apply* IHShape1.
  simpls*.
Qed.



Lemma regular_typing : forall Γ A Mode B e,
    elab_typing_alg Γ A Mode B e ->
    awfs Γ /\ ok Γ /\ contains_terms Γ /\ sterm A /\ sterm B /\ term e.
Proof.
  apply elab_induct with
    (P0 := fun Γ (_ : awfs Γ) => awfs Γ /\ ok Γ /\ contains_terms Γ);
      unfolds contains_terms; intros; splits*.

  (* pi *)
  apply_fresh* sterm_pi as y.
  forwards * : H0 y.
  apply_fresh* term_pi as y.
  forwards * : H0 y.

  (* app *)
  destructs H.
  destructs H0.
  inverts* H4.
  pick_fresh y.
  assert (y \notin L) by auto.
  rewrite subst_intro_s with (x := y); auto.

  (* lam *)
  apply_fresh sterm_lam as y.
  forwards* : H0 y.
  apply_fresh term_lam as y.
  forwards* : H0 y.

  (* sub *)
  apply* coercion_regular.

  (* wf empty *)
  intros. false* binds_empty_inv.

  (* wf cons *)
  intros.
  destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst*.
Qed.


Lemma ok_from_wf : forall E, awfs E -> ok E.
Proof.
  induction 1. auto. autos* (regular_typing H0).
Qed.

Hint Extern 1 (ok ?E) => match goal with
  | H: awfs E |- _ => apply (ok_from_wf H)
  end.

Hint Extern 1 (awfs ?E) => match goal with
  | H: elab_typing_alg E _ _ _ _ |- _ => apply (proj1 (regular_typing H))
  end.

Hint Extern 1 (sterm ?t) => match goal with
  | H: elab_typing_alg _ t _ _ _ |- _ => apply (proj1 (proj44 (regular_typing H)))
  | H: elab_typing_alg _ _ _ t _ |- _ => apply (proj1 (proj2 (proj44 (regular_typing H))))
  end.

Hint Extern 1 (term ?t) => match goal with
  | H: elab_typing_alg _ _ _ _ t |- _ => apply (proj2 (proj2 (proj44 (regular_typing H))))
  end.


Lemma wf_push_inv : forall E x U,
  awfs (E & x ~ U) -> awfs E /\ sterm U.
Proof.
  introv W. inversions W.
  false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. subst~.
Qed.

Lemma term_from_binds_in_wf : forall x E U,
  awfs E -> binds x U E -> sterm U.
Proof.
  introv W Has. gen E. induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct (wf_push_inv W). binds_push~ Has.
Qed.

Hint Extern 1 (sterm ?t) => match goal with
  H: binds ?x t ?E |- _ => apply (@term_from_binds_in_wf x E)
  end.


Lemma wf_left : forall E F : sctx,
  awfs (E & F) -> awfs E.
Proof.
  intros. induction F using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   inversions H. false (empty_push_inv H1).
   destruct (eq_push_inv H0) as [? [? ?]]. subst~.
Qed.

Lemma fv_open_var : forall y x t,
  x <> y -> x \notin fv_source (t ^ y) -> x \notin fv_source t.
Proof.
  introv Neq. unfold open_source. generalize 0.
  induction t; simpl; intros; try auto_star.
Qed.


Lemma typing_fresh : forall Γ T e x Mode,
  elab_typing_alg Γ T Mode DStar e -> x # Γ -> x \notin fv_source T.
Proof.
  introv Typ.
  induction Typ; simpls; intros; auto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1.
  pick_fresh y. notin_simpl. auto. apply* (@fv_open_var y).
  pick_fresh y. apply* (@fv_open_var y).
Qed.

Lemma notin_fv_from_wf : forall E F x V,
  awfs (E & x ~ V & F) -> x \notin fv_source V.
Proof.
  intros.
  lets W: (wf_left H). inversions W.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]]. subst~.
    (*todo: factorize the above pattern *)
  apply* typing_fresh.
Qed.

Lemma notin_fv_from_binds : forall x y U E,
  awfs E -> binds y U E -> x # E -> x \notin fv_source U.
Proof.
  induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct (wf_push_inv H). binds_push H0.
    inversions H. false* (empty_push_inv H5).
     destruct (eq_push_inv H4) as [? [? ?]]. subst~.
     apply* typing_fresh.
    autos*.
Qed.

Lemma notin_fv_from_binds' : forall E F x V y U,
  awfs (E & x ~ V & F) -> binds y U E -> x \notin fv_source U.
Proof.
  intros. lets W: (wf_left H). inversions keep W.
  false (empty_push_inv H2).
  destruct (eq_push_inv H1) as [? [? ?]]. subst~.
  lets W': (wf_left W). apply* notin_fv_from_binds.
Qed.

Hint Extern 1 (?x \notin fv_source ?V) =>
  match goal with H: awfs (?E & x ~ V & ?F) |- _ =>
    apply (@notin_fv_from_wf E F) end.

Hint Extern 1 (?x \notin fv_source ?U) =>
  match goal with H: awfs (?E & x ~ ?V & ?F), B: binds ?y U ?E |- _ =>
    apply (@notin_fv_from_binds' E F x V y) end.



Lemma typing_weaken : forall G E F Mode e T c,
    elab_typing_alg (E & G) e Mode T c ->
    awfs (E & F & G) ->
    elab_typing_alg (E & F & G) e Mode T c.
Proof.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; eauto.

  (* case: var *)
  apply* ATyVar. apply* binds_weaken.

  (* case: trm_prod *)
  apply_fresh* ATyPi as y. apply_ih_bind* H0.

  (* case: trm_abs *)
  apply_fresh* ATyLam as y.
  forwards TypP: (IHTyp G); auto.
  destruct (elab_pi_inv TypP) as [a [b [? [TyA [L0 TyB]]]]]. subst.
  apply_ih_bind* H0.
Qed.



Lemma trans_dom : forall Γ Ω,
    trans_ctx_alg Γ Ω -> dom Γ = dom Ω.
Proof.
  introv Ctx.
  induction Ctx.
  rewrite dom_empty.
  rewrite dom_empty.
  reflexivity.

  rewrite dom_push.
  rewrite dom_push.
  rewrite IHCtx; auto.
Qed.

(* Lemma sub_subst2 : forall S1 S2 a e e' B C x, *)
(*     term a -> *)
(*     sub S1 S2 e B C e' -> *)
(*     sub S1 S2 ([x |~> a] e) B C ([x |~> a] e'). *)
(* Proof. *)
(*   introv Trm Sub. *)
(*   induction Sub using sub_ind'; simpl; auto. *)

(*   - apply SVar. *)
(*     apply* subst_term. *)

(*   - apply SStar. *)
(*     apply* subst_term. *)

(*   (* Pi *) *)
(*   - apply_fresh* SPi as y. *)
(*     forwards* HH : H0 y. *)
(*     case_var*. *)
(*     rewrite* <- subst_open_var in HH. *)
(*     rewrite* <- subst_open_var in HH. *)

(*   (* Lam *) *)
(*   - apply_fresh* SLam as x. *)

(* Qed. *)

(** Ordinary are stable by substitution *)

Lemma ordinary_subst : forall A C x,
    ordinary A -> ordinary C -> ordinary ([x ~> A] C).
Proof.
  induction 2; simpl; auto.
  case_var*.
Qed.

Lemma orthoax_subst : forall x A B a,
    orthoax A B -> orthoax ([x ~> a] A) ([x ~> a] B).
Proof.
  unfolds orthoax.
  intros.
  destructs H.

  destruct A; simpls; try Omega.omega; try (destruct B; simpls; Omega.omega).
Qed.

Lemma ortho_subst : forall x a A B,
    ortho A B -> sterm a -> ortho ([x ~> a] A) ([x ~> a] B).
Proof.
  introv Ortho. gen a.
  induction Ortho; intros; simpls*.

  apply_fresh* OLam as y.
  rewrite*  subst_open_var_s.
  rewrite*  subst_open_var_s.

  apply_fresh* OPi as y.
  rewrite*  subst_open_var_s.
  rewrite*  subst_open_var_s.

  apply OAx.
  apply* orthoax_subst.
Qed.

Lemma subst_value : forall x u e,
    svalue e ->
    sterm u ->
    svalue ([x ~> u] e).
Proof.
  introv Val.
  induction Val; intros; simpl; auto.

  (* lam *)
  - inverts H.
    apply svalue_lam.
    apply_fresh sterm_lam as x.
    rewrite* subst_open_var_s.


  (* pi *)
  - inverts H.
    apply svalue_pi.
    apply_fresh sterm_pi as x.
    apply* subst_term_s.
    rewrite* subst_open_var_s.

  (* and *)
  - inverts H.
    apply svalue_inter.
    apply* sterm_inter.

Qed.

Lemma subst_sred : forall x A B C,
    B ~~> C ->
    sterm A ->
    [x ~> A] B ~~> [x ~> A] C.
Proof.
  intros. gen x A.
  induction H; intros; simpls*.

  - rewrite* subst_open_s.
    apply* sred_beta.
    pose (subst_term_s x H1 H); auto.


  - apply* sred_castelem.
    apply* subst_value.


Qed.



(* ********************************************************************** *)
(** Utility of subtyping   *)

Fixpoint apps A D : DExp :=
  match D with
  | nil => A
  | T :: TS => apps (DApp A T) TS
  end.

Fixpoint substS (S : list (var * DExp)) (A : DExp) : DExp :=
  match S with
  | nil => A
  | (x, E) :: ES => substS ES ([x ~> E ]A)
  end.

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

Lemma substS_anno : forall S A B,
    substS S (DAnn A B) = DAnn (substS S A) (substS S B).
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

Lemma sterm_substS : forall S B,
    sterm B -> ok S -> contains_terms S -> sterm (substS S B).
Proof.
  induction S; intros; simpls*.

  destruct a.
  rewrite cons_to_push in *.
  apply IHS.
  apply* subst_term_s.
  unfold contains_terms in H1.
  apply* ok_push_inv_ok.
  apply* contains_cons.
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


Lemma substS_apps : forall S B x T,
    [x ~> T] apps B S = apps ([x ~> T] B) (map (subst_source x T) S).
Proof.
  induction S; auto.
  intros.
  simpl.
  rewrite IHS.
  simpl.
  reflexivity.
Qed.

Definition all_terms S := forall e, In e S -> sterm e.

Lemma all_term_rest : forall S e,
    all_terms (e :: S) -> all_terms S.
Proof.
  intros.
  unfolds all_terms.
  intros.
  apply H.
  simpls*.
Qed.


Lemma apps_red : forall S A B,
    all_terms S ->
    A ~~> B -> apps A S ~~> apps B S.
Proof.
  induction S; auto.
  intros.
  lets : all_term_rest H.
  unfold all_terms in H.
  simpls*.
Qed.

Lemma substS_sred : forall S A B,
    ok S ->
    contains_terms S ->
    A ~~> B ->
    substS S A ~~> substS S B.
Proof.
  induction S; auto.
  intros.
  destruct a.
  simpl.
  rewrite cons_to_push in *.
  apply* IHS.
  apply* contains_cons.
  apply* subst_sred.
Qed.
