Require Import definitions.
Require Import subtyping.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module Typing
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.

  Module N := SubTyping VarTyp set.
  Export N.

  (* Free variable *)

  (* Source language *)

  Fixpoint fv_source (e : SExp) : vars :=
    match e with
      | SStar => empty
      | SBVar _ => empty
      | SFVar x => singleton x
      | SLam t => fv_source t
      | SApp t1 t2 => union (fv_source t1) (fv_source t2)
      | SCastdn e => fv_source e
      | SCastup e => fv_source e
      | SPi t1 t2 => union (fv_source t1) (fv_source t2)
      | SAnd t1 t2 => union (fv_source t1) (fv_source t2)
      | SMerge t1 t2 => union (fv_source t1) (fv_source t2)
      | SAnno e t => union (fv_source e) (fv_source t)
    end.

  (* Target language *)
  Fixpoint fv (tExp : TExp) : vars :=
    match tExp with
      | TStar => empty
      | TBVar _ => empty
      | TFVar x => singleton x
      | TLam t => fv t
      | TApp t1 t2 => union (fv t1) (fv t2)
      | TCastdn e => fv e
      | TCastup e => fv e
      | TPi t1 t2 => union (fv t1) (fv t2)
      | TProd t1 t2 => union (fv t1) (fv t2)
      | TPair e1 e2 => union (fv e1) (fv e2)
      | TFst e => fv e
      | TSnd e => fv e
    end.


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
    let C := gather_vars_with (fun (x : context SExp) => dom x) in
    let D := gather_vars_with (fun (x : context TExp) => dom x) in
    let E := gather_vars_with (fun x : SExp => fv_source x) in
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


  (* Opening a term "u" with a term "t" *)

  (* Source language *)

  Fixpoint open_rec_source (k : nat) (u : SExp) (t : SExp) {struct t} : SExp :=
    match t with
      | SStar =>  SStar
      | SBVar i => if Nat.eqb k i then u else (SBVar i)
      | SFVar x => SFVar x
      | SLam t1 => SLam (open_rec_source (S k) u t1)
      | SApp t1 t2 => SApp (open_rec_source k u t1) (open_rec_source k u t2)
      | SCastdn t => SCastdn (open_rec_source k u t)
      | SCastup t => SCastup (open_rec_source k u t)
      | SPi t1 t2 => SPi (open_rec_source k u t1) (open_rec_source k u t2)
      | SAnd t1 t2 => SAnd (open_rec_source k u t1) (open_rec_source k u t2)
      | SMerge t1 t2 => SMerge (open_rec_source k u t1) (open_rec_source k u t2)
      | SAnno e t => SAnno (open_rec_source k u e) (open_rec_source k u t)
    end.

  Definition open_source t u := open_rec_source 0 u t.

  (* Target language *)

  Fixpoint open_rec (k : nat) (u : TExp) (t : TExp) {struct t} : TExp :=
    match t with
      | TStar =>  TStar
      | TBVar i => if Nat.eqb k i then u else (TBVar i)
      | TFVar x => TFVar x
      | TLam t1 => TLam (open_rec (S k) u t1)
      | TApp t1 t2 => TApp (open_rec k u t1) (open_rec k u t2)
      | TCastdn t => TCastdn (open_rec k u t)
      | TCastup t => TCastup (open_rec k u t)
      | TPi t1 t2 => TPi (open_rec k u t1) (open_rec k u t2)
      | TProd t1 t2 => TProd (open_rec k u t1) (open_rec k u t2)
      | TPair t1 t2 => TPair (open_rec k u t1) (open_rec k u t2)
      | TFst t => TFst (open_rec k u t)
      | TSnd t => TSnd (open_rec k u t)
    end.


  Definition open (t : TExp) u := open_rec 0 u t.


  (* Substitution *)

  (* Source language *)

  Fixpoint subst_source (z : var) (u : SExp) (t : SExp) {struct t} : SExp :=
    match t with
      | SStar => SStar
      | SBVar i => SBVar i
      | SFVar x => if VarTyp.eqb x z then u else (SFVar x)
      | SLam t => SLam (subst_source z u t)
      | SApp t1 t2 => SApp (subst_source z u t1) (subst_source z u t1)
      | SCastdn t => SCastdn (subst_source z u t)
      | SCastup t => SCastup (subst_source z u t)
      | SPi t1 t2 => SPi (subst_source z u t1) (subst_source z u t1)
      | SAnd t1 t2 => SAnd (subst_source z u t1) (subst_source z u t1)
      | SMerge t1 t2 => SMerge (subst_source z u t1) (subst_source z u t1)
      | SAnno e t => SAnno (subst_source z u e) (subst_source z u t)
    end.

  (* Target language *)

  Fixpoint subst (z : var) (u : TExp) (t : TExp) {struct t} : TExp :=
    match t with
      | TStar => TStar
      | TBVar i => TBVar i
      | TFVar x => if VarTyp.eqb x z then u else (TFVar x)
      | TLam t => TLam (subst z u t)
      | TApp t1 t2 => TApp (subst z u t1) (subst z u t1)
      | TCastdn t => TCastdn (subst z u t)
      | TCastup t => TCastup (subst z u t)
      | TPi t1 t2 => TPi (subst z u t1) (subst z u t1)
      | TProd t1 t2 => TProd (subst z u t1) (subst z u t1)
      | TPair t1 t2 => TPair (subst z u t1) (subst z u t1)
      | TFst t => TFst (subst z u t)
      | TSnd t => TSnd (subst z u t)
    end.


  (* Functions on contexts *)
  Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
    map (fun p => (fst p, (f (snd p)))) c.

  Inductive ok {A} : context A -> Prop :=
  | Ok_nil : ok nil
  | Ok_push : forall (E : context A) (v : var) (ty : A),
                ok E -> not (In v (dom E)) -> ok (extend v ty E).

  Hint Constructors ok.

  (* Local closure *)

  Inductive term : TExp -> Prop :=
  | term_star : term TStar
  | term_var : forall x, term (TFVar x)
  | term_lam : forall L t1,
                 (forall x, not (In x L) -> term (open t1 (TFVar x))) ->
                 term (TLam t1)
  | term_app : forall t1 t2,
                 term t1 -> term t2 -> term (TApp t1 t2)
  | term_castdn : forall t, term t -> term (TCastdn t)
  | term_castup : forall t, term t -> term (TCastup t)
  | term_pi : forall L t1 t2,
                term t1 ->
                (forall x, not (In x L) -> term (open t2 (TFVar x))) ->
                term (TPi t1 t2)
  | term_prod : forall t1 t2,
                  term t1 -> term t2 -> term (TProd t1 t2)
  | term_pair : forall t1 t2,
                  term t1 -> term t2 -> term (TPair t1 t2)
  | term_fst : forall t, term t -> term (TFst t)
  | term_snd : forall t, term t -> term (TSnd t).

  Hint Constructors term.


  (* Semantics *)

  (* Static semantics (call-by-value) *)

  Inductive value : TExp -> Prop :=
  | value_star : value TStar
  | value_lam : forall t1,
                  term (TLam t1) -> value (TLam t1)
  | value_pi : forall t1 t2,
                 term (TPi t1 t2) -> value (TPi t1 t2)
  | value_castup : forall e,
                     value e -> value (TCastup e)
  | value_prod : forall t1 t2, value (TProd t1 t2)
  | value_pair : forall e1 e2,
                   value e1 -> value e2 -> value (TPair e1 e2).

  Hint Constructors value.

  Inductive red : TExp -> TExp -> Prop :=
  | red_beta : forall t1 t2,
                 term (TLam t1) -> value t2 -> red (TApp (TLam t1) t2) (open t1 t2)
  | red_app1 : forall t1 t1' t2,
                 term t2 ->
                 red t1 t1' ->
                 red (TApp t1 t2) (TApp t1' t2)
  | red_app2 : forall t1 t2 t2',
                 value t1 ->
                 red t2 t2' ->
                 red (TApp t1 t2) (TApp t1 t2')
  | red_castelem : forall t,
                     value t ->
                     red (TCastdn (TCastup t)) t
  | red_castdn : forall e e',
                   red e e' ->
                   red (TCastdn e) (TCastdn e')
  | red_castup : forall e e',
                   red e e' ->
                   red (TCastup e) (TCastup e')
  | red_pair1 : forall e1 e2 e1',
                  red e1 e1' ->
                  red (TPair e1 e2) (TPair e1' e2)
  | red_pair2 : forall e1 e2 e2',
                  value e1 ->
                  red e2 e2' ->
                  red (TPair e1 e2) (TPair e1 e2')
  | red_fst1 : forall e e',
                 red e e' ->
                 red (TFst e) (TFst e')
  | red_fst2 : forall e1 e2,
                 value e1 ->
                 value e2 ->
                 red (TFst (TPair e1 e2)) e1
  | red_snd1 : forall e e',
                 red e e' ->
                 red (TSnd e) (TSnd e')
  | red_snd2 : forall e1 e2,
                 value e1 ->
                 value e2 ->
                 red (TSnd (TPair e1 e2)) e2.

  Hint Constructors red.

  Notation "t ~~> t'" := (red t t') (at level 68).


  (* Bidirection type-system (algorithmic) *)

  Inductive Dir := Inf | Chk.

  Inductive has_type_source : context SExp -> SExp -> Dir -> SExp -> TExp -> Prop :=
  (* inference rules *)
  | ATyStar : forall Gamma, ok Gamma -> has_type_source Gamma SStar Inf SStar TStar
  | ATyVar : forall Gamma x ty,
               ok Gamma ->
               List.In (x,ty) Gamma ->
               has_type_source Gamma (SFVar x) Inf ty (TFVar x)
  | ATyAnno : forall Gamma E T e,
                has_type_source Gamma E Chk T e ->
                has_type_source Gamma (SAnno E T) Inf T e
  | ATyApp : forall Gamma E1 E2 A B e1 e2,
               has_type_source Gamma E1 Inf (SPi A B) e1 ->
               has_type_source Gamma E2 Chk A e2 ->
               has_type_source Gamma (SApp E1 E2) Inf (open_source B E2) (TApp e1 e2)
  | ATyPi : forall Gamma L T1 T2 t1 t2,
              has_type_source Gamma T1 Chk SStar t1 ->
              (forall x, not (In x L) -> has_type_source
                                           (extend x T1 Gamma)
                                           (open_source T2 (SFVar x)) Chk SStar (open t2 (TFVar x))) ->
              has_type_source Gamma (SPi T1 T2) Inf SStar (TPi t1 t2)
  | ATyAnd : forall Gamma T1 T2 t1 t2,
               has_type_source Gamma T1 Chk SStar t1 ->
               has_type_source Gamma T2 Chk SStar t2 ->
               has_type_source Gamma (SAnd T1 T2) Inf SStar (TProd t1 t2)
  | ATyMerge : forall Gamma A B C D e1 e2,
                 has_type_source Gamma A Inf C e1 ->
                 has_type_source Gamma B Inf D e2 ->
                 has_type_source Gamma (SMerge A B) Inf (SAnd C D) (TPair e1 e2)

  (* Checking rules *)
  | ATyCastDown : forall Gamma E T1 T2 t1 t2 e,
                    has_type_source Gamma E Inf T1 e ->
                    has_type_source Gamma T1 Chk SStar t1 ->
                    has_type_source Gamma T2 Chk SStar t2 ->
                    t1 ~~> t2 ->
                    has_type_source Gamma (SCastdn E) Chk T2 (TCastdn e)
  | ATyCastUp : forall Gamma E T1 T2 t1 t2 e,
                  has_type_source Gamma E Inf T1 e ->
                  has_type_source Gamma T1 Chk SStar t1 ->
                  has_type_source Gamma T2 Chk SStar t2 ->
                  t2 ~~> t1 ->
                  has_type_source Gamma (SCastup E) Chk T2 (TCastup e)
  | ATyLam : forall L Gamma A B t t1,
               (forall x, not (In x L) -> has_type_source
                                            (extend x A Gamma)
                                            (open_source t (SFVar x)) Chk (open_source B (SFVar x)) (open t1 (TFVar x))) ->
               has_type_source Gamma (SLam t) Chk (SPi A B) (TLam t1)
  | ATySub : forall Gamma E T T' c e,
               has_type_source Gamma E Inf T' e ->
               sub T' T c ->
               has_type_source Gamma E Chk T (TApp c e).

  (* Typing rules for target *)

  Inductive has_type : context TExp -> TExp -> TExp -> Prop :=
  | TyTSTar : forall Gamma, has_type Gamma TStar TStar
  | TyTVar : forall Gamma x ty,
               ok Gamma ->
               List.In (x, ty) Gamma ->
               has_type Gamma (TFVar x) ty
  | TyTLam : forall L Gamma a b t,
               (forall x, not (In x L) -> has_type (extend x a Gamma) (open t (TFVar x)) b) ->
               has_type Gamma (TLam t) (TPi a b)
  | TyTApp : forall Gamma e1 e2 a b,
               has_type Gamma e1 (TPi a b) ->
               has_type Gamma e2 a ->
               has_type Gamma (TApp e1 e2) (open b e2)
  | TyTPi : forall Gamma L a b,
              has_type Gamma a TStar ->
              (forall x, not (In x L) -> has_type (extend x a Gamma) b TStar) ->
              has_type Gamma (TPi a b) TStar
  | TyTCastUp : forall Gamma t1 t2 e,
                  has_type Gamma e t2 ->
                  has_type Gamma t1 TStar ->
                  t1 ~~> t2 ->
                  has_type Gamma (TCastup e) t1
  | TyTCastDown : forall Gamma t1 t2 e,
                    has_type Gamma e t1 ->
                    t1 ~~> t2 ->
                    has_type Gamma (TCastdn e) t2
  | TyTProd : forall Gamma t1 t2,
                has_type Gamma t1 TStar ->
                has_type Gamma t2 TStar ->
                has_type Gamma (TProd t1 t2) TStar
  | TyTPair : forall Gamma e1 e2 t1 t2,
                has_type Gamma e1 t1 ->
                has_type Gamma e2 t2 ->
                has_type Gamma (TPair e1 e2) (TProd t1 t2)
  | TyTFst : forall Gamma e t1 t2,
               has_type Gamma e (TProd t1 t2) ->
               has_type Gamma (TFst e) t1
  | TyTSnd : forall Gamma e t1 t2,
               has_type Gamma e (TProd t1 t2) ->
               has_type Gamma (TSnd e) t2.

End Typing.