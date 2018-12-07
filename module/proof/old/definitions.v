Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module ExprDefs
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Definition var : Type := VarTyp.t.

  Module M := MSetWeakList.Make(VarTyp).
  Export M.

  Definition vars := M.t.

  Module EqFacts := BoolEqualityFacts(VarTyp).

  Definition context (A : Type) := list (var * A).

  Definition extend {A} (x : var) (a : A) (c : context A) : context A :=
    ((x,a) :: nil) ++ c.

  (* Functions on contexts *)
  Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
    map (fun p => (fst p, (f (snd p)))) c.

  Fixpoint dom {A} (c : context A) : vars :=
    match c with
    | nil => empty
    | el :: cs => add (fst el) (dom cs)
    end.


  Lemma env_ind : forall {A} (P : context A -> Prop),
      (P nil) ->
      (forall E x v, P E -> P (extend x v E)) ->
      (forall E, P E).
  Proof.
    unfold extend.
    intros.
    induction E; auto.
    simpl in H0.
    destruct a; subst.
    apply H0; auto.
Qed.

  (* Source language *)

  Inductive SExp :=
  | SStar : SExp
  | SBVar : nat -> SExp
  | SFVar : var -> SExp
  | SLam : SExp -> SExp
  | SApp : SExp -> SExp -> SExp
  | SCastdn : SExp -> SExp
  | SCastup : SExp -> SExp
  | SPi : SExp -> SExp -> SExp      (* II x : T . e => SPi T e *)
  | SAnd : SExp -> SExp -> SExp
  | SMerge : SExp -> SExp -> SExp.
  (* | SAnno : SExp -> SExp -> SExp. *)

  Hint Constructors SExp.

  (* Source langauge with dependent intersection types *)

  Inductive DExp :=
  | DStar : DExp
  | DBVar : nat -> DExp
  | DFVar : var -> DExp
  | DLam : DExp -> DExp
  | DApp : DExp -> DExp -> DExp
  | DCastdn : DExp -> DExp
  | DCastup : DExp -> DExp
  | DPi : DExp -> DExp -> DExp      (* II x : T . e => SPi T e *)
  | DAnd : DExp -> DExp -> DExp     (* Dependent intersection {x : A} & B *)
  | DMerge : DExp -> DExp -> DExp.

  Hint Constructors DExp.

  Fixpoint open_rec_source (k : nat) (u : DExp) (t : DExp) {struct t} : DExp :=
    match t with
    | DStar =>  DStar
    | DBVar i => if Nat.eqb k i then u else (DBVar i)
    | DFVar x => DFVar x
    | DLam t1 => DLam (open_rec_source (S k) u t1)
    | DApp t1 t2 => DApp (open_rec_source k u t1) (open_rec_source k u t2)
    | DCastdn t => DCastdn (open_rec_source k u t)
    | DCastup t => DCastup (open_rec_source k u t)
    | DPi t1 t2 => DPi (open_rec_source k u t1) (open_rec_source (S k) u t2)
    | DAnd t1 t2 => DAnd (open_rec_source k u t1) (open_rec_source k u t2)
    | DMerge t1 t2 => DMerge (open_rec_source k u t1) (open_rec_source k u t2)
    end.

  Definition open_source t u := open_rec_source 0 u t.


  Fixpoint close_var_rec (k : nat) (z : var) (t : DExp) {struct t} : DExp :=
    match t with
    | DStar => DStar
    | DBVar i => DBVar i
    | DFVar x => if VarTyp.eqb x z then (DBVar k) else (DFVar x)
    | DLam t1 => DLam (close_var_rec (S k) z t1)
    | DApp t1 t2 => DApp (close_var_rec k z t1) (close_var_rec k z t2)
    | DCastup t => DCastup (close_var_rec k z t)
    | DCastdn t => DCastdn (close_var_rec k z t)
    | DPi t1 t2 => DPi (close_var_rec k z t1) (close_var_rec (S k) z t1)
    | DAnd t1 t2 => DAnd (close_var_rec k z t1) (close_var_rec k z t2)
    | DMerge t1 t2 => DMerge (close_var_rec k z t1) (close_var_rec k z t2)
    end.

  Definition close_var z t := close_var_rec 0 z t.

  (* Target language *)

  Inductive TExp :=
  | TStar : TExp
  | TBVar : nat -> TExp
  | TFVar : var -> TExp
  | TLam : TExp -> TExp
  | TApp : TExp -> TExp -> TExp
  | TCastdn : TExp -> TExp
  | TCastup : TExp -> TExp
  | TPi : TExp -> TExp -> TExp
  | TProd : TExp -> TExp -> TExp
  | TPair : TExp -> TExp -> TExp
  | TFst : TExp -> TExp
  | TSnd : TExp -> TExp.

  Hint Constructors TExp.

  Fixpoint open_rec (k : nat) (u : TExp) (t : TExp) {struct t} : TExp :=
    match t with
    | TStar =>  TStar
    | TBVar i => if Nat.eqb k i then u else (TBVar i)
    | TFVar x => TFVar x
    | TLam t1 => TLam (open_rec (S k) u t1)
    | TApp t1 t2 => TApp (open_rec k u t1) (open_rec k u t2)
    | TCastdn t => TCastdn (open_rec k u t)
    | TCastup t => TCastup (open_rec k u t)
    | TPi t1 t2 => TPi (open_rec k u t1) (open_rec (S k) u t2)
    | TProd t1 t2 => TProd (open_rec k u t1) (open_rec k u t2)
    | TPair t1 t2 => TPair (open_rec k u t1) (open_rec k u t2)
    | TFst t => TFst (open_rec k u t)
    | TSnd t => TSnd (open_rec k u t)
    end.


  Definition open (t : TExp) u := open_rec 0 u t.

  Fixpoint close_rec (k : nat) (z : var) (t : TExp) {struct t} : TExp :=
    match t with
    | TStar => TStar
    | TBVar i => TBVar i
    | TFVar x => if VarTyp.eqb x z then (TBVar k) else (TFVar x)
    | TLam t1 => TLam (close_rec (S k) z t1)
    | TApp t1 t2 => TApp (close_rec k z t1) (close_rec k z t2)
    | TCastup t => TCastup (close_rec k z t)
    | TCastdn t => TCastdn (close_rec k z t)
    | TPi t1 t2 => TPi (close_rec k z t1) (close_rec (S k) z t1)
    | TPair t1 t2 => TPair (close_rec k z t1) (close_rec k z t2)
    | TProd t1 t2 => TProd (close_rec k z t1) (close_rec k z t2)
    | TFst e => TFst (close_rec k z e)
    | TSnd e => TSnd (close_rec k z e)
    end.

  Definition close z t := close_rec 0 z t.

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

  Fixpoint subst_source (z : var) (u : DExp) (t : DExp) {struct t} : DExp :=
    match t with
    | DStar => DStar
    | DBVar i => DBVar i
    | DFVar x => if VarTyp.eqb x z then u else (DFVar x)
    | DLam t => DLam (subst_source z u t)
    | DApp t1 t2 => DApp (subst_source z u t1) (subst_source z u t2)
    | DCastdn t => DCastdn (subst_source z u t)
    | DCastup t => DCastup (subst_source z u t)
    | DPi t1 t2 => DPi (subst_source z u t1) (subst_source z u t2)
    | DAnd t1 t2 => DAnd (subst_source z u t1) (subst_source z u t2)
    | DMerge t1 t2 => DMerge (subst_source z u t1) (subst_source z u t2)
    end.

  Fixpoint subst (z : var) (u : TExp) (t : TExp) {struct t} : TExp :=
    match t with
    | TStar => TStar
    | TBVar i => TBVar i
    | TFVar x => if VarTyp.eqb x z then u else (TFVar x)
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

  Fixpoint fv_source (e : DExp) : vars :=
    match e with
    | DStar => empty
    | DBVar _ => empty
    | DFVar x => singleton x
    | DLam t => fv_source t
    | DApp t1 t2 => union (fv_source t1) (fv_source t2)
    | DCastdn e => fv_source e
    | DCastup e => fv_source e
    | DPi t1 t2 => union (fv_source t1) (fv_source t2)
    | DAnd t1 t2 => union (fv_source t1) (fv_source t2)
    | DMerge t1 t2 => union (fv_source t1) (fv_source t2)
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

  Inductive sterm : DExp -> Prop :=
  | sterm_star : sterm DStar
  | sterm_var : forall x, sterm (DFVar x)
  | sterm_lam : forall L t1,
      (forall x, not (In x L) -> sterm (open_source t1 (DFVar x))) ->
      sterm (DLam t1)
  | sterm_app : forall t1 t2,
      sterm t1 -> sterm t2 -> sterm (DApp t1 t2)
  | sterm_castdn : forall t, sterm t -> sterm (DCastdn t)
  | sterm_castup : forall t, sterm t -> sterm (DCastup t)
  | sterm_pi : forall L t1 t2,
      sterm t1 ->
      (forall x, not (In x L) -> sterm (open_source t2 (DFVar x))) ->
      sterm (DPi t1 t2)
  | sterm_inter : forall t1 t2,
      sterm t1 -> sterm t2 -> sterm (DAnd t1 t2)
  | sterm_merge : forall t1 t2,
      sterm t1 -> sterm t2 -> sterm (DMerge t1 t2).

  Hint Constructors sterm.

  Definition body_source t :=
  exists L, forall x, ~ In x L -> sterm (open_source t (DFVar x)).



  Inductive svalue : DExp -> Prop :=
  | svalue_star : svalue DStar
  | svalue_lam : forall t1,
      sterm (DLam t1) -> svalue (DLam t1)
  | svalue_pi : forall t1 t2,
      sterm (DPi t1 t2) -> svalue (DPi t1 t2)
  | svalue_castup : forall e,
      svalue e -> svalue (DCastup e)
  | svalue_inter : forall t1 t2,
      sterm (DAnd t1 t2) ->
      svalue (DAnd t1 t2)
  | svalue_pair : forall e1 e2,
      svalue e1 -> svalue e2 -> svalue (DMerge e1 e2).

  Hint Constructors svalue.

  Inductive sred : DExp -> DExp -> Prop :=
  | sred_beta : forall t1 t2,
      sterm (DLam t1) -> svalue t2 -> sred (DApp (DLam t1) t2) (open_source t1 t2)
  | sred_app1 : forall t1 t1' t2,
      sterm t2 ->
      sred t1 t1' ->
      sred (DApp t1 t2) (DApp t1' t2)
  | sred_app2 : forall t1 t2 t2',
      svalue t1 ->
      sred t2 t2' ->
      sred (DApp t1 t2) (DApp t1 t2')
  | sred_castelem : forall t,
      svalue t ->
      sred (DCastdn (DCastup t)) t
  | sred_castdn : forall e e',
      sred e e' ->
      sred (DCastdn e) (DCastdn e')
  | sred_castup : forall e e',
      sred e e' ->
      sred (DCastup e) (DCastup e')
  | sred_merge1 : forall e1 e2 e1',
      sred e1 e1' ->
      sterm e2 ->
      sred (DMerge e1 e2) (DMerge e1' e2)
  | sred_merge2 : forall e1 e2 e2',
      svalue e1 ->
      sred e2 e2' ->
      sred (DMerge e1 e2) (DMerge e1 e2')
  | sred_unmerge1 : forall e1 e2,
      sterm e1 ->
      sterm e2 ->
      sred (DMerge e1 e2) e1
  | sred_unmerge2 : forall e1 e2,
      sterm e1 ->
      sterm e2 ->
      sred (DMerge e1 e2) e2.
  (* do we need the following step/split? *)
  (* | sred_split : forall e, *)
  (*     sterm e -> *)
  (*     sred e (DMerge e e). *)



  Hint Constructors sred.

  Notation "t ~~> t'" := (sred t t') (at level 68).

  Definition relation := TExp -> TExp -> Prop.

  (** Definition of the reflexive-transitive closure of a relation *)

  Inductive star_ (R : relation) : relation :=
  | star_refl : forall t,
      term t ->
      star_ R t t
  | star_trans : forall t2 t1 t3,
      star_ R t1 t2 -> star_ R t2 t3 -> star_ R t1 t3
  | star_step : forall t t',
      R t t' -> star_ R t t'.

  Notation "R 'star'" := (star_ R) (at level 69).




  (* Subtyping: wait for Bruno's version *)
  (* Parameter sub : list DExp -> list DExp -> DExp -> DExp -> DExp -> DExp -> Prop. *)




End ExprDefs.
