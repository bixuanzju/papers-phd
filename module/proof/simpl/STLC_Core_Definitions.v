(***************************************************************************
* Safety for Simply Typed Lambda Calculus (CBV) - Definitions              *
* Brian Aydemir & Arthur Chargueraud, July 2007                            *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_int   : typ
  | typ_unit : typ
  | typ_arrow : typ -> typ -> typ
  | typ_prod : typ -> typ -> typ.


(** Grammar of pre-terms. *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : trm -> trm
  | trm_app  : trm -> trm -> trm
  | trm_lit  : nat -> trm
  | trm_unit : trm
  | trm_pair : trm -> trm -> trm
  | trm_proj1 : trm -> trm
  | trm_proj2 : trm -> trm.

(** Opening up abstractions *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => If k = i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_unit      => trm_unit
  | trm_lit n      => trm_lit n
  | trm_abs t1    => trm_abs (open_rec (S k) u t1)
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_pair t1 t2 => trm_pair (open_rec k u t1) (open_rec k u t2)
  | trm_proj1 t => trm_proj1 (open_rec k u t)
  | trm_proj2 t => trm_proj2 (open_rec k u t)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(** Terms are locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (trm_abs t1)
  | term_unit : term (trm_unit)
  | term_lit : forall n, term (trm_lit n)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_proj1 : forall t,
      term t ->
      term (trm_proj1 t)
  | term_proj2 : forall t,
      term t ->
      term (trm_proj2 t)
  | term_pair : forall t1 t2,
      term t1 ->
      term t2 ->
      term (trm_pair t1 t2).


(** Environment is an associative list mapping variables to types. *)

Definition env := LibEnv.env typ.

(** Typing relation *)

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      E |= (trm_fvar x) ~: T
  | typing_unit : forall E,
      ok E ->
      E |= trm_unit ~: typ_unit
  | typing_lit : forall E n,
      ok E ->
      E |= (trm_lit n) ~: typ_int
  | typing_abs : forall L E U T t1,
      (forall x, x \notin L -> 
        (E & x ~ U) |= t1 ^ x ~: T) ->
      E |= (trm_abs t1) ~: (typ_arrow U T)
  | typing_app : forall S T E t1 t2,
      E |= t1 ~: (typ_arrow S T) -> 
      E |= t2 ~: S ->
      E |= (trm_app t1 t2) ~: T
  | typing_pair : forall S T E t1 t2,
      E |= t1 ~: T ->
      E |= t2 ~: S ->
      E |= (trm_pair t1 t2) ~: (typ_prod T S)
  | typing_proj1 : forall E T S t,
      E |= t ~: (typ_prod T S) ->
      E |= (trm_proj1 t) ~: T
  | typing_proj2 : forall E T S t,
      E |= t ~: (typ_prod T S) ->
      E |= (trm_proj2 t) ~: S


where "E |= t ~: T" := (typing E t T).

(** Definition of values (only abstractions are values) *)

Inductive value : trm -> Prop :=
  | value_int : forall n, value (trm_lit n)
  | value_abs : forall t1, 
      term (trm_abs t1) -> value (trm_abs t1)
  | value_unit :
      value (trm_unit)
  | value_pair : forall v1 v2,
     value v1 ->
     value v2 ->
     value (trm_pair v1 v2)
  | value_inj1 : forall v1,
     value v1 ->
     value (trm_proj1 v1)
  | value_inj2 : forall v1,
     value v1 ->
     value (trm_proj2 v1).


Inductive red : trm -> trm -> Prop :=
  | red_beta : forall t1 t2,
      term (trm_abs t1) ->
      value t2 ->
      red (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | red_app_1 : forall t1 t1' t2,
      term t2 ->
      red t1 t1' ->
      red (trm_app t1 t2) (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2',
      value t1 ->
      red t2 t2' ->
      red (trm_app t1 t2) (trm_app t1 t2')
  | red_pair_1 : forall t1 t1' t2,
      red t1 t1' ->
      term t2 ->
      red (trm_pair t1 t2) (trm_pair t1' t2)
  | red_pair_2 : forall t1 t2 t2',
      value t1 ->
      red t2 t2' ->
      red (trm_pair t1 t2) (trm_pair t1 t2')
  | red_inj1_1 : forall t1 t1',
      red t1 t1' ->
      red (trm_proj1 t1) (trm_proj1 t1')
  | red_inj2_1 : forall t1 t1',
      red t1 t1' ->
      red (trm_proj2 t1) (trm_proj2 t1').

Notation "t --> t'" := (red t t') (at level 68).

(** Definition of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

Definition relation := trm -> trm -> Prop.

Inductive star_ (R : relation) : relation :=
  | star_refl : forall t,
      term t ->
      star_ R t t
  | star_trans : forall t2 t1 t3,
      star_ R t1 t2 -> star_ R t2 t3 -> star_ R t1 t3
  | star_step : forall t t',
      R t t' -> star_ R t t'.

Notation "R 'star'" := (star_ R) (at level 69).

Notation "t ->* t'" := (red star t t') (at level 68).
