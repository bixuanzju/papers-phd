(***************************************************************************
* WeakCast - Definitions                                                   *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Description of the Language *)

(* ********************************************************************** *)
(** Grammar of pre-terms of the calculus of constructions *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_star : trm
  | trm_app  : trm -> trm -> trm
  | trm_abs  : trm -> trm -> trm
  | trm_prod : trm -> trm -> trm
  | trm_mu   : trm -> trm -> trm
  | trm_castup : trm -> trm -> trm
  | trm_castdn : trm -> trm.

(* ********************************************************************** *)
(** Open operation *)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i     => If k = i then u else (trm_bvar i)
  | trm_fvar x     => trm_fvar x 
  | trm_star       => trm_star
  | trm_app t1 t2  => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1 t2  => trm_abs (open_rec k u t1) (open_rec (S k) u t2) 
  | trm_prod t1 t2 => trm_prod (open_rec k u t1) (open_rec (S k) u t2) 
  | trm_mu t1 t2   => trm_mu (open_rec k u t1) (open_rec (S k) u t2) 
  | trm_castup t1 t2  => trm_castup (open_rec k u t1) (open_rec k u t2)
  | trm_castdn t1  => trm_castdn (open_rec k u t1)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(* ********************************************************************** *)
(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_star :
      term trm_star
  | term_abs : forall L t1 t2,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_abs t1 t2)
  | term_prod : forall L t1 t2,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_prod t1 t2)
  | term_mu : forall L t1 t2,
      term t1 ->
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_mu t1 t2)
  | term_castup : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_castup t1 t2)
  | term_castdn : forall t1,
      term t1 -> 
      term (trm_castdn t1).

(* ********************************************************************** *)
(** Closedness of the body of an abstraction *)

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x). 

(* ********************************************************************** *)
(** Definition of a relation on terms *)

Definition relation := trm -> trm -> Prop.

(* ********************************************************************** *)
(** Definition of the reduction *)

Inductive value : trm -> Prop :=
  | value_star : value trm_star
  | value_lam : forall t e,
      term (trm_abs t e) -> value (trm_abs t e)
  | value_pi : forall t1 t2,
      term (trm_prod t1 t2) -> value (trm_prod t1 t2)
  | value_castup : forall t v,
      term t -> value v -> value (trm_castup t v).

Inductive reduct : trm -> trm -> Prop :=
  | reduct_beta : forall t e1 e2,
      term (trm_abs t e1) ->
      term e2 ->
      reduct (trm_app (trm_abs t e1) e2) (e1 ^^ e2)
  | reduct_app : forall e1 e1' e2,
      term e2 -> reduct e1 e1' ->
      reduct (trm_app e1 e2) (trm_app e1' e2)
  | reduct_mu : forall t e,
      term (trm_mu t e) ->
      reduct (trm_mu t e) (e ^^ trm_mu t e)
  | reduct_castup : forall t e e',
      term t ->
      reduct e e' -> reduct (trm_castup t e) (trm_castup t e')
  | reduct_castdn : forall e e',
      reduct e e' -> reduct (trm_castdn e) (trm_castdn e')
  | reduct_castelim : forall t v,
      term t -> value v ->
      reduct (trm_castdn (trm_castup t v)) v.

Notation "t ~~> t'" := (reduct t t') (at level 67).

(* ********************************************************************** *)
(** Environment for typing *)

Definition env := LibEnv.env trm.

(* ********************************************************************** *)
(** Typing relation for terms and contexts *)

Section Typing.
Implicit Types E : env.

Inductive typing : env -> relation :=
  | typing_star : forall E,
      wf E ->
      typing E trm_star trm_star
  | typing_var : forall E x U,
      wf E ->
      binds x U E ->
      typing E (trm_fvar x) U
 | typing_prod : forall L E U T,
      typing E U trm_star ->
      (forall x, x \notin L ->
        typing (E & x ~ U) (T ^ x) trm_star) -> 
      typing E (trm_prod U T) trm_star
  | typing_abs : forall L E U t T,
      typing E (trm_prod U T) trm_star ->
      (forall x, x \notin L ->
        typing (E & x ~ U) (t ^ x) (T ^ x)) ->
      typing E (trm_abs U t) (trm_prod U T)
  | typing_app : forall E t u T U,
      typing E t (trm_prod U T) ->
      typing E u U ->
      typing E (trm_app t u) (T ^^ u)
  | typing_mu : forall L E t T,
      typing E T trm_star ->
      (forall x, x \notin L ->
        typing (E & x ~ T) (t ^ x) T) ->
      typing E (trm_mu T t) T
  | typing_castup : forall E t T U,
      typing E U trm_star ->
      typing E t T ->
      U ~~> T ->
      typing E (trm_castup U t) U
  | typing_castdn : forall E t T U,
      typing E t T ->
      T ~~> U ->
      typing E (trm_castdn t) U
 
with wf : env -> Prop :=
  | wf_nil : wf empty
  | wf_cons : forall E x U,
     x # E -> 
     typing E U trm_star -> 
     wf (E & x ~ U).

End Typing.

