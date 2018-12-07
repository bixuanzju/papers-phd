(***************************************************************************
* FullCast - Definitions                                                   *
* Based on CoC formalization in LibLN by                                   *
*   Arthur Chargueraud, April 2007                                         *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN CoCMu_Definitions CoCMu_ParaReduction.
Implicit Types x : var.

(* ********************************************************************** *)
(** ** Description of the Language *)

(* ********************************************************************** *)
(** Grammar of pre-terms of the calculus of constructions *)

Inductive src : Set :=
  | src_bvar : nat -> src
  | src_fvar : var -> src
  | src_star : src
  | src_app  : src -> src -> src
  | src_abs  : src -> src -> src
  | src_prod : src -> src -> src
  | src_mu   : src -> src -> src
  | src_castup : src -> src -> src
  | src_castdn : src -> src -> src.

(* ********************************************************************** *)
(** Open operation *)

Fixpoint open_rec (k : nat) (u : src) (t : src) {struct t} : src :=
  match t with
  | src_bvar i     => If k = i then u else (src_bvar i)
  | src_fvar x     => src_fvar x 
  | src_star       => src_star
  | src_app t1 t2  => src_app (open_rec k u t1) (open_rec k u t2)
  | src_abs t1 t2  => src_abs (open_rec k u t1) (open_rec (S k) u t2) 
  | src_prod t1 t2 => src_prod (open_rec k u t1) (open_rec (S k) u t2) 
  | src_mu t1 t2   => src_mu (open_rec k u t1) (open_rec (S k) u t2) 
  | src_castup t1 t2 => src_castup (open_rec k u t1) (open_rec k u t2)
  | src_castdn t1 t2 => src_castdn (open_rec k u t1) (open_rec k u t2)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (src_fvar x)).

(* ********************************************************************** *)
(** Terms as locally closed pre-terms *)

Inductive termsrc : src -> Prop :=
  | termsrc_var : forall x, 
      termsrc (src_fvar x)
  | termsrc_app : forall t1 t2,
      termsrc t1 -> 
      termsrc t2 -> 
      termsrc (src_app t1 t2)
  | termsrc_star :
      termsrc src_star
  | termsrc_abs : forall L t1 t2,
      termsrc t1 ->
      (forall x, x \notin L -> termsrc (t2 ^ x)) -> 
      termsrc (src_abs t1 t2)
  | termsrc_prod : forall L t1 t2,
      termsrc t1 ->
      (forall x, x \notin L -> termsrc (t2 ^ x)) -> 
      termsrc (src_prod t1 t2)
  | termsrc_mu : forall L t1 t2,
      termsrc t1 ->
      (forall x, x \notin L -> termsrc (t2 ^ x)) -> 
      termsrc (src_mu t1 t2)
  | termsrc_castup : forall t1 t2,
      termsrc t1 -> 
      termsrc t2 -> 
      termsrc (src_castup t1 t2)
  | termsrc_castdn : forall t1 t2,
      termsrc t1 ->
      termsrc t2 ->
      termsrc (src_castdn t1 t2).

(* ********************************************************************** *)
(** Closedness of the body of an abstraction *)

Definition bodysrc t :=
  exists L, forall x, x \notin L -> termsrc (t ^ x).

(* ********************************************************************** *)
(** Definition of erasure *)

Fixpoint erasure (s : src) {struct s} : trm :=
  match s with
  | src_bvar i       => trm_bvar i 
  | src_fvar x       => trm_fvar x
  | src_star         => trm_star
  | src_app t1 t2    => trm_app (erasure t1) (erasure t2)
  | src_abs t1 t2    => trm_abs (erasure t1) (erasure t2)
  | src_prod t1 t2   => trm_prod (erasure t1) (erasure t2)
  | src_mu t1 t2     => trm_mu (erasure t1) (erasure t2)
  | src_castup t1 t2 => erasure t2
  | src_castdn t1 t2 => erasure t2
  end.

Notation "| e |" := (erasure e) (at level 37).

Definition erasure_pared t t' :=
  pared (erasure t) (erasure t').

(* ********************************************************************** *)
(** Definition of a relation on terms *)

Definition relsrc := src -> src -> Prop.

(* ********************************************************************** *)
(** Environment for typing *)

Definition env := LibEnv.env src.

(* ********************************************************************** *)
(** typing relation for terms and contexts *)

Section Typing.
Implicit Types E : env.

Inductive typsrc : env -> relsrc :=
  | typsrc_star : forall E,
      wf E ->
      typsrc E src_star src_star
  | typsrc_var : forall E x U,
      wf E ->
      binds x U E ->
      typsrc E (src_fvar x) U
 | typsrc_prod : forall L E U T,
      typsrc E U src_star ->
      (forall x, x \notin L ->
        typsrc (E & x ~ U) (T ^ x) src_star) -> 
      typsrc E (src_prod U T) src_star
  | typsrc_abs : forall L E U t T,
      typsrc E (src_prod U T) src_star ->
      (forall x, x \notin L ->
        typsrc (E & x ~ U) (t ^ x) (T ^ x)) ->
      typsrc E (src_abs U t) (src_prod U T)
  | typsrc_app : forall E t u T U,
      typsrc E t (src_prod U T) ->
      typsrc E u U ->
      typsrc E (src_app t u) (T ^^ u)
  | typsrc_mu : forall L E t T,
      typsrc E T src_star ->
      (forall x, x \notin L ->
        typsrc (E & x ~ T) (t ^ x) T) ->
      typsrc E (src_mu T t) T
  | typsrc_castup : forall E t T U,
      typsrc E U src_star ->
      typsrc E t T ->
      |U| ~p> |T| ->
      typsrc E (src_castup U t) U
  | typsrc_castdn : forall E t T U,
      typsrc E U src_star ->
      typsrc E t T ->
      |T| ~p> |U| ->
      typsrc E (src_castdn U t) U
 
with wf : env -> Prop :=
  | wf_nil : wf empty
  | wf_cons : forall E x U,
     x # E -> 
     typsrc E U src_star -> 
     wf (E & x ~ U).

End Typing.

