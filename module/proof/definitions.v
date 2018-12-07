Set Implicit Arguments.
Require Import LibLN.


(* ********************************************************************** *)
(** ** Syntax *)


(* Source language *)

Inductive DExp :=
| DStar : DExp
| DBVar : nat -> DExp
| DFVar : var -> DExp
| DLam : DExp -> DExp
| DApp : DExp -> DExp -> DExp
| DCastdn : DExp -> DExp
| DCastup : DExp -> DExp
| DPi : DExp -> DExp -> DExp
| DAnd : DExp -> DExp -> DExp
| DMerge : DExp -> DExp -> DExp
| DAnn : DExp -> DExp -> DExp.    (* Only needed for algorithmic version *)

Hint Constructors DExp.


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



(* ********************************************************************** *)


(* ********************************************************************** *)
(** ** Infrastrcuture *)


Fixpoint open_rec_source (k : nat) (u : DExp) (t : DExp) {struct t} : DExp :=
  match t with
  | DStar =>  DStar
  | DBVar i => If k = i then u else (DBVar i)
  | DFVar x => DFVar x
  | DLam t1 => DLam (open_rec_source (S k) u t1)
  | DApp t1 t2 => DApp (open_rec_source k u t1) (open_rec_source k u t2)
  | DCastdn t => DCastdn (open_rec_source k u t)
  | DCastup t => DCastup (open_rec_source k u t)
  | DPi t1 t2 => DPi (open_rec_source k u t1) (open_rec_source (S k) u t2)
  | DAnd t1 t2 => DAnd (open_rec_source k u t1) (open_rec_source k u t2)
  | DMerge t1 t2 => DMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | DAnn t1 t2 => DAnn (open_rec_source k u t1) (open_rec_source k u t2)
  end.

Definition open_source t u := open_rec_source 0 u t.

Notation "{ k ~> u } t" := (open_rec_source k u t) (at level 67).
Notation "t ^^ u" := (open_source t u) (at level 67).
Notation "t ^ x" := (open_source t (DFVar x)).


Fixpoint open_rec (k : nat) (u : TExp) (t : TExp) {struct t} : TExp :=
  match t with
  | TStar =>  TStar
  | TBVar i => If k = i then u else (TBVar i)
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

Notation "{ k |~> u } t" := (open_rec k u t) (at level 67).
Notation "t $$ u" := (open t u) (at level 67).
Notation "t $ x" := (open t (TFVar x)) (at level 67).

Fixpoint close_source_rec (k : nat) (z : var) (t : DExp) {struct t} : DExp :=
  match t with
  | DStar => DStar
  | DBVar i => DBVar i
  | DFVar x => If x = z then (DBVar k) else (DFVar x)
  | DLam t1 => DLam (close_source_rec (S k) z t1)
  | DApp t1 t2 => DApp (close_source_rec k z t1) (close_source_rec k z t2)
  | DCastup t => DCastup (close_source_rec k z t)
  | DCastdn t => DCastdn (close_source_rec k z t)
  | DPi t1 t2 => DPi (close_source_rec k z t1) (close_source_rec (S k) z t2)
  | DAnd t1 t2 => DAnd (close_source_rec k z t1) (close_source_rec k z t2)
  | DMerge t1 t2 => DMerge (close_source_rec k z t1) (close_source_rec k z t2)
  | DAnn t1 t2 => DAnn (close_source_rec k z t1) (close_source_rec k z t2)
  end.

Definition close_source z t := close_source_rec 0 z t.


Fixpoint close_var_rec (k : nat) (z : var) (t : TExp) {struct t} : TExp :=
  match t with
  | TStar => TStar
  | TBVar i => TBVar i
  | TFVar x => If x = z then (TBVar k) else (TFVar x)
  | TLam t1 => TLam (close_var_rec (S k) z t1)
  | TApp t1 t2 => TApp (close_var_rec k z t1) (close_var_rec k z t2)
  | TCastup t => TCastup (close_var_rec k z t)
  | TCastdn t => TCastdn (close_var_rec k z t)
  | TPi t1 t2 => TPi (close_var_rec k z t1) (close_var_rec (S k) z t2)
  | TPair t1 t2 => TPair (close_var_rec k z t1) (close_var_rec k z t2)
  | TProd t1 t2 => TProd (close_var_rec k z t1) (close_var_rec k z t2)
  | TFst e => TFst (close_var_rec k z e)
  | TSnd e => TSnd (close_var_rec k z e)
  end.

Definition close_var z t := close_var_rec 0 z t.

(* ********************************************************************** *)
(** ** Local closure *)

Inductive sterm : DExp -> Prop :=
| sterm_star : sterm DStar
| sterm_var : forall x, sterm (DFVar x)
| sterm_lam : forall L t1,
    (forall x, x \notin L -> sterm (t1 ^ x)) ->
    sterm (DLam t1)
| sterm_app : forall t1 t2,
    sterm t1 -> sterm t2 -> sterm (DApp t1 t2)
| sterm_castdn : forall t, sterm t -> sterm (DCastdn t)
| sterm_castup : forall t, sterm t -> sterm (DCastup t)
| sterm_pi : forall L t1 t2,
    sterm t1 ->
    (forall x, x \notin L -> sterm (t2 ^ x)) ->
    sterm (DPi t1 t2)
| sterm_inter : forall t1 t2,
    sterm t1 -> sterm t2 -> sterm (DAnd t1 t2)
| sterm_merge : forall t1 t2,
    sterm t1 -> sterm t2 -> sterm (DMerge t1 t2)
| sterm_ann : forall t1 t2,
    sterm t1 -> sterm t2 -> sterm (DAnn t1 t2).


Hint Constructors sterm.

Definition body_source t :=
  exists L, forall x, x \notin L -> sterm (t ^ x).


Inductive term : TExp -> Prop :=
| term_star : term TStar
| term_var : forall x, term (TFVar x)
| term_lam : forall L t1,
    (forall x, x \notin L -> term (open t1 (TFVar x))) ->
    term (TLam t1)
| term_app : forall t1 t2,
    term t1 -> term t2 -> term (TApp t1 t2)
| term_castdn : forall t, term t -> term (TCastdn t)
| term_castup : forall t, term t -> term (TCastup t)
| term_pi : forall L t1 t2,
    term t1 ->
    (forall x, x \notin L -> term (open t2 (TFVar x))) ->
    term (TPi t1 t2)
| term_prod : forall t1 t2,
    term t1 -> term t2 -> term (TProd t1 t2)
| term_pair : forall t1 t2,
    term t1 -> term t2 -> term (TPair t1 t2)
| term_fst : forall t, term t -> term (TFst t)
| term_snd : forall t, term t -> term (TSnd t).

Hint Constructors term.


Fixpoint erase (d : DExp) : DExp :=
  match d with
  | DStar => DStar
  | DBVar v => DBVar v
  | DFVar n => DFVar n
  | DLam t => DLam (erase t)
  | DApp a b => DApp (erase a) (erase b)
  | DCastdn e => DCastdn (erase e)
  | DCastup e => DCastup (erase e)
  | DPi a b => DPi (erase a) (erase b)
  | DAnd a b => DAnd (erase a) (erase b)
  | DMerge a b => DMerge (erase a) (erase b)
  | DAnn a b => erase a
  end.


(* ********************************************************************** *)
(** ** Semantics *)

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

(* CBN *)
Inductive sred : DExp -> DExp -> Prop :=
| sred_beta : forall t1 t2,
    sterm (DLam t1) -> sterm t2 -> sred (DApp (DLam t1) t2) (t1 ^^ t2)
| sred_app1 : forall t1 t1' t2,
    sterm t2 ->
    sred t1 t1' ->
    sred (DApp t1 t2) (DApp t1' t2)
| sred_castelem : forall t,
    svalue t ->
    sred (DCastdn (DCastup t)) t
| sred_castdn : forall e e',
    sred e e' ->
    sred (DCastdn e) (DCastdn e')
| sred_castup : forall e e',
    sred e e' ->
    sred (DCastup e) (DCastup e')
(* | sred_merge1 : forall e1 e2 e1', *)
(*     sred e1 e1' -> *)
(*     sterm e2 -> *)
(*     sred (DMerge e1 e2) (DMerge e1' e2) *)
(* | sred_merge2 : forall e1 e2 e2', *)
(*     svalue e1 -> *)
(*     sred e2 e2' -> *)
(*     sred (DMerge e1 e2) (DMerge e1 e2') *)
| sred_unmerge1 : forall e1 e2,
    sterm e1 ->
    sterm e2 ->
    sred (DMerge e1 e2) e1
| sred_unmerge2 : forall e1 e2,
    sterm e1 ->
    sterm e2 ->
    sred (DMerge e1 e2) e2.

Hint Constructors sred.

Notation "t ~~> t'" := (sred t t') (at level 68).



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
    term (TLam t1) -> term t2 -> red (TApp (TLam t1) t2) (open t1 t2)
| red_app1 : forall t1 t1' t2,
    term t2 ->
    red t1 t1' ->
    red (TApp t1 t2) (TApp t1' t2)
| red_castelem : forall t,
    value t ->
    red (TCastdn (TCastup t)) t
| red_castdn : forall e e',
    red e e' ->
    red (TCastdn e) (TCastdn e')
| red_castup : forall e e',
    red e e' ->
    red (TCastup e) (TCastup e')
| red_fst1 : forall e e',
    red e e' ->
    red (TFst e) (TFst e')
| red_fst2 : forall e1 e2,
    red (TFst (TPair e1 e2)) e1
| red_snd1 : forall e e',
    red e e' ->
    red (TSnd e) (TSnd e')
| red_snd2 : forall e1 e2,
    red (TSnd (TPair e1 e2)) e2.

Hint Constructors red.

Notation "t --> t'" := (red t t') (at level 68).


(* ********************************************************************** *)
(** ** Environments *)

Definition sctx := env DExp.

Definition ctx := env TExp.


(* ********************************************************************** *)
(** Subtyping relation *)

Inductive ordinary : DExp -> Prop :=
| OrdLam : forall t, ordinary (DLam t)
| OrdVar : forall v, ordinary (DFVar v)
| OrdPi : forall d t, ordinary (DPi d t)
| OrdStar : ordinary DStar
| OrdApp : forall t1 t2, ordinary (DApp t1 t2).

(* Incomplete *)
Inductive sub : list DExp -> list (var * DExp) -> TExp -> DExp -> DExp -> TExp -> Prop :=
| SVar : forall S1 S2 e x, term e -> sub S1 S2 e (DFVar x) (DFVar x) e
| SStar : forall S e, term e -> sub nil S e DStar DStar e
| SPi : forall L A B A' B' e e1 e2 S,
    (forall x, x \notin L ->
          sub nil S (TFVar x) A' A (e1 $ x) /\
          sub nil S (TApp e (e1 $ x)) (B ^ x) (B' ^ x) (e2 $ x)) ->
    sub nil S e (DPi A B) (DPi A' B') (TLam e2)
| SLam: forall L e A B e' T D S,
    (forall x, x \notin L -> sub D ((x, T) :: S) (TCastdn e) (A ^ x) (B ^ x) e') ->
    sub (T :: D) S e (DLam A) (DLam B) (TCastup e')
| SApp: forall T A B e e' D S,
    sub (T :: D) S e A B e' -> sub D S e (DApp A T) (DApp B T) e'
(* | SCastDown: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastdn A) (DCastdn B) e' *)
(* | SCastUp: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastup A) (DCastup B) e' *)
| SL1: forall A C e e' B S, ordinary C ->
    sub nil S (TFst e) A C e' -> sub nil S e (DAnd A B) C e'
| SL2: forall A C e e' B S, ordinary C ->
    sub nil S (TSnd e) B C e' -> sub nil S e (DAnd A B) C e'
| SL3 : forall A B C e e1 e2 S,
          sub nil S e A B e1 -> sub nil S e A C e2 -> sub nil S e A (DAnd B C) (TPair e1 e2).

Hint Constructors ordinary sub.

(* Meta-Coercive subtyping.

Motivation: To solve some of the difficulties when proving facts with transformational
subtyping (i.e. sub), but retaining its advantages over coercive subtyping (namely
avoiding redundant *target* identity functions).

The idea is quite similar to coercive subtyping, but instead of a *target* coercion
function, we generate a meta-coercion (i.e. a function in the meta-language).
The advantage is that no (redundant) target identity functions are generated.

*)

Inductive subM : list DExp -> list (var * DExp) -> DExp -> DExp -> (TExp -> TExp) -> Prop :=
| SVarM : forall S1 S2 x, subM S1 S2 (DFVar x) (DFVar x) (fun e => e)
| SStarM : forall S, subM nil S DStar DStar (fun e => e)
| SPiM : forall L A B A' B' c1 c2 S body,
    (forall x, x \notin L -> subM nil S (B ^ x) (B' ^ x) c2 /\
                       body = fun e => (close_var x ((c2 (TApp e (c1 (TFVar x))))))) ->
    subM nil S A' A c1 ->
    subM nil S (DPi A B) (DPi A' B') (fun e => TLam (body e))
| SLamM : forall L A B c T D S,
    (forall x, x \notin L -> subM D ((x, T) :: S) (A ^ x) (B ^ x) c) ->
    subM (T :: D) S (DLam A) (DLam B) (fun e => (TCastup (c (TCastdn e))))
| SAppM: forall T A B c D S,
    sterm T ->
    subM (T :: D) S A B c -> subM D S (DApp A T) (DApp B T) c
(* | SCastDown: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastdn A) (DCastdn B) e' *)
(* | SCastUp: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastup A) (DCastup B) e' *)
| SAnnoM : forall T A B c D S,
    sterm T ->
    subM D S A B c ->
    subM D S (DAnn A T) (DAnn B T) c
| SL1M: forall A C B c S,
    ordinary C ->
    sterm B ->
    subM nil S A C c -> subM nil S (DAnd A B) C (fun e => c (TFst e))
| SL2M: forall A C c B S,
    ordinary C ->
    sterm A ->
    subM nil S B C c -> subM nil S (DAnd A B) C (fun e => c (TSnd e))
| SL3M : forall A B C c1 c2 S,
    subM nil S A B c1 -> subM nil S A C c2 -> subM nil S A (DAnd B C) (fun e => TPair (c1 e) (c2 e)).

Hint Constructors subM.

Inductive coShape : (TExp -> TExp) -> Prop :=
| CoID : coShape (fun e => e)
| CoPi : forall x c1 c2, coShape c1 -> coShape c2 -> coShape (fun e : TExp => TLam (close_var x (c2 (TApp e (c1 (TFVar x))))))
| CoLam : forall c, coShape c -> coShape (fun e => TCastup (c (TCastdn e)))
| CoL1 : forall c, coShape c -> coShape (fun e => c (TFst e))
| CoL2 : forall c, coShape c -> coShape (fun e => c (TSnd e))
| CoL3 : forall c1 c2, coShape c1 -> coShape c2 -> coShape (fun e => TPair (c1 e) (c2 e)).

Hint Constructors coShape.

Inductive usubM : list DExp -> list (var * DExp) -> DExp -> DExp -> Prop :=
| USVarM : forall S1 S2 x, usubM S1 S2 (DFVar x) (DFVar x)
| USStarM : forall S, usubM nil S DStar DStar
| USPiM : forall L A B A' B' S,
    (forall x, x \notin L ->
          usubM nil S (B ^ x) (B' ^ x)) ->
    usubM nil S A' A ->
    usubM nil S (DPi A B) (DPi A' B')
| USLamM : forall L A B T D S,
    (forall x, x \notin L -> usubM D ((x, T) :: S) (A ^ x) (B ^ x)) ->
    usubM (T :: D) S (DLam A) (DLam B)
| USAppM: forall T A B D S,
    sterm T ->
    usubM (T :: D) S A B -> usubM D S (DApp A T) (DApp B T)
| USAnnoM: forall T A B D S,
    sterm T ->
    usubM D S A B -> usubM D S (DAnn A T) (DAnn B T)
(* | SCastDown: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastdn A) (DCastdn B) e' *)
(* | SCastUp: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastup A) (DCastup B) e' *)
| USL1M: forall A C B S,
    sterm B ->
    usubM nil S A C -> usubM nil S (DAnd A B) C
| USL2M: forall A C B S,
    sterm A ->
    usubM nil S B C -> usubM nil S (DAnd A B) C
| USL3M : forall A B C S,
    usubM nil S A B -> usubM nil S A C -> usubM nil S A (DAnd B C).

Hint Constructors usubM.

(* Customised induction principle *)
Section sub_ind'.

  Variable P : list DExp -> list (var * DExp) -> TExp -> DExp -> DExp -> TExp -> Prop.

  Hypothesis var_case : forall S1 S2 e x, term e -> P S1 S2 e (DFVar x) (DFVar x) e.
  Hypothesis star_case : forall S e, term e -> P nil S e DStar DStar e.
  Hypothesis pi_case : forall L A B A' B' e e1 e2 S,
      (forall x, x \notin L ->
            sub nil S (TFVar x) A' A (e1 $ x) /\
            sub nil S (TApp e (e1 $ x)) (B ^ x) (B' ^ x) (e2 $ x)) ->
      (forall x, x \notin L ->
            P nil S (TFVar x) A' A (e1 $ x) /\
            P nil S (TApp e (e1 $ x)) (B ^ x) (B' ^ x) (e2 $ x)) ->
      P nil S e (DPi A B) (DPi A' B') (TLam e2).
  Hypothesis lam_case : forall L e A B e' T D S,
      (forall x, x \notin L -> sub D ((x, T) :: S) (TCastdn e) (A ^ x) (B ^ x) e') ->
      (forall x, x \notin L -> P D ((x, T) :: S) (TCastdn e) (A ^ x) (B ^ x) e') ->
      P (T :: D) S e (DLam A) (DLam B) (TCastup e').
  Hypothesis app_case : forall T e A B e' D S,
      sub (T :: D) S e A B e' -> P (T :: D) S e A B e' -> P D S e (DApp A T) (DApp B T) e'.
  (* Hypothesis castdn_case : forall (e A B e' : DExp) S, *)
  (*     sub nil S e A B e' -> P nil S e A B e' -> P nil S e (DCastdn A) (DCastdn B) e'. *)
  (* Hypothesis castup_case : forall (e A B e' : DExp) S, *)
  (*     sub nil S e A B e' -> P nil S e A B e' -> P nil S e (DCastup A) (DCastup B) e'. *)
  Hypothesis sl1_case : forall A C e e' B S, ordinary C ->
      sub nil S (TFst e) A C e' -> P nil S (TFst e) A C e' -> P nil S e (DAnd A B) C e'.
  Hypothesis sl2_case : forall A C e e' B S, ordinary C ->
      sub nil S (TSnd e) B C e' -> P nil S (TSnd e) B C e' -> P nil S e (DAnd A B) C e'.
  Hypothesis sl3_case : forall A B C e e1 e2 S,
      sub nil S e A B e1 ->
      P nil S e A B e1 -> sub nil S e A C e2 -> P nil S e A C e2 -> P nil S e A (DAnd B C) (TPair e1 e2).

  Fixpoint sub_ind' (l : list DExp) (l0 : list (var * DExp)) (t : TExp) (d d0 : DExp) (t0 : TExp) (s : sub l l0 t d d0 t0) {struct s} : P l l0 t d d0 t0 :=
    match s in (sub l1 l2 d3 d4 d5 d6) return (P l1 l2 d3 d4 d5 d6) with
    | @SVar S1 S2 e x c => @var_case S1 S2 e x c
    | @SStar S0 e c => @star_case S0 e c
    | @SPi L A B A' B' e e1 e2 S0 f =>
      @pi_case L A B A' B' e e1 e2 S0 f
               (fun x (y : x \notin L) =>
                  match f x y with
                    conj t1 t2 => conj (sub_ind' t1) (sub_ind' t2)
                  end)


    | @SLam L e A B e' T D S0 s0 => @lam_case L e A B e' T D S0 s0
                                             (fun x (y : x \notin L) =>
                                                sub_ind' (s0 x y))
    | @SApp T e A B e' D S0 s0 => app_case s0 (sub_ind' s0)
    (* | @SCastDown e A B e' S0 s0 => @castdn_case e A B e' S0 s0 (sub_ind' s0) *)
    (* | @SCastUp e A B e' S0 s0 => @castup_case e A B e' S0 s0 (sub_ind' s0) *)
    | @SL1 A C e e' B S0 H s0 => @sl1_case A C e e' B S0 H s0 (sub_ind' s0)
    | @SL2 A C e e' B S0 H s0 => @sl2_case A C e e' B S0 H s0 (sub_ind' s0)
    | @SL3 e A B C e1 e2 S0 s0 s1 => @sl3_case e A B C e1 e2 S0 s0 (sub_ind' s0) s1 (sub_ind' s1)
    end.

End sub_ind'.

Section subM_ind'.

  Variable P : list DExp -> list (var * DExp) -> DExp -> DExp -> (TExp -> TExp) -> Prop.
  Hypothesis var_case : forall (S1 : list DExp) (S2 : list (var * DExp)) (x : var), P S1 S2 (DFVar x) (DFVar x) (fun e : TExp => e).
  Hypothesis star_case : forall S : list (var * DExp), P nil S DStar DStar (fun e : TExp => e).
  Hypothesis pi_case : forall (L : fset var) (A B A' B' : DExp) (c1 c2 : TExp -> TExp) (S : list (var * DExp)) (body : TExp -> TExp),
      (forall x : var, x \notin L ->
                  subM nil S (B ^ x) (B' ^ x) c2 /\
                  body = (fun e : TExp => close_var x (c2 (TApp e (c1 (TFVar x)))))) ->
      (forall x : var, x \notin L -> P nil S (B ^ x) (B' ^ x) c2) ->
      subM nil S A' A c1 -> P nil S A' A c1 -> P nil S (DPi A B) (DPi A' B') (fun e : TExp => TLam (body e)).
  Hypothesis lam_case : forall (L : fset var) (A B : DExp) (c : TExp -> TExp) (T : DExp) (D : list DExp) (S : list (var * DExp)),
      (forall x : var, x \notin L -> subM D ((x, T) :: S) (A ^ x) (B ^ x) c) ->
      (forall x : var, x \notin L -> P D ((x, T) :: S) (A ^ x) (B ^ x) c) ->
      P (T :: D) S (DLam A) (DLam B) (fun e : TExp => TCastup (c (TCastdn e))).
  Hypothesis app_case : forall (T A B : DExp) (c : TExp -> TExp) (D : list DExp) (S : list (var * DExp)),
      sterm T -> subM (T :: D) S A B c -> P (T :: D) S A B c -> P D S (DApp A T) (DApp B T) c.
  Hypothesis anno_case : forall (T A B : DExp) (c : TExp -> TExp) (D : list DExp) (S : list (var * DExp)),
      sterm T -> subM D S A B c -> P D S A B c -> P D S (DAnn A T) (DAnn B T) c.
  Hypothesis sl1_case : forall (A C B : DExp) (c : TExp -> TExp) (S : list (var * DExp)),
      ordinary C -> sterm B ->
      subM nil S A C c -> P nil S A C c -> P nil S (DAnd A B) C (fun e : TExp => c (TFst e)).
  Hypothesis sl2_case : forall (A C : DExp) (c : TExp -> TExp) (B : DExp) (S : list (var * DExp)),
      ordinary C -> sterm A ->
      subM nil S B C c -> P nil S B C c -> P nil S (DAnd A B) C (fun e : TExp => c (TSnd e)).
  Hypothesis sl3_case : forall (A B C : DExp) (c1 c2 : TExp -> TExp) (S : list (var * DExp)), 
      subM nil S A B c1 ->
      P nil S A B c1 -> subM nil S A C c2 -> P nil S A C c2 -> P nil S A (DAnd B C) (fun e : TExp => TPair (c1 e) (c2 e)).

  Fixpoint subM_ind' (l : list DExp) (l0 : list (var * DExp)) (d d0 : DExp) (t : TExp -> TExp) (s : subM l l0 d d0 t) {struct s} :
P l l0 d d0 t :=
    match s in (subM l1 l2 d1 d2 t0) return (P l1 l2 d1 d2 t0) with
    | SVarM S1 S2 x => var_case S1 S2 x
    | SStarM S0 => star_case S0
    | @SPiM L A B A' B' c1 c2 S0 body a s0 =>
      @pi_case L A B A' B' c1 c2 S0 body a (fun x y => match a x y with conj t1 _ => subM_ind' t1 end) s0 (subM_ind' s0)
    | @SLamM L A B c T D S0 s0 => @lam_case L A B c T D S0 s0 (fun (x : var) (n : x \notin L) => subM_ind' (s0 x n))
    | @SAppM T A B c D T0 S0 s0 => @app_case T A B c D T0 S0 s0 (subM_ind' s0)
    | @SAnnoM T A B c D T0 S0 s0 => @anno_case T A B c D T0 S0 s0 (subM_ind' s0)
    | @SL1M A C B c S0 T0 H s0 => @sl1_case A C B c S0 T0 H s0 (subM_ind' s0)
    | @SL2M A C c B S0 T0 H s0 => @sl2_case A C c B S0 T0 H s0 (subM_ind' s0)
    | @SL3M A B C c1 c2 S0 s0 s1 => @sl3_case A B C c1 c2 S0 s0 (subM_ind' s0) s1 (subM_ind' s1)
    end.

End subM_ind'.

(* ********************************************************************** *)
(** ** Disjointness *)

Definition hd (dexp : DExp) : nat :=
  match dexp with
  | DStar        => 0
  | DLam t       => 1
  | DPi t1 t2    => 2
  | DApp t1 t2   => 3
  | DMerge t1 t2 => 4
  | DCastdn t    => 5
  | DCastup t    => 6
  | DAnn t1 t2   => 7
  | DAnd t1 t2   => 8
  | DBVar n      => 9
  | DFVar v      => 10
  end.

Definition orthoax (t1 t2 : DExp) : Prop :=
  (hd t1 < 4 /\ hd t2 < 4 /\ not (hd t1 = hd t2)).

Inductive ortho : DExp -> DExp -> Prop :=
  | OAnd1 : forall t1 t2 t3, ortho t1 t3 -> ortho t2 t3 -> ortho (DAnd t1 t2) t3
  | OAnd2 : forall t1 t2 t3, ortho t1 t2 -> ortho t1 t3 -> ortho t1 (DAnd t2 t3)
  | OLam  : forall L t1 t2,
              (forall x, x \notin L -> ortho (t1 ^ x) (t2 ^ x)) ->
              ortho (DLam t1) (DLam t2)
  | OPi : forall L d1 d2 t1 t2,
            (forall x, x \notin L -> ortho (t1 ^ x) (t2 ^ x)) ->
                (* PType (And d1 d2) -> *)
            ortho (DPi d1 t1) (DPi d2 t2)
  | OApp : forall A B T, ortho A B -> ortho (DApp A T) (DApp B T)
  (*
  | OVar : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                       usub A ty ->
                       PType ty ->
                       ortho Gamma (DFVar x) ty
  | OVarSym : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                          usub A ty ->
                          PType ty ->
                          ortho Gamma ty (PFVarT x)
  | OTop1 : forall Gamma t, ortho Gamma Top t
  | OTop2 : forall Gamma t, ortho Gamma t Top *)
  | OAx : forall t1 t2, orthoax t1 t2 -> ortho t1 t2.

Hint Constructors ortho.

(* ********************************************************************** *)
(** ** Typing *)

(* Elaboration typing *)
Inductive elab_typing : sctx -> DExp -> DExp -> TExp -> Prop :=
| Ty3Star : forall Γ,
    wfs3 Γ ->
    elab_typing Γ DStar DStar TStar
| Ty3Var : forall Γ x ty,
    wfs3 Γ ->
    binds x ty Γ ->
    elab_typing Γ (DFVar x) ty (TFVar x)
| Ty3Lam : forall L Γ A B t t1 e,
    elab_typing Γ (DPi A B) DStar e ->
    (forall x, x \notin L ->
          elab_typing (Γ & x ~ A) (t ^ x) (B ^ x) (open t1 (TFVar x))) ->
    elab_typing Γ (DLam t) (DPi A B) (TLam t1)
| Ty3App : forall Γ E1 E2 A B e1 e2,
    elab_typing Γ E1 (DPi A B) e1 ->
    elab_typing Γ E2 A e2 ->
    elab_typing Γ (DApp E1 E2) (B ^^ E2) (TApp e1 e2)
| Ty3Pi : forall L Γ A B t1 t2,
    elab_typing Γ A DStar t1 ->
    (forall x, x \notin L -> elab_typing (Γ & x ~ A) (B ^ x) DStar (open t2 (TFVar x))) ->
    elab_typing Γ (DPi A B) DStar (TPi t1 t2)
| Ty3And : forall Γ A B t1 t2,
    elab_typing Γ A DStar t1 ->
    elab_typing Γ B DStar t2 ->
    elab_typing Γ (DAnd A B) DStar (TProd t1 t2)
| Ty3CastDown : forall Γ A B C a c,
    elab_typing Γ A B a ->
    elab_typing Γ C DStar c -> (* should c be existentially quantified? *)
    B ~~> C ->
    elab_typing Γ (DCastdn A) C (TCastdn a)
| Ty3CastUp : forall Γ A B C a b,
    elab_typing Γ A C a ->
    elab_typing Γ B DStar b ->
    B ~~> C ->
    elab_typing Γ (DCastup A) B (TCastup a)
| Ty3Merge: forall Γ E1 E2 A B e1 e2,
    elab_typing Γ E1 A e1 ->
    elab_typing Γ E2 B e2 ->
    ortho A B ->
    elab_typing Γ (DMerge E1 E2) (DAnd A B) (TPair e1 e2)
| Ty3Sub : forall Γ A B C a a',
    sterm C ->
    term a' ->
    elab_typing Γ A B a ->
    sub nil nil a B C a' ->
    elab_typing Γ A C a'

with wfs3 : sctx -> Prop :=
     | wfs3_nil : wfs3 empty
     | wfs3_cons : forall Γ x U e,
         x # Γ ->
         elab_typing Γ U DStar e ->
         wfs3 (Γ & x ~ U).

Hint Constructors elab_typing wfs3.


Inductive Dir := Inf | Chk.


(* Incomplete *)
Inductive elab_typing_alg : sctx -> DExp -> Dir -> DExp -> TExp -> Prop :=
| ATyStar : forall Γ,
    awfs Γ ->
    elab_typing_alg Γ DStar Inf DStar TStar
| ATyVar : forall Γ x ty,
    awfs Γ ->
    binds x ty Γ ->
    elab_typing_alg Γ (DFVar x) Inf ty (TFVar x)
| ATyPi : forall L Γ A B t1 t2,
    elab_typing_alg Γ A Chk DStar t1 ->
    (forall x, x \notin L -> elab_typing_alg (Γ & x ~ A) (B ^ x) Chk DStar (t2 $ x)) ->
    elab_typing_alg Γ (DPi A B) Inf DStar (TPi t1 t2)
(* The following is mode correct *)
| ATyApp : forall Γ E1 E2 A A' B e1 e2,
    elab_typing_alg Γ E1 Inf (DPi A B) e1 ->
    elab_typing_alg Γ E2 Inf A' e2 ->
    A = A' ->
    elab_typing_alg Γ (DApp E1 E2) Inf (B ^^ E2) (TApp e1 e2)
| ATyAnd : forall Γ A B t1 t2,
    elab_typing_alg Γ A Chk DStar t1 ->
    elab_typing_alg Γ B Chk DStar t2 ->
    ortho A B ->
    elab_typing_alg Γ (DAnd A B) Inf DStar (TProd t1 t2)
| ATyMerge: forall Γ E1 E2 A B e1 e2,
    elab_typing_alg Γ E1 Inf A e1 ->
    elab_typing_alg Γ E2 Inf B e2 ->
    ortho A B ->
    elab_typing_alg Γ (DMerge E1 E2) Inf (DAnd A B) (TPair e1 e2)
| ATyAnn : forall Γ A T e e',
    elab_typing_alg Γ A Chk T e ->
    elab_typing_alg Γ T Chk DStar e' ->
    elab_typing_alg Γ (DAnn A T) Inf T e


(* Checking rules *)
| ATyLam : forall L Γ A B t t1 e,
    elab_typing_alg Γ (DPi A B) Chk DStar e ->
    (forall x, x \notin L ->
          elab_typing_alg (Γ & x ~ A) (t ^ x) Chk (B ^ x) (t1 $ x)) ->
    elab_typing_alg Γ (DLam t) Chk (DPi A B) (TLam t1)
| ATyCastDown : forall Γ A B C a b c,
    elab_typing_alg Γ A Inf B a ->
    elab_typing_alg Γ C Chk DStar c ->
    elab_typing_alg Γ B Chk DStar b ->
    B ~~> C ->
    elab_typing_alg Γ (DCastdn A) Chk C (TCastdn a)
| ATyCastUp : forall Γ A B C a b c,
    elab_typing_alg Γ A Inf B a ->
    elab_typing_alg Γ C Chk DStar c ->
    elab_typing_alg Γ B Chk DStar b ->
    C ~~> B ->
    elab_typing_alg Γ (DCastup A) Chk C (TCastup a)
| ATySub : forall Γ A B C a c,
    sterm C ->
    elab_typing_alg Γ A Inf B a ->
    subM nil nil B C c ->
    elab_typing_alg Γ A Chk C (c a)

with
awfs : sctx -> Prop :=
| awfs_nil : awfs empty
| awfs_cons : forall Γ x U e,
    x # Γ ->
    elab_typing_alg Γ U Chk DStar e ->
    awfs (Γ & x ~ U).

Hint Constructors elab_typing_alg awfs.



(* Target typing *)
Inductive has_type : ctx -> TExp -> TExp -> Prop :=
| TyTStar : forall Ω,
    wft Ω ->
    has_type Ω TStar TStar
| TyTVar : forall Ω x ty,
    wft Ω ->
    binds x ty Ω ->
    has_type Ω (TFVar x) ty
| TyTLam : forall L Ω a b t,
    (forall x, x \notin L -> has_type (Ω & x ~ a) (open t (TFVar x)) (open b (TFVar x))) ->
    has_type Ω (TLam t) (TPi a b)
| TyTApp : forall Ω e1 e2 a b,
    has_type Ω e1 (TPi a b) ->
    has_type Ω e2 a ->
    has_type Ω (TApp e1 e2) (open b e2)
| TyTPi : forall L Ω a b,
    has_type Ω a TStar ->
    (forall x, x \notin L -> has_type (Ω & x ~ a) (open b (TFVar x)) TStar) ->
    has_type Ω (TPi a b) TStar
| TyTCastUp : forall Ω t1 t2 e,
    has_type Ω e t2 ->
    (* really need the following? *)
    red t1 t2 ->
    (* has_type Ω t1 TStar -> *)
    has_type Ω (TCastup e) t1
| TyTCastDown : forall Ω t1 t2 e,
    has_type Ω e t1 ->
    red t1 t2 ->
    has_type Ω (TCastdn e) t2
| TyTProd : forall Ω t1 t2,
    has_type Ω t1 TStar ->
    has_type Ω t2 TStar ->
    has_type Ω (TProd t1 t2) TStar
| TyTPair : forall Ω e1 e2 t1 t2,
    has_type Ω e1 t1 ->
    has_type Ω e2 t2 ->
    has_type Ω (TPair e1 e2) (TProd t1 t2)
| TyTFst : forall Ω e t1 t2,
    has_type Ω e (TProd t1 t2) ->
    has_type Ω (TFst e) t1
| TyTSnd : forall Ω e t1 t2,
    has_type Ω e (TProd t1 t2) ->
    has_type Ω (TSnd e) t2

with wft : ctx -> Prop :=
     | wft_nil : wft empty
     | wft_cons : forall Ω x U,
         x # Ω ->
         has_type Ω U TStar ->
         wft (Ω & x ~ U).

Hint Constructors has_type wft.

Inductive trans_ctx : env DExp -> env TExp -> Prop :=
| trans_nil : trans_ctx empty empty
| trans_cons : forall Γ Ω x T t,
    trans_ctx Γ Ω ->
    elab_typing Γ T DStar t ->
    trans_ctx (Γ & x ~ T) (Ω & x ~ t).

Inductive trans_ctx_alg : env DExp -> env TExp -> Prop :=
| Atrans_nil : trans_ctx_alg empty empty
| Atrans_cons : forall Γ Ω x T t,
    trans_ctx_alg Γ Ω ->
    elab_typing_alg Γ T Chk DStar t ->
    trans_ctx_alg (Γ & x ~ T) (Ω & x ~ t).

Hint Constructors trans_ctx trans_ctx_alg.
