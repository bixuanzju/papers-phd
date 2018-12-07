Set Implicit Arguments.


Require Import LibLN.


(* ********************************************************************** *)
(** ** Syntax *)


(* Source language *)

(* Inductive SExp := *)
(* | SStar : SExp *)
(* | SBVar : nat -> SExp *)
(* | SFVar : var -> SExp *)
(* | SLam : SExp -> SExp *)
(* | SApp : SExp -> SExp -> SExp *)
(* | SCastdn : SExp -> SExp *)
(* | SCastup : SExp -> SExp *)
(* | SPi : SExp -> SExp -> SExp      (* II x : T . e => SPi T e *) *)
(* | SAnd : SExp -> SExp -> SExp *)
(* | SMerge : SExp -> SExp -> SExp. *)
(* (* | SAnno : SExp -> SExp -> SExp. *) *)

(* Hint Constructors SExp. *)

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

Notation "t $$ u" := (open t u) (at level 67).
Notation "t $ x" := (open t (TFVar x)) (at level 67).


Fixpoint close_rec (k : nat) (z : var) (t : TExp) {struct t} : TExp :=
  match t with
  | TStar => TStar
  | TBVar i => TBVar i
  | TFVar x => If x = z then (TBVar k) else (TFVar x)
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
    sterm t1 -> sterm t2 -> sterm (DMerge t1 t2).

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

Inductive sred : DExp -> DExp -> Prop :=
| sred_beta : forall t1 t2,
    sterm (DLam t1) -> svalue t2 -> sred (DApp (DLam t1) t2) (t1 ^^ t2)
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

Notation "t --> t'" := (red t t') (at level 68).


(* ********************************************************************** *)
(** ** Environments *)

Definition sctx := env DExp.

Definition ctx := env TExp.


(* ********************************************************************** *)
(** Subtyping relation *)

Inductive sub : list DExp -> list (var * DExp) -> DExp -> DExp -> DExp -> DExp -> Prop :=
| SVar : forall E S1 S2 x, sub S1 S2 E (DFVar x) (DFVar x) E (* if S1 != empty, V else N *)
| SStar : forall E S, sub nil S E DStar DStar E
| SPi : forall L A B A' B' E E1 E2 S,
    (forall x, x \notin L ->
          sub nil S (DFVar x) A' A E1 /\
          sub nil S (DApp E E1) (B ^ x) (B' ^ x) (E2 ^ x)) ->
    sub nil S E (DPi A B) (DPi A' B') (DLam E2)
| SLam: forall L E A B E' T D S, (* I believe we need this here: A T ~~> C /\ B T ~~> D *)
    (forall x, x \notin L -> sub D ((x, T) :: S) (DCastdn E) (open_source A (DFVar x)) (open_source B (DFVar x)) E') ->
    sub (T :: D) S E (DLam A) (DLam B) (DCastup E')
| SApp: forall T E A B E' D S,
    sub (T :: D) S E A B E' -> sub D S E (DApp A T) (DApp B T) E'
| SCastDown: forall E A B E' S,
    sub nil S E A B E' -> sub nil S E (DCastdn A) (DCastdn B) E'
| SCastUp: forall E A B E' S,
    sub nil S E A B E' -> sub nil S E (DCastup A) (DCastup B) E'
| SL1: forall E A C E' B S,
    sub nil S E A C E' -> sub nil S E (DAnd A B) C E'
| SL2: forall E A C E' B S,
    sub nil S E B C E' -> sub nil S E (DAnd A B) C E'
| SL3 : forall E A B C E1 E2 S,
    sub nil S E A B E1 -> sub nil S E A C E2 -> sub nil S E A (DAnd B C) (DMerge E1 E2).


(* Customised induction principle *)
Section sub_ind'.

  Variable P : list DExp -> list (var * DExp) -> DExp -> DExp -> DExp -> DExp -> Prop.

  (* Should be free variable? *)
  Hypothesis var_case : forall E S1 S2 x, P S1 S2 E (DFVar x) (DFVar x) E.
  Hypothesis star_case : forall E S, P nil S E DStar DStar E.
  Hypothesis pi_case : forall L A B A' B' E E1 E2 S,
      (forall x, x \notin L ->
            sub nil S (DFVar x) A' A E1 /\
            sub nil S (DApp E E1) (B ^ x) (B' ^ x) (E2 ^ x)) ->
      (forall x, x \notin L ->
            P nil S (DFVar x) A' A E1 /\
            P nil S (DApp E E1) (B ^ x) (B' ^ x) (E2 ^ x)) ->
      P nil S E (DPi A B) (DPi A' B') (DLam E2).
  Hypothesis lam_case : forall L E A B E' T D S,
      (forall x, x \notin L -> sub D ((x, T) :: S) (DCastdn E) (A ^ x) (B ^ x) E') ->
      (forall x, x \notin L -> P D ((x, T) :: S) (DCastdn E) (A ^ x) (B ^ x) E') ->
      P (T :: D) S E (DLam A) (DLam B) (DCastup E').
  Hypothesis app_case : forall T E A B E' D S,
      sub (T :: D) S E A B E' -> P (T :: D) S E A B E' -> P D S E (DApp A T) (DApp B T) E'.
  Hypothesis castdn_case : forall (E A B E' : DExp) S,
      sub nil S E A B E' -> P nil S E A B E' -> P nil S E (DCastdn A) (DCastdn B) E'.
  Hypothesis castup_case : forall (E A B E' : DExp) S,
      sub nil S E A B E' -> P nil S E A B E' -> P nil S E (DCastup A) (DCastup B) E'.
  Hypothesis sl1_case : forall (E A C E' B : DExp) S,
      sub nil S E A C E' -> P nil S E A C E' -> P nil S E (DAnd A B) C E'.
  Hypothesis sl2_case : forall (E A C E' B : DExp) S,
      sub nil S E B C E' -> P nil S E B C E' -> P nil S E (DAnd A B) C E'.
  Hypothesis sl3_case : forall (E A B C E1 E2 : DExp) S,
      sub nil S E A B E1 ->
      P nil S E A B E1 -> sub nil S E A C E2 -> P nil S E A C E2 -> P nil S E A (DAnd B C) (DMerge E1 E2).


  Fixpoint sub_ind' l l0 (d d0 d1 d2 : DExp) (s : sub l l0 d d0 d1 d2) {struct s} : P l l0 d d0 d1 d2 :=
    match s in (sub l1 l2 d3 d4 d5 d6) return (P l1 l2 d3 d4 d5 d6) with
    | SVar E S1 S2 x => var_case E S1 S2 x
    | SStar E S0 => star_case E S0
    | @SPi L A B A' B' E E1 E2 S0 f =>
      @pi_case L A B A' B' E E1 E2 S0 f
               (fun x (y : x \notin L) =>
                  match f x y with
                    conj t1 t2 => conj (sub_ind' t1) (sub_ind' t2)
                  end)


    | @SLam L E A B E' T D S0 s0 => @lam_case L E A B E' T D S0 s0
                                             (fun x (y : x \notin L) =>
                                                sub_ind' (s0 x y))
    | @SApp T E A B E' D S0 s0 => app_case s0 (sub_ind' s0)
    | @SCastDown E A B E' S0 s0 => @castdn_case E A B E' S0 s0 (sub_ind' s0)
    | @SCastUp E A B E' S0 s0 => @castup_case E A B E' S0 s0 (sub_ind' s0)
    | @SL1 E A C E' B S0 s0 => @sl1_case E A C E' B S0 s0 (sub_ind' s0)
    | @SL2 E A C E' B S0 s0 => @sl2_case E A C E' B S0 s0 (sub_ind' s0)
    | @SL3 E A B C E1 E2 S0 s0 s1 => @sl3_case E A B C E1 E2 S0 s0 (sub_ind' s0) s1 (sub_ind' s1)

    end.

End sub_ind'.


(* ********************************************************************** *)
(** ** Typing *)

Section Typing.

  (* First system *)
  Inductive has_type_source : sctx -> DExp -> DExp -> Prop :=
  | TyStar : forall SE, wfs SE -> has_type_source SE DStar DStar
  | TyVar : forall SE x ty,
      wfs SE ->
      binds x ty SE ->
      has_type_source SE (DFVar x) ty
  | TyLam : forall L SE A B t,
      has_type_source SE (DPi A B) DStar ->
      (forall x, x \notin L -> has_type_source (SE & x ~ A) (t ^ x) (B ^ x)) ->
      has_type_source SE (DLam t) (DPi A B)
  | TyApp : forall SE E1 E2 A B,
      has_type_source SE E1 (DPi A B) ->
      has_type_source SE E2 A ->
      has_type_source SE (DApp E1 E2) (B ^^ E2)
  | TyPi : forall SE L A B,
      has_type_source SE A DStar ->
      (forall x, x \notin L -> has_type_source (SE & x ~ A) (B ^ x) DStar) ->
      has_type_source SE (DPi A B) DStar
  | TyAnd : forall SE A B,
      has_type_source SE A DStar ->
      has_type_source SE B DStar ->
      has_type_source SE (DAnd A B) DStar
  | TyCastDown : forall SE A B C,
      (* has_type_source SE B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source SE A B ->
      has_type_source SE C DStar ->
      B ~~> C ->
      has_type_source SE (DCastdn A) C
  | TyCastUp : forall SE A B C,
      (* has_type_source SE B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source SE A C ->
      has_type_source SE B DStar ->
      B ~~> C ->
      has_type_source SE (DCastup A) B
  (* FIXME *)
  | TySub : forall SE A A' B C,
      has_type_source SE A B ->
      (* has_type_source SE B DStar B' -> *)
      (* has_type_source SE C DStar C' -> *)
      sub nil nil A B C A' ->
      has_type_source SE A C
  | TyMerge1: forall SE E1 E2 A,
      has_type_source SE E1 A ->
      sterm E2 ->
      has_type_source SE (DMerge E1 E2) A
  | TyMerge2: forall SE E1 E2 A,
      has_type_source SE E2 A ->
      sterm E1 ->
      has_type_source SE (DMerge E1 E2) A
  | TyInter: forall SE E A1 A2,
      has_type_source SE E A1 ->
      has_type_source SE E A2 ->
      has_type_source SE E (DAnd A1 A2)
  | TyInter1: forall SE E A1 A2,
      has_type_source SE E (DAnd A1 A2) ->
      has_type_source SE E A1
  | TyInter2: forall SE E A1 A2,
      has_type_source SE E (DAnd A1 A2) ->
      has_type_source SE E A2
  with wfs : sctx -> Prop :=
  | wfs_nil : wfs empty
  | wfs_cons : forall SE x U,
      x # SE ->
      has_type_source SE U DStar ->
      wfs (SE & x ~ U).


  Hint Constructors has_type_source wfs.


  (* Second system *)
  Definition opt (t : TExp) :=
    match t with
    | (TFst (TPair e1 e2)) => e1
    | (TSnd (TPair e1 e2)) => e2
    | _ => t
    end.

  Inductive has_type_source2 : sctx -> DExp -> DExp -> TExp -> Prop :=
  | Ty2Star : forall SE,
      wfs2 SE ->
      has_type_source2 SE DStar DStar TStar
  | Ty2Var : forall SE x ty,
      wfs2 SE ->
      binds x ty SE ->
      has_type_source2 SE (DFVar x) ty (TFVar x)
  | Ty2Lam : forall L SE A B t t1 e,
      has_type_source2 SE (DPi A B) DStar e ->
      (forall x, x \notin L ->
            has_type_source2 (SE & x ~ A) (t ^ x) (B ^ x) (open t1 (TFVar x))) ->
      has_type_source2 SE (DLam t) (DPi A B) (TLam t1)
  | Ty2App : forall SE E1 E2 A B e1 e2,
      has_type_source2 SE E1 (DPi A B) e1 ->
      has_type_source2 SE E2 A e2 ->
      has_type_source2 SE (DApp E1 E2) (B ^^ E2) (TApp e1 e2)
  | Ty2Pi : forall L SE A B t1 t2,
      has_type_source2 SE A DStar t1 ->
      (forall x, x \notin L -> has_type_source2 (SE & x ~ A) (B ^ x) DStar (open t2 (TFVar x))) ->
      has_type_source2 SE (DPi A B) DStar (TPi t1 t2)
  | Ty2And : forall SE A B t1 t2,
      has_type_source2 SE A DStar t1 ->
      has_type_source2 SE B DStar t2 ->
      has_type_source2 SE (DAnd A B) DStar (TProd t1 t2)
  | Ty2CastDown : forall SE A B C a c,
      (* has_type_source SE B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source2 SE A B a ->
      has_type_source2 SE C DStar c ->
      B ~~> C ->
      has_type_source2 SE (DCastdn A) C (TCastdn a)
  | Ty2CastUp : forall SE A B C a b,
      (* has_type_source SE B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source2 SE A C a ->
      has_type_source2 SE B DStar b ->
      B ~~> C ->
      has_type_source2 SE (DCastup A) B (TCastup a)
  | Ty2Merge1: forall SE E1 E2 A e,
      has_type_source2 SE E1 A e ->
      sterm E2 ->
      has_type_source2 SE (DMerge E1 E2) A e
  | Ty2Merge2: forall SE E1 E2 A e,
      has_type_source2 SE E2 A e ->
      sterm E1 ->
      has_type_source2 SE (DMerge E1 E2) A e
  | Ty2Inter: forall SE E A1 A2 e1 e2,
      has_type_source2 SE E A1 e1 ->
      has_type_source2 SE E A2 e2 ->
      has_type_source2 SE E (DAnd A1 A2) (TPair e1 e2)
  | Ty2Inter1: forall SE E A1 A2 e,
      has_type_source2 SE E (DAnd A1 A2) e ->
      has_type_source2 SE E A1 (opt (TFst e))
  | Ty2Inter2: forall SE E A1 A2 e,
      has_type_source2 SE E (DAnd A1 A2) e ->
      has_type_source2 SE E A2 (opt (TSnd e))

  with wfs2 : sctx -> Prop :=
       | wfs2_nil : wfs2 empty
       | wfs2_cons : forall E x U e,
           x # E ->
           has_type_source2 E U DStar e ->
           wfs2 (E & x ~ U).

  Hint Constructors has_type_source2 wfs2.


  (* Target typing *)
  Inductive has_type : ctx -> TExp -> TExp -> Prop :=
  | TyTStar : forall E,
      wft E ->
      has_type E TStar TStar
  | TyTVar : forall E x ty,
      wft E ->
      binds x ty E ->
      has_type E (TFVar x) ty
  | TyTLam : forall L E a b t,
      (forall x, x \notin L -> has_type (E & x ~ a) (open t (TFVar x)) (open b (TFVar x))) ->
      has_type E (TLam t) (TPi a b)
  | TyTApp : forall E e1 e2 a b,
      has_type E e1 (TPi a b) ->
      has_type E e2 a ->
      has_type E (TApp e1 e2) (open b e2)
  | TyTPi : forall L E a b,
      has_type E a TStar ->
      (forall x, x \notin L -> has_type (E & x ~ a) (open b (TFVar x)) TStar) ->
      has_type E (TPi a b) TStar
  | TyTCastUp : forall E t1 t2 e,
      has_type E e t2 ->
      (* really need the following? *)
      red t1 t2 ->
      (* has_type E t1 TStar -> *)
      has_type E (TCastup e) t1
  | TyTCastDown : forall E t1 t2 e,
      has_type E e t1 ->
      red t1 t2 ->
      has_type E (TCastdn e) t2
  | TyTProd : forall E t1 t2,
      has_type E t1 TStar ->
      has_type E t2 TStar ->
      has_type E (TProd t1 t2) TStar
  | TyTPair : forall E e1 e2 t1 t2,
      has_type E e1 t1 ->
      has_type E e2 t2 ->
      has_type E (TPair e1 e2) (TProd t1 t2)
  | TyTFst : forall E e t1 t2,
      has_type E e (TProd t1 t2) ->
      has_type E (TFst e) t1
  | TyTSnd : forall E e t1 t2,
      has_type E e (TProd t1 t2) ->
      has_type E (TSnd e) t2

  with wft : ctx -> Prop :=
  | wft_nil : wft empty
  | wft_cons : forall E x U,
      x # E ->
      has_type E U TStar ->
      wft (E & x ~ U).

  Hint Constructors has_type wft.

End Typing.
