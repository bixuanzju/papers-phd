Set Implicit Arguments.

Require Import definitions.
Require Import LibLN.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.
Require Import Program.Equality.



Module Typing
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.


  Inductive sub : list DExp -> list (var * DExp) -> DExp -> DExp -> DExp -> DExp -> Prop :=
  | SVar : forall E S1 S2 x, sub S1 S2 E (DFVar x) (DFVar x) E (* if S1 != empty, V else N *)
  | SStar : forall E S, sub nil S E DStar DStar E
  | SPi : forall L A B A' B' E E1 E2 S,
      (forall x, ~ In x L ->
            sub nil S (DFVar x) A' A E1 /\
            sub nil S (DApp E E1) (open_source B (DFVar x)) (open_source B' (DFVar x)) (open_source E2 (DFVar x))) ->
      sub nil S E (DPi A B) (DPi A' B') (DLam E2)
  | SLam: forall L E A B E' T D S, (* I believe we need this here: A T ~~> C /\ B T ~~> D *)
      (forall x, ~ In x L -> sub D ((x, T) :: S) (DCastdn E) (open_source A (DFVar x)) (open_source B (DFVar x)) E') ->
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
    let C := gather_vars_with (fun (x : context DExp) => dom x) in
    let D := gather_vars_with (fun (x : context TExp) => dom x) in
    let E := gather_vars_with (fun x : DExp => fv_source x) in
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


  (* Customised induction principle *)
  Section sub_ind'.

    Variable P : list DExp -> list (var * DExp) -> DExp -> DExp -> DExp -> DExp -> Prop.

    (* Should be free variable? *)
    Hypothesis var_case : forall E S1 S2 x, P S1 S2 E (DFVar x) (DFVar x) E.
    Hypothesis star_case : forall E S, P nil S E DStar DStar E.
    Hypothesis pi_case : forall L A B A' B' E E1 E2 S,
        (forall x, ~ In x L ->
              sub nil S (DFVar x) A' A E1 /\
              sub nil S (DApp E E1) (open_source B (DFVar x)) (open_source B' (DFVar x)) (open_source E2 (DFVar x))) ->
        (forall x, ~ In x L ->
              P nil S (DFVar x) A' A E1 /\
              P nil S (DApp E E1) (open_source B (DFVar x)) (open_source B' (DFVar x)) (open_source E2 (DFVar x))) ->
        P nil S E (DPi A B) (DPi A' B') (DLam E2).
    Hypothesis lam_case : forall L E A B E' T D S,
        (forall x, ~ In x L -> sub D ((x, T) :: S) (DCastdn E) (open_source A (DFVar x)) (open_source B (DFVar x)) E') ->
        (forall x, ~ In x L -> P D ((x, T) :: S) (DCastdn E) (open_source A (DFVar x)) (open_source B (DFVar x)) E') ->
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
                 (fun x (y : ~ In x L) =>
                    match f x y with
                      conj t1 t2 => conj (sub_ind' t1) (sub_ind' t2)
                    end)


      | @SLam L E A B E' T D S0 s0 => @lam_case L E A B E' T D S0 s0
                                               (fun x (y : ~ In x L) =>
                                                  sub_ind' (s0 x y))
      | @SApp T E A B E' D S0 s0 => app_case s0 (sub_ind' s0)
      | @SCastDown E A B E' S0 s0 => @castdn_case E A B E' S0 s0 (sub_ind' s0)
      | @SCastUp E A B E' S0 s0 => @castup_case E A B E' S0 s0 (sub_ind' s0)
      | @SL1 E A C E' B S0 s0 => @sl1_case E A C E' B S0 s0 (sub_ind' s0)
      | @SL2 E A C E' B S0 s0 => @sl2_case E A C E' B S0 s0 (sub_ind' s0)
      | @SL3 E A B C E1 E2 S0 s0 s1 => @sl3_case E A B C E1 E2 S0 s0 (sub_ind' s0) s1 (sub_ind' s1)

      end.

  End sub_ind'.


  (* Check sub_ind'. *)
  (* Check sub_ind. *)


  Inductive has_type_source : context DExp -> DExp -> DExp -> Prop :=
  | TyStar : forall Gamma, wfs Gamma -> has_type_source Gamma DStar DStar
  | TyVar : forall Gamma x ty,
      wfs Gamma ->
      List.In (x, ty) Gamma ->
      has_type_source Gamma (DFVar x) ty
  | TyLam : forall L Gamma A B t,
      has_type_source Gamma (DPi A B) DStar ->
      (forall x, not (In x L) -> has_type_source (extend x A Gamma) (open_source t (DFVar x)) (open_source B (DFVar x))) ->
      has_type_source Gamma (DLam t) (DPi A B)
  | TyApp : forall Gamma E1 E2 A B,
      has_type_source Gamma E1 (DPi A B) ->
      has_type_source Gamma E2 A ->
      has_type_source Gamma (DApp E1 E2) (open_source B E2)
  | TyPi : forall Gamma L A B,
      has_type_source Gamma A DStar ->
      (forall x, not (In x L) -> has_type_source (extend x A Gamma) (open_source B (DFVar x)) DStar) ->
      has_type_source Gamma (DPi A B) DStar
  | TyAnd : forall Gamma A B,
      has_type_source Gamma A DStar ->
      has_type_source Gamma B DStar ->
      has_type_source Gamma (DAnd A B) DStar
  | TyCastDown : forall Gamma A B C,
      (* has_type_source Gamma B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source Gamma A B ->
      has_type_source Gamma C DStar ->
      B ~~> C ->
      has_type_source Gamma (DCastdn A) C
  | TyCastUp : forall Gamma A B C,
      (* has_type_source Gamma B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source Gamma A C ->
      has_type_source Gamma B DStar ->
      B ~~> C ->
      has_type_source Gamma (DCastup A) B
  (* FIXME *)
  | TySub : forall Gamma A A' B C,
      has_type_source Gamma A B ->
      sub nil nil A B C A' ->
      has_type_source Gamma A C
  | TyMerge1: forall Gamma E1 E2 A,
      has_type_source Gamma E1 A ->
      sterm E2 ->
      has_type_source Gamma (DMerge E1 E2) A
  | TyMerge2: forall Gamma E1 E2 A,
      has_type_source Gamma E2 A ->
      sterm E1 ->
      has_type_source Gamma (DMerge E1 E2) A
  | TyInter: forall Gamma E A1 A2,
      has_type_source Gamma E A1 ->
      has_type_source Gamma E A2 ->
      has_type_source Gamma E (DAnd A1 A2)
  | TyInter1: forall Gamma E A1 A2,
      has_type_source Gamma E (DAnd A1 A2) ->
      has_type_source Gamma E A1
  | TyInter2: forall Gamma E A1 A2,
      has_type_source Gamma E (DAnd A1 A2) ->
      has_type_source Gamma E A2
  with wfs : context DExp -> Prop :=
  | wfs_nil : wfs nil
  | wfs_cons : forall E x U,
      not (In x (dom E)) ->
      has_type_source E U DStar ->
      wfs (extend x U E).


  Hint Constructors has_type_source wfs.

  (* Inductive has_type_source : context DExp -> DExp -> DExp -> DExp -> Prop := *)
  (* | TyStar : forall Gamma, *)
  (*     wfs Gamma -> *)
  (*     has_type_source Gamma DStar DStar DStar *)
  (* | TyVar : forall Gamma x ty, *)
  (*     wfs Gamma -> *)
  (*     List.In (x, ty) Gamma -> *)
  (*     has_type_source Gamma (DFVar x) ty (DFVar x) *)
  (* | TyLam : forall L Gamma A B t t' E, *)
  (*     has_type_source Gamma (DPi A B) DStar E -> *)
  (*     (forall x, not (In x L) -> *)
  (*           has_type_source (extend x A Gamma) *)
  (*                           (open_source t (DFVar x)) *)
  (*                           (open_source B (DFVar x)) *)
  (*                           (open_source t' (DFVar x))) -> *)
  (*     has_type_source Gamma (DLam t) (DPi A B) (DLam t') *)
  (* | TyApp : forall Gamma E1 E2 E1' E2' A B, *)
  (*     has_type_source Gamma E1 (DPi A B) E1' -> *)
  (*     has_type_source Gamma E2 A E2' -> *)
  (*     has_type_source Gamma (DApp E1 E2) (open_source B E2) (DApp E1' E2') *)
  (* | TyPi : forall Gamma L A A' B B', *)
  (*     has_type_source Gamma A DStar A' -> *)
  (*     (forall x, not (In x L) -> has_type_source (extend x A Gamma) (open_source B (DFVar x)) DStar (open_source B' (DFVar x))) -> *)
  (*     has_type_source Gamma (DPi A B) DStar (DPi A' B') *)
  (* | TyAnd : forall Gamma A A' B B', *)
  (*     has_type_source Gamma A DStar A' -> *)
  (*     has_type_source Gamma B DStar B' -> *)
  (*     has_type_source Gamma (DAnd A B) DStar (DAnd A' B') *)
  (* | TyCastDown : forall Gamma A B C A' C', *)
  (*     (* has_type_source Gamma B DStar -> *) (* can probably be shown as a theorem ? *) *)
  (*     has_type_source Gamma A B A' -> *)
  (*     has_type_source Gamma C DStar C' -> *)
  (*     B ~~> C -> *)
  (*     has_type_source Gamma (DCastdn A) C (DCastdn A') *)
  (* | TyCastUp : forall Gamma A B C A' B', *)
  (*     (* has_type_source Gamma B DStar -> *) (* can probably be shown as a theorem ? *) *)
  (*     has_type_source Gamma A C A' -> *)
  (*     has_type_source Gamma B DStar B' -> *)
  (*     B ~~> C -> *)
  (*     has_type_source Gamma (DCastup A) B (DCastup A') *)
  (* | TySub : forall Gamma A A' A'' B C, *)
  (*     has_type_source Gamma A B A' -> *)
  (*     sub nil nil A' B C A'' -> *)
  (*     has_type_source Gamma A C A'' *)
  (* | TyMerge1: forall Gamma E1 E1' E2 A, *)
  (*     has_type_source Gamma E1 A E1' -> *)
  (*     sterm E2 -> *)
  (*     has_type_source Gamma (DMerge E1 E2) A (DMerge E1' E2) *)
  (* | TyMerge2: forall Gamma E1 E2 E2' A, *)
  (*     has_type_source Gamma E2 A E2' -> *)
  (*     sterm E1 -> *)
  (*     has_type_source Gamma (DMerge E1 E2) A (DMerge E1 E2') *)
  (* | TyInter: forall Gamma E A1 A2 A1' A2', *)
  (*     has_type_source Gamma E A1 A1' -> *)
  (*     has_type_source Gamma E A2 A2' -> *)
  (*     has_type_source Gamma E (DAnd A1 A2) (DMerge A1' A2') *)
  (* | TyInter1: forall Gamma E A1 A2 E', *)
  (*     has_type_source Gamma E (DAnd A1 A2) E' -> *)
  (*     has_type_source Gamma E A1 E' *)
  (* | TyInter2: forall Gamma E A1 A2 E', *)
  (*     has_type_source Gamma E (DAnd A1 A2) E' -> *)
  (*     has_type_source Gamma E A2 E' *)

  (* with wfs : context DExp -> Prop := *)
  (* | wfs_nil : wfs nil *)
  (* | wfs_cons : forall E x U e, *)
  (*     not (In x (dom E)) -> *)
  (*     has_type_source E U DStar e -> *)
  (*     wfs (extend x U E). *)


  (* Hint Constructors has_type_source wfs. *)

  (* =======================
     Typing: T |- A : B ~> e  (without subsumption)
     =======================
  *)

  Definition opt (t : TExp) :=
    match t with
      | (TFst (TPair e1 e2)) => e1
      | (TSnd (TPair e1 e2)) => e2
      | _ => t
    end.

  Inductive has_type_source2 : context DExp -> DExp -> DExp -> TExp -> Prop :=
  | Ty2Star : forall Gamma,
      wfs2 Gamma ->
      has_type_source2 Gamma DStar DStar TStar
  | Ty2Var : forall Gamma x ty,
      wfs2 Gamma ->
      List.In (x, ty) Gamma ->
      has_type_source2 Gamma (DFVar x) ty (TFVar x)
  | Ty2Lam : forall L Gamma A B t t1 e,
      has_type_source2 Gamma (DPi A B) DStar e ->
      (forall x, not (In x L) ->
            has_type_source2 (extend x A Gamma) (open_source t (DFVar x)) (open_source B (DFVar x)) (open t1 (TFVar x))) ->
      has_type_source2 Gamma (DLam t) (DPi A B) (TLam t1)
  | Ty2App : forall Gamma E1 E2 A B e1 e2,
      has_type_source2 Gamma E1 (DPi A B) e1 ->
      has_type_source2 Gamma E2 A e2 ->
      has_type_source2 Gamma (DApp E1 E2) (open_source B E2) (TApp e1 e2)
  | Ty2Pi : forall L Gamma A B t1 t2,
      has_type_source2 Gamma A DStar t1 ->
      (forall x, not (In x L) -> has_type_source2 (extend x A Gamma) (open_source B (DFVar x)) DStar (open t2 (TFVar x))) ->
      has_type_source2 Gamma (DPi A B) DStar (TPi t1 t2)
  | Ty2And : forall Gamma A B t1 t2,
      has_type_source2 Gamma A DStar t1 ->
      has_type_source2 Gamma B DStar t2 ->
      has_type_source2 Gamma (DAnd A B) DStar (TProd t1 t2)
  | Ty2CastDown : forall Gamma A B C a c,
      (* has_type_source Gamma B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source2 Gamma A B a ->
      has_type_source2 Gamma C DStar c ->
      B ~~> C ->
      has_type_source2 Gamma (DCastdn A) C (TCastdn a)
  | Ty2CastUp : forall Gamma A B C a b,
      (* has_type_source Gamma B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source2 Gamma A C a ->
      has_type_source2 Gamma B DStar b ->
      B ~~> C ->
      has_type_source2 Gamma (DCastup A) B (TCastup a)
  | Ty2Merge1: forall Gamma E1 E2 A e,
      has_type_source2 Gamma E1 A e ->
      sterm E2 ->
      has_type_source2 Gamma (DMerge E1 E2) A e
  | Ty2Merge2: forall Gamma E1 E2 A e,
      has_type_source2 Gamma E2 A e ->
      sterm E1 ->
      has_type_source2 Gamma (DMerge E1 E2) A e
  | Ty2Inter: forall Gamma E A1 A2 e1 e2,
      has_type_source2 Gamma E A1 e1 ->
      has_type_source2 Gamma E A2 e2 ->
      has_type_source2 Gamma E (DAnd A1 A2) (TPair e1 e2)
  | Ty2Inter1: forall Gamma E A1 A2 e,
      has_type_source2 Gamma E (DAnd A1 A2) e ->
      has_type_source2 Gamma E A1 (opt (TFst e))
  | Ty2Inter2: forall Gamma E A1 A2 e,
      has_type_source2 Gamma E (DAnd A1 A2) e ->
      has_type_source2 Gamma E A2 (opt (TSnd e))

  with wfs2 : context DExp -> Prop :=
  | wfs2_nil : wfs2 nil
  | wfs2_cons : forall E x U e,
      not (In x (dom E)) ->
      has_type_source2 E U DStar e ->
      wfs2 (extend x U E).

  Hint Constructors has_type_source2 wfs2.

  Scheme typing_induct := Induction for has_type_source2 Sort Prop with wf_induct := Induction for wfs2 Sort Prop.

  (* Inductive P : DExp -> DExp -> TExp -> Prop := *)
  (* | PStar : P DStar DStar TStar *)
  (* | PLam : forall A B E e, P (DLam E) (DPi A B) (TLam e)  *)
  (* | Step : forall A B E e1 e2, P E A e1 -> P E B e2 -> P E (DAnd A B) (TPair e1 e2). *)

  (* Require Import Program.Equality. *)

  (* Lemma prop_star : forall Gamma A B e, has_type_source2 Gamma A B e -> P A B e. *)
  (*   intros. *)
  (*   induction H. *)
  (*   apply PStar. admit. apply PLam. admit. admit. admit. admit. admit. admit. admit. *)
  (*   apply Step. auto. auto. *)
  (*   inversion IHhas_type_source2; subst. *)
  (*   simpl. auto. *)
  (*   inversion IHhas_type_source2; subst. *)
  (*   simpl. inversion IHhas_type_source2; subst. auto. *)
  (* Admitted. *)

  (* Lemma prop_star2 : forall Gamma e, has_type_source2 Gamma DStar DStar e -> e = TStar. *)
  (*   intros. *)
  (*   apply prop_star in H. inversion H. auto. *)
  (* Defined. *)


  (* Inductive has_type_source3 : context DExp -> DExp -> DExp -> TExp -> Prop := *)
  (* | Ty3Star : has_type_source3 nil DStar DStar TStar *)
  (* | Ty3Start : forall Gamma x A a, *)
  (*     has_type_source3 Gamma A DStar a -> *)
  (*     has_type_source3 (extend x A Gamma) (DFVar x) A (TFVar x) *)
  (* | Ty3Weak : forall Gamma A B C a c x, *)
  (*     has_type_source3 Gamma A B a -> *)
  (*     has_type_source3 Gamma C DStar c -> *)
  (*     has_type_source3 (extend x C Gamma) A B a *)
  (* | Ty3Lam : forall L Gamma A B t t1, *)
  (*     (forall x, not (In x L) -> has_type_source3 (extend x A Gamma) (open_source t (DFVar x)) (open_source B (DFVar x)) (open t1 (TFVar x))) -> *)
  (*     has_type_source3 Gamma (DLam t) (DPi A B) (TLam t1) *)
  (* | Ty3App : forall Gamma E1 E2 A B e1 e2, *)
  (*     has_type_source3 Gamma E1 (DPi A B) e1 -> *)
  (*     has_type_source3 Gamma E2 A e2 -> *)
  (*     has_type_source3 Gamma (DApp E1 E2) (open_source B E2) (TApp e1 e2) *)
  (* | Ty3Pi : forall Gamma L A B t1 t2, *)
  (*     has_type_source3 Gamma A DStar t1 -> *)
  (*     (forall x, not (In x L) -> has_type_source3 (extend x A Gamma) (open_source B (DFVar x)) DStar (open t2 (TFVar x))) -> *)
  (*     has_type_source3 Gamma (DPi A B) DStar (TPi t1 t2) *)
  (* | Ty3And : forall Gamma A B t1 t2, *)
  (*     has_type_source3 Gamma A DStar t1 -> *)
  (*     has_type_source3 Gamma B DStar t2 -> *)
  (*     has_type_source3 Gamma (DAnd A B) DStar (TProd t1 t2) *)
  (* | Ty3CastDown : forall Gamma A B C t1 t2 e, *)
  (*     has_type_source3 Gamma B DStar t1 -> *)
  (*     has_type_source3 Gamma A B e -> *)
  (*     has_type_source3 Gamma C DStar t2 -> *)
  (*     t1 ~~> t2 -> *)
  (*     has_type_source3 Gamma (DCastdn A) C (TCastdn e) *)
  (* | Ty3CastUp : forall Gamma A B C t1 t2 e, *)
  (*     has_type_source3 Gamma B DStar t1 -> *)
  (*     has_type_source3 Gamma A C e -> *)
  (*     has_type_source3 Gamma C DStar t2 -> *)
  (*     t1 ~~> t2 -> *)
  (*     has_type_source3 Gamma (DCastup A) B (TCastup e) *)
  (* | Ty3Merge1: forall Gamma E1 E2 A e, *)
  (*     has_type_source3 Gamma E1 A e -> *)
  (*     has_type_source3 Gamma (DMerge E1 E2) A e *)
  (* | Ty3Merge2: forall Gamma E1 E2 A e, *)
  (*     has_type_source3 Gamma E2 A e -> *)
  (*     has_type_source3 Gamma (DMerge E1 E2) A e *)
  (* | Ty3Inter: forall Gamma E A1 A2 e1 e2, *)
  (*     has_type_source3 Gamma E A1 e1 -> *)
  (*     has_type_source3 Gamma E A2 e2 -> *)
  (*     has_type_source3 Gamma E (DAnd A1 A2) (TPair e1 e2) *)
  (* | Ty3Inter1: forall Gamma E A1 A2 e, *)
  (*     has_type_source3 Gamma E (DAnd A1 A2) e -> *)
  (*     has_type_source3 Gamma E A1 (opt (TFst e)) *)
  (* | Ty3Inter2: forall Gamma E A1 A2 e, *)
  (*     has_type_source3 Gamma E (DAnd A1 A2) e -> *)
  (*     has_type_source3 Gamma E A2 (opt (TSnd e)). *)

  (* Target typing *)
  Inductive has_type : context TExp -> TExp -> TExp -> Prop :=
  | TyTStar : forall Gamma,
      wft Gamma ->
      has_type Gamma TStar TStar
  | TyTVar : forall Gamma x ty,
      wft Gamma ->
      List.In (x, ty) Gamma ->
      has_type Gamma (TFVar x) ty
  | TyTLam : forall L Gamma a b t,
      (forall x, not (In x L) -> has_type (extend x a Gamma) (open t (TFVar x)) (open b (TFVar x))) ->
      has_type Gamma (TLam t) (TPi a b)
  | TyTApp : forall Gamma e1 e2 a b,
      has_type Gamma e1 (TPi a b) ->
      has_type Gamma e2 a ->
      has_type Gamma (TApp e1 e2) (open b e2)
  | TyTPi : forall Gamma L a b,
      has_type Gamma a TStar ->
      (forall x, not (In x L) -> has_type (extend x a Gamma) (open b (TFVar x)) TStar) ->
      has_type Gamma (TPi a b) TStar
  | TyTCastUp : forall Gamma t1 t2 e,
      has_type Gamma e t2 ->
      (* really need the following? *)
      red t1 t2 ->
      (* has_type Gamma t1 TStar -> *)
      has_type Gamma (TCastup e) t1
  | TyTCastDown : forall Gamma t1 t2 e,
      has_type Gamma e t1 ->
      red t1 t2 ->
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
      has_type Gamma (TSnd e) t2

  with wft : context TExp -> Prop :=
  | wft_nil : wft nil
  | wft_cons : forall E x U,
      not (In x (dom E)) ->
      has_type E U TStar ->
      wft (extend x U E).

  Hint Constructors has_type wft.


  Scheme typing_induct2 := Induction for has_type Sort Prop with wf_induct2 := Induction for wft Sort Prop.


  (*

appleS [E1, E2,...En] A   ==>      open (open A En) ... E1

How come a term can be opened multiple times?

   *)
  Fixpoint applyS (S : list DExp) (A : DExp) : DExp :=
    match S with
    | nil => A
    | E :: ES => open_source (applyS ES A) E
    end.

  Fixpoint substS (S : list (var * DExp)) (A : DExp) : DExp :=
    match S with
    | nil => A
    | (x, E) :: ES => subst_source x E (substS ES A)
    end.



  Inductive Result : list DExp -> list (var * DExp) -> DExp -> DExp -> DExp -> DExp -> Prop :=
  | RBNil : forall A B C A' S,
      (forall Gamma, has_type_source Gamma A (substS S B) -> has_type_source Gamma A' (substS S C)) ->
      Result nil S A B C A'
  | RFVar : forall A x T D S, Result (T :: D) S A (DFVar x) (DFVar x) A
  | RLam : forall L A A' B C T D S,
      (forall x, ~ In x L -> Result D ((x, T) :: S) (DCastdn A) (open_source B (DFVar x)) (open_source C (DFVar x)) A') ->
      Result (T :: D) S A (DLam B) (DLam C) (DCastup A')
  | RApp : forall A A' B C E D S T,
      Result (E :: T :: D) S A B C A' -> Result (T :: D) S A (DApp B E) (DApp C E) A'.

  (* D = T :: D' & B = DVar ==> DVar case *)


  (*

  apps A [D1,D2,...,Dn]  ==>   ((A D1) D2) ... Dn

   *)
  Fixpoint apps A D : DExp :=
    match D with
    | nil => A
    | T :: TS => apps (DApp A T) TS
    end.

  Lemma list_ass : forall {A a} (D1 : list A) {D2}, (a :: D1) ++ D2 = a :: (D1 ++ D2).
    intros.
    rewrite (app_comm_cons D1 D2). auto.
  Defined.

  Lemma apply_dand : forall S A B, applyS S (DAnd A B) = DAnd (applyS S A) (applyS S B).
    induction S; intros; simpl. auto.
    rewrite (IHS A B). unfold open_source. simpl. auto.
  Defined.

  Lemma apply_castdn : forall S A, applyS S (DCastdn A) = DCastdn (applyS S A).
    induction S; intros; simpl. auto.
    rewrite (IHS A). unfold open_source. simpl. auto.
  Defined.

  Lemma apply_castup : forall S A, applyS S (DCastup A) = DCastup (applyS S A).
    induction S; intros; simpl. auto.
    rewrite (IHS A). unfold open_source. simpl. auto.
  Defined.


  Lemma substS_pi : forall S A A', substS S (DPi A A') = DPi (substS S A) (substS S A').
  Admitted.

  Lemma substS_castup : forall S A, substS S (DCastup A) = DCastup (substS S A).
  Admitted.

  Lemma substS_dand : forall S A B, substS S (DAnd A B) = DAnd (substS S A) (substS S B).
  Admitted.





  Lemma app_many : forall B T D,
      apps (DApp (DLam B) T) D ~~> apps (open_source B T) D.
  Proof.
    intros.
    induction D.
  Admitted.

  Lemma red_open : forall B C D,
      B ~~> C ->
      (open_source B D) ~~> (open_source C D).
  Proof.
  Admitted.

  Lemma applyS_red : forall S D D',
      D ~~> D' ->
      applyS S D ~~> applyS S D'.
  Proof.
    intros.
    induction S.
    simpl; auto.
    simpl. apply red_open; auto.
  Qed.

  Lemma apply_open : forall S B T D,
      applyS S (apps (DApp (DLam B) T) D) ~~> applyS S (apps (open_source B T) D).
  Proof.
    intros.
    apply applyS_red.
    apply app_many.
  Qed.



  Lemma open_commute : forall C D E,
      open_source (open_source C D) E =
      open_source (open_source C E) D.
  Proof.
  Admitted.

  Lemma open_distribute_app : forall D E F,
      open_source (apps D E) F =
      apps (open_source D F) (map (fun a => open_source a F) E).
  Proof.
  Admitted.

  Fixpoint terms (E : list DExp) :=
    match E with
    | nil => True
    | (e :: es) => sterm e /\ terms es
    end.


  Axiom open_rec_sterm : forall t u,
      sterm t -> forall k, t = open_rec_source k u t.


  Lemma app_term : forall E F,
      terms E ->
      (map (fun a : DExp => open_source a F) E) = E.
  Proof.
    intros.
    induction E; simpl; auto.
    inversion H.
    pose (IH := IHE H1).
    rewrite IH; clear IH.
    unfold open_source.
    rewrite <- (open_rec_sterm F H0 0). auto.
  Qed.


  Lemma open_distribute_app_term : forall D E F,
      terms E ->
      open_source (apps D E) F =
      apps (open_source D F) E.
  Proof.
    intros.
    pose (IH := open_distribute_app D E F).
    rewrite app_term in IH; auto.
  Qed.


  (*

((C ^ T) D1 ..  Dn) ^ S1 ... ^ Sn

= C ^ T ^ S1 ... ^ Sn

((C D1) ... D2) ^ S1 ... ^ Sn ^ T

= C ^ S1 .. ^ Sn ^ T

hold only when each D is a locally closed term and open is commute

   *)


  Lemma applyS_open : forall S C T D,
      applyS S (apps (open_source C T) D) =
      open_source (applyS S (apps C D)) T.
  Proof.
  Admitted.



  Axiom red_star : forall E B C,
    B ~~> C ->
    has_type_source E B DStar ->
    has_type_source E C DStar.


  Axiom red_star_rev : forall E B C,
    B ~~> C ->
    has_type_source E C DStar ->
    has_type_source E B DStar.


  Axiom typing_wf_from_typing : forall E A B,
      has_type_source E A B ->
      has_type_source E B DStar.


  Axiom regular_typing : forall Gamma A B,
      has_type_source Gamma A B -> wfs Gamma /\ sterm A /\ sterm B.


  Axiom typing_weaken : forall x G e T T',
      has_type_source G e T ->
      wfs (extend x T' G) ->
      has_type_source (extend x T' G) e T.



  Lemma apps_lemma : forall {D2 D1 S E A B E'},
      sub (D1 ++ D2) S E A B E' -> Result (D1 ++ D2) S E A B E' -> Result D2 S E (apps A D1) (apps B D1) E'.
    destruct D2; intros.
    -
      rewrite (app_nil_r D1) in H, H0.
      induction H0.
      (* Base case *)
      simpl. apply RBNil. auto.
      simpl. apply RBNil. auto.
      (* Lam case *)
      inversion H; subst; clear H.
      pick_fresh x.
      assert (~ In x L0). admit.
      lets : H6 H; clear H6.
      assert (~ In x L). admit.
      lets : H1 H3 H2; clear H1.
      inversion H4; subst. apply RBNil. intros.
      pose (@TyCastDown _ _ _ (substS ((x, T) :: S) (apps (open_source B (DFVar x)) D)) H5).
      assert (substS S (apps (DLam B) (T :: D)) ~~> substS ((x, T) :: S) (apps (open_source B (DFVar x)) D)). admit.
      assert ((substS S (apps (DLam C) (T :: D))) ~~> substS ((x, T) :: S) (apps (open_source C (DFVar x)) D)). admit.

      apply (H1 _) in h; auto.
      apply (@TyCastUp _ _ _ (substS ((x, T) :: S) (apps (open_source C (DFVar x)) D))
); auto.


      (*inversion H4; subst.*)
      (* assert (applyS S (apps (DLam C) (T :: D)) ~~> applyS (T :: S) (apps C D)). *)
      (* simpl. *)
      (* pose (apply_open S C T D). *)
      (* rewrite <- applyS_open. auto. *)

      (* assert (applyS S (apps (DLam B) (T :: D)) ~~> applyS (T :: S) (apps B D)). *)
      (* simpl. *)
      (* pose (apply_open S B T D). *)
      (* rewrite <- applyS_open. auto. *)

      (* apply (H1 _) in h; auto. *)
      (* apply (@TyCastUp _ _ _ (applyS (T :: S) (apps C D))); auto. *)

      pose (WF2 := typing_wf_from_typing h).
      (* cast require both star, might still need red_star *)
      pose (red_star_rev H7 WF2). auto.

      pose (WF1 := typing_wf_from_typing H5).
      (* cast require both star, might still need red_star *)
      pose (red_star H6 WF1). auto.

      (* app case *)
      inversion H; subst. apply IHResult in H8. simpl. simpl in H8. auto.
    -
      (* Inductive case *)
      generalize H H0. clear H H0. generalize S E A B E' d. clear d S E A B E'.
      induction D1; simpl; intros.
      auto.
      apply IHD1. apply SApp. auto.
      destruct D1. simpl in H0. simpl. apply RApp. auto.
      rewrite (list_ass D1). apply RApp.
      rewrite (list_ass D1) in H0. auto.
  Qed.

  Inductive Form : DExp -> Prop :=
  | FBase : Form DStar
  | FStep1 : forall A B, Form A -> Form (DAnd A B)
  | FStep2 : forall A B, Form B -> Form (DAnd A B).

  Lemma bad_form : forall B C, Form B -> B ~~> C -> False.
    intros.
    induction H. inversion H0.
    inversion H0. inversion H0.
  Defined.

  Lemma form_preserve: forall C, Form C -> forall B D S A A', sub D S A B C A' -> Form B.
    intros C fc.
    induction fc; intros.
    dependent induction H; subst.
    apply FBase. apply (@FStep1 _ _ IHsub). apply (@FStep2 _ _ IHsub).
    dependent induction H; subst.
    apply IHsub in fc. apply (@FStep1 _ _ fc). auto.
    apply IHsub in fc. apply (@FStep2 _ _ fc). auto.
    apply (@IHfc _ _ _  _ _ H).
    dependent induction H; subst.
    apply IHsub in fc. apply (@FStep1 _ _ fc). auto.
    apply IHsub in fc. apply (@FStep2 _ _ fc). auto.
    apply (@IHfc _ _ _  _ _ H0).
  Defined.

  Lemma castup_false : forall B, Form B -> forall A Gamma, has_type_source Gamma (DCastup A) B -> False.
    intros.
    dependent induction H0; subst.
    apply (bad_form H H0).
    apply IHhas_type_source. apply (@form_preserve C H _ _ _ _ _ H1).
    inversion H; subst. apply IHhas_type_source1. auto. apply IHhas_type_source2. auto.
    apply (IHhas_type_source (@FStep1 _ _ H)).
    apply (IHhas_type_source (@FStep2 _ _ H)).
  Defined.

  Lemma sub_gen : forall {A A' B C D S}, sub D S A B C A' -> Result D S A B C A'.
    intros.
    induction H using sub_ind'; intros.
    (* DBVar *)
    destruct S1.
    apply RBNil. intros. auto.
    apply RFVar.
    (* Star *)
    apply RBNil; intros. auto.
    (* Pi *)
    apply RBNil; intros.
    rewrite substS_pi in *.
    apply_fresh TyLam as x.
    (* star should hold *)
    admit.
    assert (~ In x L). admit.
    lets [IH1 IH2] : H0 H2; clear H0.
    inverts IH1 as HH1.
    inverts IH2 as HH2.
    forwards TyE1 : HH1 (extend x (substS S A') Gamma).
    apply TyVar.
    (* WFS *)
    admit. simpl. auto.

    forwards TyE: typing_weaken x Gamma (substS S A') H1.
    (* WFS *)
    admit.
    assert (open_source (substS S B') (DFVar x) = substS S (open_source B' (DFVar x))). admit.
    rewrite H0.
    apply HH2.
    lets TyApp: TyApp TyE TyE1.
    assert (open_source (substS S B) (DFVar x) = substS S (open_source B (DFVar x))). admit.
    rewrite <- H3.
    (*

    look at TyApp and the goal


    Here is an counter example:

    Assume the context E = y : Pi x : * & *. x


    x <| * <: * & * |> x,,x       y (x,,x) <| x <: x |> y (x,,x)
  ------------------------------------------------------------
    y <| Pi x : * & *. x <: Pi x : *. x |> \x. y (x,,x)


    But   G |- \x . y (x,,x) : Pi x : *. x,,x

    Not   Pi x : *. x




     *)
    admit.

    (* Lam *)
    apply_fresh RLam as x.
    assert (~ In x L). admit.
    lets : H0 H1; auto.

    (* App *)
    assert (forall A, DApp A T = apps A (T :: nil)). intros. simpl. auto.
    rewrite (H0 A). rewrite (H0 B). clear H0.
    apply apps_lemma. rewrite (list_ass nil). simpl. auto.
    rewrite (list_ass nil). simpl. auto.
    (* CastDown *)
    inversion IHsub; subst. clear IHsub.
    apply RBNil. intros.
    lets H2 : typing_wf_from_typing H1.
    (* seems the conditions are useless *)
    (* TODO: counter example *)
    admit.

    (* CastUp *)
    inversion IHsub; subst. clear IHsub.
    apply RBNil. intros.
    pose (H2 := typing_wf_from_typing H1).
    rewrite (substS_castup S A) in H2.
    destruct (@castup_false _ FBase _ _ H2).

    (* And *)
    inversion IHsub; subst. apply RBNil. intros.
    rewrite (substS_dand S A B) in H1.
    exact (H0 _ (@TyInter1 _ _ _ _ H1)).
    inversion IHsub; subst. clear IHsub. apply RBNil. intros.
    rewrite (substS_dand S A B) in H1.
    exact (@H0 _ (@TyInter2 _ _ _ _ H1)).
    inversion IHsub1. inversion IHsub2. subst. apply RBNil. intros.
    pose (H1 _ H3).
    pose (H2 _ H3).
    rewrite (substS_dand S B C).
    destruct (regular_typing h) as [? [TE1 ?]].
    destruct (regular_typing h0) as [? [TE2 ?]].
    apply TyInter.
    apply TyMerge1; auto.
    apply TyMerge2; auto.
  Qed.

  (* has_type_source A (DApp B C) -> exists T, DApp B C ~~> T /\ has_type_source (castDown A) T *)

  Lemma main : forall A B C A', sub nil nil A B C A' -> forall Gamma, has_type_source Gamma A B -> has_type_source Gamma A' C.
    intros A B C A' H. pose (sub_gen H). inversion r; subst. simpl in H0. auto.
  Defined.

  (* Lemma sub_gen : forall A B C A' e e', *)
  (*     sub nil nil A B C A' -> *)
  (*     forall Gamma, has_type_source2 Gamma A B e -> *)
  (*              has_type_source2 Gamma A' C e'. *)
  (* Proof. *)
  (* Admitted. *)


  (*
castUp 3 : (\x . x) Int

sub nil ((x,Int) :: nil) (castDown (castUp 3)) x x (castDown (castUp 3))
-----------------------------------------------------------------------------
sub (Int :: nil) nil (castUp 3) (\x . x) (\x . x) (castUp (castDown (castUp 3)))
-------------------------------------------------------------------------------
sub nil nil (castUp 3) ((\x . x) Int) ((\x . x) Int) (castUp (castDown (castUp 3)))


sub nil ((x, Int) :: (y, Int) :: nil) (castDown (castDown (castUp 3))) x x
-------------------------------------------------------------------
sub (Int :: nil) ((y, Int) :: nil) (castDown (castUp 3)) (\x . x) (\x . x)
----------------------------------------------------------------------
sub (Int :: Int :: nil) nil (castUp 3) (\y . (\x . x)) (\y . (\x . x))
---------------------------------------------------------------------------
sub (Int :: nil) nil (castUp 3) ((\y . (\x . x)) Int) ((\y . (\x . x)) Int)
-------------------------------------------------------------------------------
sub nil nil (castUp 3) ((\y . (\x . x)) Int Int) ((\y . (\x . x)) Int Int) (castUp (castDown (castUp 3)))


sub nil (castDown (castUp 3) : [x -> Int] x) x x (castDown (castUp 3) : [x -> Int] x)
-----------------------------------------------------------------------------
sub (Int :: nil) (castUp 3 : (\x . x))  (\x . x) (\x . x) (castUp (castDown (castUp 3)) : (\x . x))
-------------------------------------------------------------------------------
sub nil (castUp 3 : ((\x . x) Int)) ((\x . x) Int) ((\x . x) Int) (castUp (castDown (castUp 3)) : ((\x . x) Int))

 *)

(* shapes in type applications:

(\x . x) Int -> end up in a bound variable being applied to Int; goes into the RBNil case

z Int -> a free variable being applied: the RBVar case (should be on free; not bound variables)

(\x . z) Int -> end up in the RBNil case

(\x . z) Int Int -> ends in RBVar case; types must be identical

(\x . z Int) Int -> ends up in RBVar case

Hypothesis: if I end up in a free variable, then types are identical:

IHsub : Result (T :: D) S E A B E' -> Result (T :: D) S E A A E' (when I end up in var case)

If I end up elsewhere then there exists A' B'


*)

(* TODO

ASSUME:

Lemma sub_gen : forall A B C A', sub nil nil A B C A' -> forall Gamma, has_type_source Gamma A B A' -> has_type_source2 Gamma A' C e.


there are a few steps:

1) firstly we need to have a source typing relation with subsumption, which produces an equivalent source terms A’ which can be type-checked without subsumption

so, you need a modified version of the typing relation:

has_type_source Gamma A B ​A’

where you get the A’ which can be checked without subsumption

2) secondly you need a version of source typing without subsumption:

has_type_source2 Gamma A' B ​e

which produces a target term

3) then you need to show 2 preservation theorems

First:

has_type_source Gamma A B ​*A’*​ -> has_type_source2 Gamma A' B ​*e*​

Second:

has_type_source2 Gamma A' B ​*e*​ -> has_type |Gamma| e |B|

MORE TODO:

At the moment casts are unchecked.

TODO: We need to define reduction on source and then fix the cast cases.

 *)

End Typing.
