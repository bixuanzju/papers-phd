Require Import definitions.
Require Import subtyping2.

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

  (* Functions on contexts *)
  Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
    map (fun p => (fst p, (f (snd p)))) c.

  Inductive ok {A} : context A -> Prop :=
  | Ok_nil : ok nil
  | Ok_push : forall (E : context A) (v : var) (ty : A),
                ok E -> not (In v (dom E)) -> ok (extend v ty E).

  Hint Constructors ok.

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

  (* ======================= *)
  (* Typing: T |- A : B ~> e  (assumming source-target) *)
  (* ======================= *)

  Inductive has_type_source : context DExp -> DExp -> DExp -> TExp -> Prop :=
  | TyStar : forall Gamma, ok Gamma -> has_type_source Gamma DStar DStar TStar
  | TyVar : forall Gamma x ty,
      ok Gamma ->
      List.In (x, ty) Gamma ->
      has_type_source Gamma (DFVar x) ty (TFVar x)
  | TyLam : forall L Gamma A B t t1,
      (forall x, not (In x L) -> has_type_source (extend x A Gamma) (open_source t (DFVar x)) B (open t1 (TFVar x))) ->
      has_type_source Gamma (DLam t) (DPi A B) (TLam t1)
  | TyApp : forall Gamma E1 E2 A B e1 e2,
      has_type_source Gamma E1 (DPi A B) e1 ->
      has_type_source Gamma E2 A e2 ->
      has_type_source Gamma (DApp E1 E2) (open_source B E2) (TApp e1 e2)
  | TyPi : forall Gamma L A B t1 t2,
      has_type_source Gamma A DStar t1 ->
      (forall x, not (In x L) -> has_type_source (extend x A Gamma) B DStar t2) ->
      has_type_source Gamma (DPi A B) DStar (TPi t1 t2)
  | TyAnd : forall Gamma A B t1 t2,
      has_type_source Gamma A DStar t1 ->
      has_type_source Gamma B DStar t2 ->
      has_type_source Gamma (DAnd A B) DStar (TProd t1 t2)
  | TyCastDown : forall Gamma A B C t1 t2 e,
      has_type_source Gamma B DStar t1 ->
      has_type_source Gamma A B e ->
      has_type_source Gamma C DStar t2 ->
      t1 ~~> t2 ->
      has_type_source Gamma (DCastdn A) C (TCastdn e)
  | TyCastUp : forall Gamma A B C t1 t2 e,
      has_type_source Gamma B DStar t1 ->
      has_type_source Gamma A C e ->
      has_type_source Gamma C DStar t2 ->
      t1 ~~> t2 ->
      has_type_source Gamma (DCastup A) B (TCastup e)
  | TySub : forall Gamma A A' B C e e',
      has_type_source Gamma A B e ->
      sub nil A B C A' ->
      has_type_source Gamma A' C e' ->
      has_type_source Gamma A C e'
  | TyMerge1: forall Gamma E1 E2 A e,
      has_type_source Gamma E1 A e ->
      has_type_source Gamma (DMerge E1 E2) A e
  | TyMerge2: forall Gamma E1 E2 A e,
      has_type_source Gamma E2 A e ->
      has_type_source Gamma (DMerge E1 E2) A e
  | TyInter: forall Gamma E A1 A2 e1 e2,
      has_type_source Gamma E A1 e1 ->
      has_type_source Gamma E A2 e2 ->
      has_type_source Gamma E (DAnd A1 A2) (TPair e1 e2)
  | TyInter1: forall Gamma E A1 A2 e,
      has_type_source Gamma E (DAnd A1 A2) e ->
      has_type_source Gamma E A1 (TFst e)
  | TyInter2: forall Gamma E A1 A2 e,
      has_type_source Gamma E (DAnd A1 A2) e ->
      has_type_source Gamma E A2 (TSnd e).


  Hint Constructors has_type_source.



  Fixpoint applyD (e : DExp) (args : ArgStack) : DExp :=
    match args with
    | nil => e
    | d :: ds => applyD (DApp e d) ds
    end.


  Lemma sub_gen: forall D A B C A',
      sub D A B C A' ->
      forall Gamma e, has_type_source Gamma A (applyD B D) e ->
                 exists e', has_type_source Gamma A' (applyD C D) e'.
  Proof.
    intros D A B C A' Sub.
    induction Sub; intros; try (exists e; assumption).

    (* SPi, skip for now *)
    - admit.

    (* SLam *)
    (* cast involves elaboration, seems hard *)
    - admit.

    (* SApp *)
    - simpl in IHSub.
      apply IHSub in H.
      inversion H as [e' H'].
      exists e'; assumption.

    (* SCastDown *)
    - admit.

    (* SCastUp *)
    - admit.

    (* S&L1 *)
    - simpl in H.
      simpl in IHSub.
      simpl.
      apply TyInter1 in H.
      apply IHSub in H.
      inversion H as [e' H'].
      exists e'; assumption.

    (* S&L2 *)
    - simpl in H.
      simpl in IHSub.
      simpl.
      apply TyInter2 in H.
      apply IHSub in H.
      inversion H as [e' H'].
      exists e'; assumption.

    (* S&R *)
    -  simpl in IHSub1.
       simpl in IHSub2.
       simpl in H.
       simpl.

       assert (has_type_source Gamma E A e).
       exact H.
       apply IHSub1 in H.
       apply IHSub2 in H0.
       inversion H as [e1 H1].
       inversion H0 as [e2 H2].
       exists (TPair e1 e2).
       apply TyInter.
       apply TyMerge1.
       assumption.
       apply TyMerge2.
       assumption.

  Admitted.






  (* ================ OLD STUFF ================= *)

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
                  (* really need the following? *)
                  (* has_type Gamma t1 TStar -> *)
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

  (* Well-typed transformations *)

  Inductive WTTrans : context TExp -> TExp -> TExp -> TExp -> TExp -> Prop :=
  | WTTee : forall Gamma e A, WTTrans Gamma e A e A
  | WTTPi : forall Gamma L A B C D e e1 e2,
      (forall x, not (In x L) -> WTTrans (extend x C Gamma) (TFVar x) C e1 A) ->
      (forall x, not (In x L) -> WTTrans (extend x C Gamma) (TApp e e1) (open B (TFVar x)) (open e2 (TFVar x)) (open D (TFVar x))) ->
      WTTrans Gamma e (TPi A B) (TLam e2) (TPi C D)
  (* | WTTPi : forall Gamma L A B C D e e1 e2, *)
  (*     (forall x, not (In x L) -> *)
  (*           and (WTTrans (extend x C Gamma) (TFVar x) C e1 A) *)
  (*               (WTTrans (extend x C Gamma) (TApp e e1) (open B (TFVar x)) (open e2 (TFVar x)) (open D (TFVar x)))) -> *)
  (*     WTTrans Gamma e (TPi A B) (TLam e2) (TPi C D) *)
  | WTTCU : forall Gamma e e' A B B' C,
      WTTrans Gamma (TCastdn e) B e' B' -> A ~~> B -> C ~~> B' -> WTTrans Gamma e A (TCastup e') C
  | WTTFst : forall Gamma e e' A B C,
      WTTrans Gamma (TFst e) A e' C -> WTTrans Gamma e (TProd A B) e' C
  | WTTSnd : forall Gamma e e' A B C,
      WTTrans Gamma (TSnd e) B e' C -> WTTrans Gamma e (TProd A B) e' C
  | WTTPair : forall Gamma e e1 e2 A B C,
                WTTrans Gamma e A e1 B -> WTTrans Gamma e A e2 C -> WTTrans Gamma e A (TPair e1 e2) (TProd B C).

  Check WTTrans_ind.

Require Import Program.Equality.

Inductive trans_ctx : context DExp -> context TExp -> Prop :=
  | trans_nil : trans_ctx nil nil
  | trans_cons : forall sctx tctx x E T t,
                   trans_ctx sctx tctx ->
                   has_type_source sctx E T t ->
                   trans_ctx ((x,T) :: sctx) ((x,t) :: tctx).

  Lemma wt : forall {Gamma e e' A B},
      has_type Gamma e A -> WTTrans Gamma e A e' B -> has_type Gamma e' B.
  Proof.
    intros Gamma e e' A B Ty WTT.
    induction WTT.
    (* WTTee *)
    - assumption.


    (* WTTPi *)
    - admit.

    (* WTTCU *)
    - assert (has_type Gamma (TCastdn e) B).
      eapply TyTCastDown.
      exact Ty.
      assumption.
      apply IHWTT in H1.
      eapply TyTCastUp.
      exact H1.
      assumption.

    (* WTTFst *)
    - assert (has_type Gamma (TFst e) A).
      eapply TyTFst.
      exact Ty.
      apply IHWTT in H.
      assumption.

    (* WTTSnd *)
    - assert (has_type Gamma (TSnd e) B).
      eapply TyTSnd.
      exact Ty.
      apply IHWTT in H.
      assumption.

    - assert (has_type Gamma e1 B).
      apply IHWTT1 in Ty.
      assumption.
      assert (has_type Gamma e2 C).
      apply IHWTT2 in Ty.
      assumption.
      eapply TyTPair.
      assumption.
      assumption.
  Admitted.

Lemma unique_trans : forall {Gamma e A t1 t2},
                       has_type_source Gamma e A t1 -> has_type_source Gamma e A t2 -> t1 = t2.
Admitted.

Lemma lam_not_star : forall {Gamma A B t1}, has_type_source Gamma (DLam A) B t1 ->
                                        forall e e', not (sub e B DStar e').
intros. dependent induction H. unfold not. intros. inversion H1.
unfold not. intros.
assert (sub e B DStar e'). admit. (* by transitivity of subtyping *)
unfold not in IHhas_type_source. apply (IHhas_type_source e e').
auto.
Admitted.

Lemma sub_wt : forall e e' A B, sub e A B e' ->
                 forall t1 t2 Gamma Gamma', has_type_source Gamma A DStar t1 ->
                    has_type_source Gamma B DStar t2 ->
                    trans_ctx Gamma Gamma' ->
                    has_type Gamma' e t1 ->
                    has_type Gamma' e' t2.
intros e e' A B sub.
induction sub; intros.
(* DBVar *)
pose (unique_trans H H0). rewrite <- e0. auto.
(* Star *)
pose (unique_trans H H0). rewrite <- e0. auto.
admit.
(* DLam *)
inversion H.
pose (lam_not_star H3 e0 t1).
contradiction.
(* DApp *)
Admitted.

Lemma sub_wt : forall e e' A B, sub e A B e' ->
                 forall t1 t2 Gamma Gamma', has_type_source Gamma A DStar t1 ->
                    has_type_source Gamma B DStar t2 ->
                    trans_ctx Gamma Gamma' ->
                    has_type Gamma' e t1 ->
                    WTTrans Gamma' e t1 e' t2.
Proof.
intros e e' A B sub.
induction sub; intros.
(* DVar *)
pose (unique_trans H H0). rewrite e0.
apply WTTee.
(* DStar *)
pose (unique_trans H H0). rewrite e0.
apply WTTee.
(* DPi *)
admit. (* lets have a look at this one later *)
(* DLam *)
inversion H.
pose (lam_not_star H3 e0 t1).
contradiction.
(* DApp *)


(* need to show that \x . e cannot be of type star: auxiliary lemma *)
