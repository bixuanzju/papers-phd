Require Import definitions.
Require Import subtyping4.

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
  
  Inductive svalue : DExp -> Prop :=
  | svalue_star : svalue DStar
  | svalue_lam : forall t1,
                  sterm (DLam t1) -> svalue (DLam t1)
  | svalue_pi : forall t1 t2,
                 sterm (DPi t1 t2) -> svalue (DPi t1 t2)
  | svalue_castup : forall e,
                     svalue e -> svalue (DCastup e)
  | svalue_inter : forall t1 t2, svalue (DAnd t1 t2)
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
                  sred (DMerge e1 e2) (DMerge e1' e2)
   | sred_merge2 : forall e1 e2 e2',
                     svalue e1 ->
                     sred e2 e2' ->
                     sred (DMerge e1 e2) (DMerge e1 e2'). (* missing rules for merge *)
   
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

  Notation "t ~~> t'" := (sred t t') (at level 68).

  (* ======================= *)
  (* Typing: T |- A : B ~> e  (assumming source-target) *)
  (* ======================= *)

  Inductive has_type_source : context DExp -> DExp -> DExp -> Prop :=
  | TyStar : forall Gamma, ok Gamma -> has_type_source Gamma DStar DStar 
  | TyVar : forall Gamma x ty,
      ok Gamma ->
      List.In (x, ty) Gamma ->
      has_type_source Gamma (DFVar x) ty
  | TyLam : forall L Gamma A B t,
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
      B ~~> C ->
      has_type_source Gamma (DCastdn A) C
  | TyCastUp : forall Gamma A B C,
      (* has_type_source Gamma B DStar -> *) (* can probably be shown as a theorem ? *)
      has_type_source Gamma A C ->
      B ~~> C ->
      has_type_source Gamma (DCastup A) B
  | TySub : forall Gamma A A' B C,
      has_type_source Gamma A B ->
      sub nil nil A B C A' ->
      has_type_source Gamma A C
  | TyMerge1: forall Gamma E1 E2 A,
      has_type_source Gamma E1 A ->
      has_type_source Gamma (DMerge E1 E2) A
  | TyMerge2: forall Gamma E1 E2 A,
      has_type_source Gamma E2 A ->
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
      has_type_source Gamma E A2.

  Hint Constructors has_type_source.

  Fixpoint applyS (S : list DExp) (A : DExp) : DExp :=
    match S with
      | nil => A
      | E :: ES => open_source (applyS ES A) E
    end.

  
  Inductive Result : list DExp -> list DExp -> DExp -> DExp -> DExp -> DExp -> Prop :=
  | RBNil : forall A B C A' S, (forall Gamma, has_type_source Gamma A (applyS S B) -> has_type_source Gamma A' (applyS S C)) -> Result nil S A B C A'  
  | RBVar : forall A x T D S, Result (T :: D) S A (DBVar x) (DBVar x) A
  | RLam : forall A A' B C T D S, Result D (T :: S) (DCastdn A) B C A' -> Result (T :: D) S A (DLam B) (DLam C) (DCastup A')
  | RApp : forall A A' B C E D S T, Result (E :: T :: D) S A B C A' -> Result (T :: D) S A (DApp B E) (DApp C E) A'.

  (* D = T :: D' & B = DVar ==> DVar case *)

  Require Import Program.Equality.
 
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

  Lemma apps_lemma : forall {D2 D1 S E A B E'}, sub (D1 ++ D2) S E A B E' -> Result (D1 ++ D2) S E A B E' -> Result D2 S E (apps A D1) (apps B D1) E'.
    destruct D2; intros.
    rewrite (app_nil_r D1) in H, H0.
    induction H0.
    (* Base case *)
    simpl. apply RBNil. auto.
    simpl. apply RBNil. intros. auto.
    inversion H; subst.
    apply IHResult in H5.
    inversion H5; subst. apply RBNil. intros.
    pose (TyCastDown _ _ _ (applyS (T :: S) (apps B D)) H2). 
    (*inversion H4; subst.*)
    apply (H1 _) in h.
    apply (TyCastUp _ _ _ (applyS (T :: S) (apps C D))).
    auto. simpl. admit. admit.
    inversion H; subst. apply IHResult in H8. simpl. simpl in H8. auto.
    (* Inductive case *) 
    generalize H H0. clear H H0. generalize S E A B E' d. clear d S E A B E'. 
    induction D1; simpl; intros.
    auto.
    apply IHD1. apply SApp. auto.
    destruct D1. simpl in H0. simpl. apply RApp. auto.
    rewrite (list_ass D1). apply RApp.
    rewrite (list_ass D1) in H0. auto.
  Admitted.

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
    apply FBase. apply (FStep1 _ _ IHsub). apply (FStep2 _ _ IHsub).
    dependent induction H; subst.
    apply IHsub in fc. apply (FStep1 _ _ fc). auto.
    apply IHsub in fc. apply (FStep2 _ _ fc). auto.
    apply (IHfc _ _ _  _ _ H).
    dependent induction H; subst.
    apply IHsub in fc. apply (FStep1 _ _ fc). auto.
    apply IHsub in fc. apply (FStep2 _ _ fc). auto.
    apply (IHfc _ _ _  _ _ H0).
  Defined.    

  Lemma castup_false : forall B, Form B -> forall A Gamma, has_type_source Gamma (DCastup A) B -> False.
    intros.
    dependent induction H0; subst.
    apply (bad_form B C H H1).
    apply IHhas_type_source. apply (form_preserve C H _ _ _ _ _ H1).
    inversion H; subst. apply IHhas_type_source1. auto. apply IHhas_type_source2. auto.
    apply (IHhas_type_source (FStep1 _ _ H)).
    apply (IHhas_type_source (FStep2 _ _ H)).
  Defined.
    
  Lemma sub_gen : forall {A A' B C D S}, sub D S A B C A' -> Result D S A B C A'. 
    intros.
    induction H; intros.
    (* DBVar *)
    destruct S1.
    apply RBNil. intros. auto. 
    apply RBVar.
    (* Star *)
    apply RBNil; intros. auto. 
    (* Pi *)
    inversion IHsub1; subst. clear IHsub1.
    inversion IHsub2; subst. clear IHsub2.
    apply RBNil; intros.
    admit. 
    (* Lam *)
    apply RLam. auto.
    (* App *)
    assert (forall A, DApp A T = apps A (T :: nil)). intros. simpl. auto.
    rewrite (H0 A). rewrite (H0 B). clear H0.
    apply apps_lemma. rewrite (list_ass nil). simpl. auto.
    rewrite (list_ass nil). simpl. auto.
    (* CastDown *)
    inversion IHsub; subst. clear IHsub.
    apply RBNil. intros.
    assert (has_type_source Gamma (applyS S (DCastdn A)) DStar). admit.
    rewrite (apply_castdn S B). rewrite (apply_castdn S A) in H2, H1.
    inversion H2; subst. inversion H6; subst. admit. admit. 
    (*inversion H2; subst. (* B0 ~~> DStar *)*)
    admit. admit. admit.
    (* CastUp *)
    inversion IHsub; subst. clear IHsub.
    apply RBNil. intros.
    assert (has_type_source Gamma (applyS S (DCastup A)) DStar). admit.
    rewrite (apply_castup S B). rewrite (apply_castup S A) in H2, H1.
    destruct (castup_false _ FBase _ _ H2). 
    (* And *)
    inversion IHsub; subst. apply RBNil. intros.
    rewrite (apply_dand S A B) in H1.
    exact (H0 _ (TyInter1 _ _ _ _ H1)).
    inversion IHsub; subst. clear IHsub. apply RBNil. intros.
    rewrite (apply_dand S A B) in H1.
    exact (H0 _ (TyInter2 _ _ _ _ H1)).
    inversion IHsub1. inversion IHsub2. subst. apply RBNil. intros.
    pose (H1 _ H3).
    pose (H2 _ H3).
    rewrite (apply_dand S B C).
    apply (TyInter _ _ _). apply TyMerge1. auto. apply TyMerge2. auto.
    Admitted.

  (* has_type_source A (DApp B C) -> exists T, DApp B C ~~> T /\ has_type_source (castDown A) T *)
  
   Lemma main : forall A B C A', sub nil nil A B C A' -> forall Gamma, has_type_source Gamma A B -> has_type_source Gamma A' C.
     intros A B C A' H. pose (sub_gen H). inversion r; subst. simpl in H0. auto.
   Defined. 

(* 
castUp 3 : (\x . x) Int

sub nil (Int :: nil) (castDown (castUp 3)) x x (castDown (castUp 3))  
-----------------------------------------------------------------------------
sub (Int :: nil) nil (castUp 3) (\x . x) (\x . x) (castUp (castDown (castUp 3)))
-------------------------------------------------------------------------------
sub nil nil (castUp 3) ((\x . x) Int) ((\x . x) Int) (castUp (castDown (castUp 3))) 


sub nil (Int :: Int :: nil) (castDown (castDown (castUp 3))) (\x . x) (\x . x)
-------------------------------------------------------------------
sub (Int :: nil) (Int :: nil) (castDown (castUp 3)) (\x . x) (\x . x)
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

(* SOME OLD STUFF: Can probably be deleted later *)

Fixpoint castsup (n : nat) (A : DExp) : DExp :=
    match n with
      | 0 => A
      | (S n) => DCastup (castsup n A)
    end.

  Fixpoint castsdn (n : nat) (A : DExp) : DExp :=
    match n with
      | 0 => A
      | (S n) => DCastdn (castsdn n A)
    end.
    

  Lemma apply_dapp : forall {S A B}, applyS S (DApp A B) = DApp (applyS S A) (applyS S B).
    induction S; intros; simpl. auto.
    rewrite (IHS A B). unfold open_source. simpl. auto.
  Defined.

  Lemma wkinded : forall {Gamma A B}, has_type_source Gamma A B -> has_type_source Gamma B DStar.
    intros.
    induction H. auto. admit.
    Admitted.

  Lemma sub_apply : forall {S1 S2 A B C A'}, sub S1 S2 A B C A' -> sub S1 nil A (applyS S2 B) (applyS S2 C) A'.
  Admitted.

  Lemma DCastdn_com : forall {n A}, DCastdn (castsdn n A) = castsdn n (DCastdn A).
    induction n; simpl; intros.
    auto. rewrite (IHn A). auto.
  Defined.
      
  Lemma casts : forall A x, DCastup (castsup x (DCastdn (castsdn x A))) = castsup (S x) (castsdn (S x) A).
    intros.
    induction x; simpl; auto.
  Defined.
    
  Lemma cast_typ : forall {x Gamma A B},
                     has_type_source Gamma A B -> has_type_source Gamma (castsup x (castsdn x A)) B.
    induction x; simpl; intros.
    auto.
  Admitted.

  Lemma silly : forall {n A}, A = castsup n (castsdn n A) -> n = 0.
    induction n; simpl; intros; try auto.
    destruct A; try (inversion H).
    Admitted.

  Lemma result_same : forall D n T S E A, Result (T :: D) S E A A (castsup n (castsdn n E)) -> Result D S E (DApp A T) (DApp A T) (castsup n (castsdn n E)).
    intros.
    dependent induction H.
    destruct D. apply RBNil. intros. rewrite (silly x). simpl. auto.
    apply RApp. rewrite (silly x). simpl. apply RBVar. 
    destruct D. apply RBNil. clear IHResult.
    inversion H; subst. intros. 
    (* Need to show: forall B S T, applyS S (DApp (DLam B) T) ~~> applyS (T :: S) B *)
    pose (TyCastDown _ _ _ (applyS (T :: S) B) H1). (*FIXME TyCastDown missing check of reduction! *)
    apply (H0 _) in h. rewrite <- x. 
    apply (TyCastUp _ _ _ (applyS (T :: S) B)). (*FIXME: TyCastDown missing check of reduction! *)
    auto.
    apply RApp. rewrite <- x. apply RLam. auto.
    destruct D.
    apply RBNil. intros. 
    apply (cast_typ H0).
    apply RApp. apply RApp. auto.
  Defined.

  Lemma split_result : forall {A A' B C D X},
                         Result D X A B C A' -> exists n, Result D X A B B (castsup n (castsdn n A)).
    intros. induction H. admit.
    exists 0; simpl. apply RBVar.
    destruct IHResult. exists (1+x). simpl.
    apply RLam. rewrite (DCastdn_com). auto.
    destruct IHResult. exists x. apply RApp. auto.
  Admitted.
