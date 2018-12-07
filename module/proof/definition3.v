
Set Implicit Arguments.

Require Import definitions infrastructure.
Require Import LibLN.
Require Import List.

(* Incomplete *)
Inductive sub2 : list DExp -> list (var * DExp) -> list (var * TExp) -> TExp -> DExp -> DExp -> TExp -> Prop :=
| SVar : forall S1 S2 S3 e x, sub2 S1 S2 S3 e (DFVar x) (DFVar x) e
| SStar : forall S2 S3 e, sub2 nil S2 S3 e DStar DStar e
| SPi : forall L A B A' B' e e1 e2 S2 S3,
    (forall x, x \notin L ->
          sub2 nil S2 S3 (TFVar x) A' A e1 /\
          sub2 nil S2 ((x,e1) :: S3) (TApp e e1) (B ^ x) (B' ^ x) (open e2 (TFVar x))) ->
    sub2 nil S2 S3 e (DPi A B) (DPi A' B') (TLam e2)
| SLam: forall L e A B e' T D S2 S3,
    (forall x, x \notin L -> sub2 D ((x, T) :: S2) S3 (TCastdn e) (A ^ x) (B ^ x) e') ->
    sub2 (T :: D) S2 S3 e (DLam A) (DLam B) (TCastup e')
| SApp: forall T A B e e' D S2 S3,
    sub2 (T :: D) S2 S3 e A B e' -> sub2 D S2 S3 e (DApp A T) (DApp B T) e'.
(* | SCastDown: forall e A B e' S, *)
(*     sub2 nil S e A B e' -> sub2 nil S e (DCastdn A) (DCastdn B) e' *)
(* | SCastUp: forall e A B e' S, *)
(*     sub2 nil S e A B e' -> sub2 nil S e (DCastup A) (DCastup B) e' *)
(* | SL1: forall A C e e' B S, *)
(*     sub2 nil S e A C e' -> sub2 nil S e (DAnd A B) C (TFst e') *)
(* | SL2: forall A C e e' B S, *)
(*     sub2 nil S e B C e' -> sub2 nil S e (DAnd A B) C (TSnd e'). *)
(* | SL3 : forall A B C e1 e2 S, *)
(*     sub2 nil S e A B e1 -> sub2 nil S e A C e2 -> sub2 nil S e A (DAnd B C) (DMerge e1 e2). *)

(* | SL1: forall e A C e' B S, *)
(*     sub2 e A C e' -> sub2 nil S e (DAnd A B) C e' *)
(* | SL2: forall e A C e' B S, *)
(*     sub2 e B C e' -> sub2 nil S e (DAnd A B) C e' *)
(* | SL3 : forall e A B C e1 e2 S, *)
(*     sub2 e A B e1 -> sub2 nil S e A C e2 -> sub2 nil S e A (DAnd B C) (DMerge e1 e2). *)




(* Customised induction principle *)
Section sub_ind'.

  Variable P : list DExp -> list (var * DExp) -> list (var * TExp) -> TExp -> DExp -> DExp -> TExp -> Prop.

  Hypothesis var_case : forall S1 S2 S3 e x, P S1 S2 S3 e (DFVar x) (DFVar x) e.
  Hypothesis star_case : forall S2 S3 e, P nil S2 S3 e DStar DStar e.
  Hypothesis pi_case : forall L A B A' B' e e1 e2 S2 S3,
      (forall x, x \notin L ->
            sub2 nil S2 S3 (TFVar x) A' A e1 /\
            sub2 nil S2 ((x,e1) :: S3) (TApp e e1) (B ^ x) (B' ^ x) (open e2 (TFVar x))) ->
      (forall x, x \notin L ->
            P nil S2 S3  (TFVar x) A' A e1 /\
            P nil S2 ((x,e1) :: S3) (TApp e e1) (B ^ x) (B' ^ x) (open e2 (TFVar x))) ->
      P nil S2 S3 e (DPi A B) (DPi A' B') (TLam e2).
  Hypothesis lam_case : forall L e A B e' T D S2 S3,
      (forall x, x \notin L -> sub2 D ((x, T) :: S2) S3 (TCastdn e) (A ^ x) (B ^ x) e') ->
      (forall x, x \notin L -> P D ((x, T) :: S2) S3 (TCastdn e) (A ^ x) (B ^ x) e') ->
      P (T :: D) S2 S3 e (DLam A) (DLam B) (TCastup e').
  Hypothesis app_case : forall T e A B e' D S2 S3 ,
      sub2 (T :: D) S2 S3 e A B e' -> P (T :: D) S2 S3 e A B e' -> P D S2 S3 e (DApp A T) (DApp B T) e'.
  (* Hypothesis castdn_case : forall (e A B e' : DExp) S, *)
  (*     sub2 nil S e A B e' -> P nil S e A B e' -> P nil S e (DCastdn A) (DCastdn B) e'. *)
  (* Hypothesis castup_case : forall (e A B e' : DExp) S, *)
  (*     sub2 nil S e A B e' -> P nil S e A B e' -> P nil S e (DCastup A) (DCastup B) e'. *)
  (* Hypothesis sl1_case : forall (e A C e' B : DExp) S, *)
  (*     sub2 nil S e A C e' -> P nil S e A C e' -> P nil S e (DAnd A B) C e'. *)
  (* Hypothesis sl2_case : forall (e A C e' B : DExp) S, *)
  (*     sub2 nil S e B C e' -> P nil S e B C e' -> P nil S e (DAnd A B) C e'. *)
  (* Hypothesis sl3_case : forall (e A B C e1 e2 : DExp) S, *)
  (*     sub2 nil S e A B e1 -> *)
  (*     P nil S e A B e1 -> sub2 nil S e A C e2 -> P nil S e A C e2 -> P nil S e A (DAnd B C) (DMerge e1 e2). *)


  Fixpoint sub2_ind' (l : list DExp) (l0 : list (var * DExp)) (l1 : list (var * TExp)) (t : TExp) (d d0 : DExp) (t0 : TExp) (s : sub2 l l0 l1 t d d0 t0) {struct s} : P l l0 l1 t d d0 t0 :=
    match s in (sub2 l1 l2 l3 d3 d4 d5 d6) return (P l1 l2 l3 d3 d4 d5 d6) with
    | SVar S1 S2 S3 e x => var_case S1 S2 S3 e x
    | SStar S2 S3 e => star_case S2 S3 e
    | @SPi L A B A' B' e e1 e2 S0 S1 f =>
      @pi_case L A B A' B' e e1 e2 S0 S1 f
               (fun x (y : x \notin L) =>
                  match f x y with
                    conj t1 t2 => conj (sub2_ind' t1) (sub2_ind' t2)
                  end)


    | @SLam L e A B e' T D S0 S1 s0 => @lam_case L e A B e' T D S0 S1 s0
                                             (fun x (y : x \notin L) =>
                                                sub2_ind' (s0 x y))
    | @SApp T e A B e' D S0 S1  s0 => app_case s0 (sub2_ind' s0)
    (* | @SCastDown e A B e' S0 s0 => @castdn_case e A B e' S0 s0 (sub_ind' s0) *)
    (* | @SCastUp e A B e' S0 s0 => @castup_case e A B e' S0 s0 (sub_ind' s0) *)
    (* | @SL1 e A C e' B S0 s0 => @sl1_case e A C e' B S0 s0 (sub_ind' s0) *)
    (* | @SL2 e A C e' B S0 s0 => @sl2_case e A C e' B S0 s0 (sub_ind' s0) *)
    (* | @SL3 e A B C e1 e2 S0 s0 s1 => @sl3_case e A B C e1 e2 S0 s0 (sub_ind' s0) s1 (sub_ind' s1) *)

    end.

End sub_ind'.


Inductive elab_typing : sctx -> DExp -> DExp -> TExp -> Prop :=
| Ty3Star : forall SE,
    wfs2 SE ->
    elab_typing SE DStar DStar TStar
| Ty3Var : forall SE x ty,
    wfs2 SE ->
    binds x ty SE ->
    elab_typing SE (DFVar x) ty (TFVar x)
| Ty3Lam : forall L SE A B t t1 e,
    elab_typing SE (DPi A B) DStar e ->
    (forall x, x \notin L ->
          elab_typing (SE & x ~ A) (t ^ x) (B ^ x) (open t1 (TFVar x))) ->
    elab_typing SE (DLam t) (DPi A B) (TLam t1)
| Ty3App : forall SE E1 E2 A B e1 e2,
    elab_typing SE E1 (DPi A B) e1 ->
    elab_typing SE E2 A e2 ->
    elab_typing SE (DApp E1 E2) (B ^^ E2) (TApp e1 e2)
| Ty3Pi : forall L SE A B t1 t2,
    elab_typing SE A DStar t1 ->
    (forall x, x \notin L -> elab_typing (SE & x ~ A) (B ^ x) DStar (open t2 (TFVar x))) ->
    elab_typing SE (DPi A B) DStar (TPi t1 t2)
| Ty3And : forall SE A B t1 t2,
    elab_typing SE A DStar t1 ->
    elab_typing SE B DStar t2 ->
    elab_typing SE (DAnd A B) DStar (TProd t1 t2)
| Ty3CastDown : forall SE A B C a c,
    elab_typing SE A B a ->
    elab_typing SE C DStar c -> (* should c be existentially quantified? *)
    B ~~> C ->
    elab_typing SE (DCastdn A) C (TCastdn a)
| Ty3CastUp : forall SE A B C a b,
    elab_typing SE A C a ->
    elab_typing SE B DStar b ->
    B ~~> C ->
    elab_typing SE (DCastup A) B (TCastup a)
| Ty3Merge: forall SE E1 E2 A B e1 e2,
    elab_typing SE E1 A e1 ->
    elab_typing SE E2 B e2 ->
    elab_typing SE (DMerge E1 E2) (DAnd A B) (TPair e1 e2)
| Ty3Sub : forall SE A B C a a',
    elab_typing SE A B a ->
    sub2 nil nil nil a B C a' ->
    elab_typing SE A C a'

with wfs3 : sctx -> Prop :=
     | wfs3_nil : wfs3 empty
     | wfs3_cons : forall E x U e,
         x # E ->
         elab_typing E U DStar e ->
         wfs3 (E & x ~ U).


Inductive trans_ctx : env DExp -> env TExp -> Prop :=
| trans_nil : trans_ctx empty empty
| trans_cons : forall sctx tctx x T t,
    trans_ctx sctx tctx ->
    elab_typing sctx T DStar t ->
    trans_ctx (sctx & x ~ T) (tctx & x ~ t).


Axiom elab_unique : forall Gamma A C1 C2 t1 t2,
    elab_typing Gamma A C1 t1 ->
    elab_typing Gamma A C2 t2 ->
    t1 = t2.


Fixpoint substS (S : list (var * DExp)) (A : DExp) : DExp :=
  match S with
  | nil => A
  | (x, E) :: ES => substS ES ([x ~> E ]A)
  end.

Fixpoint substT (S : list (var * TExp)) (A : TExp) : TExp :=
  match S with
  | nil => A
  | (x, E) :: ES => substT ES ([x |~> E ] A) 
  end.

Inductive Result : list DExp -> list (var * DExp) -> list (var * TExp) -> TExp -> DExp -> DExp -> TExp -> Prop :=
| RBNil : forall e e' A B S2 S3,
    (forall Gamma Gamma' a b,
        trans_ctx Gamma Gamma' ->
        elab_typing Gamma (substS S2 A) DStar a ->
        elab_typing Gamma (substS S2 B) DStar b ->
        has_type Gamma' e ((*substT S3*) a) -> (*has_type Gamma' e' b*)
        has_type Gamma' e' ((*substT S3*) b)) ->
    Result nil S2 S3 e A B e'
| RFVar : forall x e T D S2 S3,
    Result (T :: D) S2 S3 e (DFVar x) (DFVar x) e
| RLam : forall L e e' B C T D S2 S3,
    (forall x, x \notin L -> Result D ((x, T) :: S2) S3 (TCastdn e) (B ^ x) (C ^ x) e') ->
    Result (T :: D) S2 S3 e (DLam B) (DLam C) (TCastup e')
| RApp : forall e e' B C D (S2 : list (var * DExp)) S3 (E T : DExp),
    Result (E :: T :: D) S2 S3 e B C e' -> Result (T :: D) S2 S3 e (DApp B E) (DApp C E) e'.

Fixpoint apps A D : DExp :=
  match D with
  | nil => A
  | T :: TS => apps (DApp A T) TS
  end.


Lemma list_ass : forall {A a} (D1 : list A) {D2}, (a :: D1) ++ D2 = a :: (D1 ++ D2).
  intros.
  rewrite (app_comm_cons D1 D2). auto.
Defined.

Lemma reduction_consistency : forall {A C}, A ~~> C -> forall {Gamma a c B}, elab_typing Gamma A B a -> elab_typing Gamma C B c -> a --> c.
  intros A C A2C. induction A2C; intros.
  Admitted.

Lemma red_subst : forall {a c S}, a --> c -> substT S a --> substT S c.
  Admitted.

(*
Lemma foo : forall A S1 S2 S3 e, sub2 S1 S2 S3 e A A e -> substT S3 e = e.
  induction A; intros.
*)   


Lemma apps_lemma : forall {D2 D1 S2 S3 E A B E'},
    sub2 (D1 ++ D2) S2 S3 E A B E' -> Result (D1 ++ D2) S2 S3 E A B E' -> Result D2 S2 S3 E (apps A D1) (apps B D1) E'.
Proof.
  destruct D2; intros.
  rewrite (app_nil_r D1) in H, H0.
  induction H0.
  (* Base case *)
  simpl. apply RBNil. auto.
  (* Var *)
  simpl. apply RBNil. intros.
  lets : (elab_unique H1 H2). subst. auto. (* admit.*)
  (* Lam case *)
  inverts H.
  pick_fresh x.
  assert (x \notin L0) by auto.
  lets : H7 H; clear H7.
  assert (x \notin L) by auto.
  lets : H1 H3 H2; clear H1.
  inverts H4.
  apply RBNil; intros.
  assert (substS S2 (apps (DLam B) (T :: D)) ~~> substS ((x, T) :: S2) (apps (B ^ x) D)). admit. (* should be derived from beta-reduction *)
  assert (exists c, elab_typing Gamma (substS ((x, T) :: S2) (apps (B ^ x) D)) DStar c). admit. (* I think this can be derived from the substitution lemma *)
  assert (substS S2 (apps (DLam C) (T :: D)) ~~> substS ((x, T) :: S2) (apps (C ^ x) D)). admit. (* should be derived from beta-reduction *)
  assert (exists c, elab_typing Gamma (substS ((x, T) :: S2) (apps (C ^ x) D)) DStar c). admit. (* I think this can be derived from the substitution lemma *)
  destruct H9. destruct H11.
  (*assert (elab_typing Gamma (substS ((x, T) :: S) (apps (B ^ x) D)) DStar a).*)
(*
pose (@TyTCastDown _ _ (substT S3 x0) _ H7).
  apply TyTCastUp with (t2 := (substT S3 x1)).
  assert (substT S3 a --> substT S3 x0). apply (red_subst (reduction_consistency H8 H5 H9)). *)
  pose (@TyTCastDown _ _ x0 _ H7).
  apply TyTCastUp with (t2 := x1).
  assert (a --> x0). apply (reduction_consistency H8 H5 H9).
  apply (H1 _ _ _ _ H4 H9 H11 (h H12)).
  (* pply (red_subst (reduction_consistency H10 H6 H11)). *)
  apply (reduction_consistency H10 H6 H11).
  (* App case *)
  inversion H; subst. apply IHResult in H9. simpl. simpl in H9. auto.
  (* Inductive case *)
  generalize H H0. clear H H0. generalize S2 S3 E A B E' d. clear d S2 S3 E A B E'.
  induction D1; simpl; intros.
  auto.
  apply IHD1. apply SApp. auto.
  destruct D1. simpl in H0. simpl. apply RApp. auto.
  rewrite (list_ass D1). apply RApp.
  rewrite (list_ass D1) in H0. auto.
Qed.

Lemma subst_pi : forall {S3 x x0}, substT S3 (TPi x x0) = TPi (substT S3 x) (substT S3 x0).
  Admitted.

Lemma sub_gen : forall {e e' B C D S2 S3}, sub2 D S2 S3 e B C e' -> Result D S2 S3 e B C e'.
Proof.
  intros.
  induction H using sub2_ind'.

  (* Var *)
  destruct S1.
  apply RBNil.
  intros.
  lets : elab_unique H0 H1. subst. auto.
  apply RFVar.

  (* Star *)
  apply RBNil. intros.
  lets : elab_unique H0 H1. subst. auto.

  (* Pi TODO *)
  apply RBNil. intros.
  assert (exists C D, b = TPi C D). admit. (* we should have an inversion lemma for H3 *)
  assert (exists C D, a = TPi C D). admit. (* we should have an inversion lemma for H5 *)
  destruct H5. destruct H5. subst.
  destruct H6. destruct H5. subst.
  (* begin: simplify reasoning for now *)
  assert (forall E, substS S2 E = E). admit.
  (*assert (S3 = nil). admit. subst. simpl.*)
  rewrite (H5 _) in H2. rewrite (H5 _) in H3. clear H5. simpl in H4.
  (* end: simplify *)
  inversion H3; subst. inversion H2; subst.  
  (*rewrite subst_pi. *)
  apply_fresh TyTLam as y.
  assert (y \notin L) by auto.
  assert (y \notin L0) by auto.
  assert (y \notin L1) by auto.
  pose (H y H5). pose (H0 y H5).
  destruct a, a0.
  assert (elab_typing (Gamma & y ~ A') (B' ^ y) DStar (open x0 (TFVar y))) by (apply (H11 y H6)).
  assert (elab_typing (Gamma & y ~ A) (B ^ y) DStar (open x2 (TFVar y))) by (apply (H13 y H7)).
  clear H H0 H5 H6 H7 H11 H13 Fry L L1 L0. (* study more at this point *)
  inversion H14; subst. inversion H15; subst. clear H14 H15.
  (* begin: simplify more *)
  assert (forall E, substS S2 E = E). admit.
  rewrite (H5 _) in H. rewrite (H5 _) in H. rewrite (H5 _) in H0. rewrite (H5 _) in H0. clear H5.
  (* end: simplify more *)
  (*assert (open x2 (TFVar y) = open x2 e1). (* I think this is what we should have *)
  admit. rewrite H5 in H17. clear H5. *)

(*  assert (x0 $ y = [y |~> e1] (x0 $ y)). admit. rewrite H5. clear H5. *)

  assert (F : elab_typing (Gamma & y ~ A') ((B ^ y)) DStar ([y |~> e1] (x2 $ y))). admit.

  (*apply (H0 (Gamma & y ~ A') _  (open x2 (TFVar y)) _). *)

  apply (H0 (Gamma & y ~ A') _  ([y |~> e1] (x2 $ y)) _).

  apply trans_cons; auto. auto. (* elaboration still holds when the environment contains subtypes *)
  auto.
  (* assert (substT ((y, e1) :: nil) (open x2 (TFVar y)) = open x2 e1). admit. simpl in H5. rewrite H5. clear H5.*)
  assert ([y |~> e1] x2 $ y = open x2 e1). admit. (* should be trivial *) simpl in H5. rewrite H5. clear H5.
  apply TyTApp with (a := x1). admit. (* weakening *)
  assert (elab_typing (Gamma & y ~ A') A' DStar x).
  admit. (*weakening*)
  assert (elab_typing (Gamma & y ~ A') A DStar x1).
  admit. (*weakening*)
  assert (has_type (Gamma' & y ~ x) (TFVar y) x).
  apply TyTVar. admit. auto.
  apply (H _ _ _ _ (@trans_cons _ _ _ _ _ H1 H10) H5 H6 H7).
  (* Subsumption cases: should not exists with bi-directional type-checking*)
  admit. admit.
  (* Lam *)
  apply_fresh RLam as x.
  apply H0; auto.

  (* App *)
  assert (forall A, DApp A T = apps A (T :: nil)). intros. auto.
  rewrite (H0 A). rewrite (H0 B). clear H0.
  apply apps_lemma. rewrite (list_ass nil). simpl. auto.
  rewrite (list_ass nil). simpl. auto.
Qed.

Lemma main : forall Gamma Gamma' A B e e' a b,
    sub2 nil nil nil e A B e' ->
    elab_typing Gamma A DStar a ->
    elab_typing Gamma B DStar b ->
    trans_ctx Gamma Gamma' ->
    has_type Gamma' e a ->
    has_type Gamma' e' b.
Proof.
  intros.
  pose (Res := sub_gen H).
  inverts Res.
  apply* H4.
Defined.

(*
---------------------------------------------------

---------------------------------------------------------------------------------
nil nil {} x <| * <: * |> e1       nil nil {a -> x; a -> e1} (id x) <| a -> a <: a -> a |>  
-----------------------------------------------------------------
nil nil {} id <| Pi (a : *) . a -> a <: Pi (a : *) . a -> a |> \x .

x : *

    id x : (a -> a) [a -> x] = x -> x

---------------------------------------------------------------------------------
nil nil {} y <| A' <: A |> e1       nil nil {a -> x} (e e1) <| B <: B' |> e2  
-----------------------------------------------------------------
nil nil {} id <| Pi (a : *) . a -> a <: Pi (a : *) . a -> a |> \x .

e2 will contain y. 


. |- a <|  A' <: A  |> E1             . |- E E1 <|  B <: B' |> E2
----------------------------------------------------  SPi
. |- E <|  forall (a : A). B <: forall (a : A') . B'  |> \a . E2

*)