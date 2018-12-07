Set Implicit Arguments.
Require Import LibLN definitions infrastructure.
Require Import List.


(* Simple optimization rules *)
Definition simplify (e : TExp) :=
  match e with
    | TLam (TApp e' (TBVar 0)) => e'  (* eta-contraction *)
    | TCastup (TCastdn e') => e'      (* cast elimination *)
    | e => e
  end.

(* Incomplete *)
Inductive sub : list DExp -> list (var * DExp) -> TExp -> DExp -> DExp -> TExp -> Prop :=
| SVar : forall S1 S2 e x, sub S1 S2 e (DFVar x) (DFVar x) e
| SStar : forall S e, sub nil S e DStar DStar e
| SPi : forall L A B A' B' e e1 e2 S,
    (forall x, x \notin L ->
          sub nil S (TBVar 0) A' A e1 /\
          sub nil S (TApp e e1) (B ^ x) (B' ^ x) e2) ->
    sub nil S e (DPi A B) (DPi A' B') (simplify (TLam e2))
| SLam: forall L e A B e' T D S,
    (forall x, x \notin L -> sub D ((x, T) :: S) (TCastdn e) (A ^ x) (B ^ x) e') ->
    sub (T :: D) S e (DLam A) (DLam B) (simplify (TCastup e'))
| SApp: forall T A B e e' D S,
    sub (T :: D) S e A B e' -> sub D S e (DApp A T) (DApp B T) e'
(* | SCastDown: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastdn A) (DCastdn B) e' *)
(* | SCastUp: forall e A B e' S, *)
(*     sub nil S e A B e' -> sub nil S e (DCastup A) (DCastup B) e' *)
| SL1: forall A C e e' B S,
    sub nil S (TFst e) A C e' -> sub nil S e (DAnd A B) C e'
| SL2: forall A C e e' B S,
    sub nil S (TSnd e) B C e' -> sub nil S e (DAnd A B) C e'
| SL3 : forall A B C e e1 e2 S, not (A = DAnd B C) ->
          sub nil S e A B e1 -> sub nil S e A C e2 -> sub nil S e A (DAnd B C) (TPair e1 e2)
| SL3EQ : forall S B C e, sub nil S e (DAnd B C) (DAnd B C) e.

Hint Constructors sub.

(* Customised induction principle *)
Section sub_ind'.

  Variable P : list DExp -> list (var * DExp) -> TExp -> DExp -> DExp -> TExp -> Prop.

  Hypothesis var_case : forall S1 S2 e x, P S1 S2 e (DFVar x) (DFVar x) e.
  Hypothesis star_case : forall S e, P nil S e DStar DStar e.
  Hypothesis pi_case : forall L A B A' B' e e1 e2 S,
      (forall x, x \notin L ->
            sub nil S (TBVar 0) A' A e1 /\
            sub nil S (TApp e e1) (B ^ x) (B' ^ x) e2) ->
      (forall x, x \notin L ->
            P nil S (TBVar 0) A' A e1 /\
            P nil S (TApp e e1) (B ^ x) (B' ^ x) e2) ->
      P nil S e (DPi A B) (DPi A' B') (simplify (TLam e2)).
  Hypothesis lam_case : forall L e A B e' T D S,
      (forall x, x \notin L -> sub D ((x, T) :: S) (TCastdn e) (A ^ x) (B ^ x) e') ->
      (forall x, x \notin L -> P D ((x, T) :: S) (TCastdn e) (A ^ x) (B ^ x) e') ->
      P (T :: D) S e (DLam A) (DLam B) (simplify (TCastup e')).
  Hypothesis app_case : forall T e A B e' D S,
      sub (T :: D) S e A B e' -> P (T :: D) S e A B e' -> P D S e (DApp A T) (DApp B T) e'.
  (* Hypothesis castdn_case : forall (e A B e' : DExp) S, *)
  (*     sub nil S e A B e' -> P nil S e A B e' -> P nil S e (DCastdn A) (DCastdn B) e'. *)
  (* Hypothesis castup_case : forall (e A B e' : DExp) S, *)
  (*     sub nil S e A B e' -> P nil S e A B e' -> P nil S e (DCastup A) (DCastup B) e'. *)
  Hypothesis sl1_case : forall A C e e' B S,
      sub nil S (TFst e) A C e' -> P nil S (TFst e) A C e' -> P nil S e (DAnd A B) C e'.
  Hypothesis sl2_case : forall A C e e' B S,
      sub nil S (TSnd e) B C e' -> P nil S (TSnd e) B C e' -> P nil S e (DAnd A B) C e'.
  Hypothesis sl3_case : forall A B C e e1 e2 S, not (A = DAnd B C) ->
      sub nil S e A B e1 ->
      P nil S e A B e1 -> sub nil S e A C e2 -> P nil S e A C e2 -> P nil S e A (DAnd B C) (TPair e1 e2).
  Hypothesis sl3_case_eq : forall S B C e, P nil S e (DAnd B C) (DAnd B C) e.

  Fixpoint sub_ind' (l : list DExp) (l0 : list (var * DExp)) (t : TExp) (d d0 : DExp) (t0 : TExp) (s : sub l l0 t d d0 t0) {struct s} : P l l0 t d d0 t0 :=
    match s in (sub l1 l2 d3 d4 d5 d6) return (P l1 l2 d3 d4 d5 d6) with
    | SVar S1 S2 e x => var_case S1 S2 e x
    | SStar S0 e => star_case S0 e
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
    | @SL1 A C e e' B S0 s0 => @sl1_case A C e e' B S0 s0 (sub_ind' s0)
    | @SL2 A C e e' B S0 s0 => @sl2_case A C e e' B S0 s0 (sub_ind' s0)
    | @SL3 e A B C e1 e2 eq S0 s0 s1 => @sl3_case e A B C e1 e2 eq S0 s0 (sub_ind' s0) s1 (sub_ind' s1)
    | @SL3EQ s B C e =>  @sl3_case_eq s B C e
    end.

End sub_ind'.


Inductive Relate : DExp -> list DExp -> list (var * DExp) -> Prop :=
| RVar : forall x S1 S2, Relate (DFVar x) S1 S2
| RStar : forall S, Relate DStar nil S
| RPi : forall L S A B, Relate A nil S -> (forall x, x \notin L -> Relate (B ^ x) nil S) ->
                      Relate (DPi A B) nil S
| RLam : forall L A T D S, (forall x, x \notin L -> Relate (A ^ x) D ((x, T) :: S)) ->
                         Relate (DLam A) (T :: D) S
| RApp : forall A T D S, Relate A (T :: D) S -> Relate (DApp A T) D S
| RL : forall A B S, Relate A nil S \/ Relate B nil S -> Relate (DAnd A B) nil S.


(*
Definition spi_eq : forall A B e S, sub nil S e (DPi A B) (DPi A B) e.
  intros. assert (sub nil S e (DPi A B) (DPi A B) (simplify (TLam ((TApp e (TBVar 0)))))).
  apply_fresh SPi as x. split.
  simpl. auto.
  rewrite <- H.
*)

(* Maybe this is not needed? *)

Lemma rel_typ_sub : forall {S1 S2 e A B e'}, sub S1 S2 e A B e' ->
                    forall {Gamma1 Gamma2 m1 m2 T1 T2 r1 r2}, elab_typing_alg Gamma1 A m1 T1 r1 ->
                                            elab_typing_alg Gamma2 B m2 T2 r2 ->
                                            Relate A S1 S2 /\ Relate B S1 S2.
  intros S1 S2 e A B e' s. induction s using sub_ind'; intros.
  (* Var and Star *)
  split; apply RVar.
  split; apply RStar.
  (* Pi *)
  split; apply_fresh RPi as x.
  pick_fresh x.
  assert (x \notin L) by auto.
  destruct (H x H3). destruct (H0 x H3). clear H H0 Fr.
  inversion H1; inversion H2; subst. apply* H6.
  inversion H16; subst. apply* H6.
  inversion H8; subst. apply* H6.
  inversion H8; inversion H17; subst. apply* H6.
  admit. admit. admit. (* some boring and similar proof to the previous case *)
  (* Lam *)
  inversion H1; inversion H2; subst; split; apply_fresh RLam as x; assert (x \notin L) by auto.
  assert (x \notin L0) by auto. assert (x \notin L1) by auto. clear Frx.
  pose (H6 x H5). pose (H13 x H7).
  destruct (H0 x H3 (Gamma1 & x ~ A0) (Gamma2 & x ~ A1) Chk Chk (B0 ^ x) (B1 ^ x) _ _ e2 e3).
  auto.
  admit. admit. admit. admit. admit. admit. admit. (* lots of boring similar cases *)
  (* App *)
  inversion H; inversion H0; subst; split; apply RApp.
  apply (IHs _ _ _ _ _ _ _ _ H4 H12).
  apply (IHs _ _ _ _ _ _ _ _ H4 H12).
  admit. admit. admit. admit. admit. admit. (* lots of boring similar cases *)
  (* And *)
  inversion H; subst; split. apply RL. left.
  apply (IHs _ _ _ _ _ _ _ _ H4 H0).
  apply (IHs _ _ _ _ _ _ _ _ H4 H0).
  (* more boring cases *)
Admitted.

Lemma sub_refl_aux : forall A S1 S2, Relate A S1 S2 -> forall e, sub S1 S2 e A A e.
Proof.
  intros A S1 S2 r. induction r; intros; try auto.
  (* Pi case *)
  assert (sub nil S e (DPi A B) (DPi A B) (simplify (TLam (TApp e (TBVar 0))))).
  apply_fresh SPi as x.
  assert (x \notin L) by auto. pose (H x H1). pose (H0 x H1).
  split*.
  simpl in H1.
  apply H1.
  (* Lam case *)
  assert (sub (T :: D) S e (DLam A) (DLam A) (simplify (TCastup (TCastdn e )))).
  apply_fresh SLam as x.
  assert (x \notin L) by auto.
  apply (H0 x H1).
  apply H1.
Admitted.

Require Import Program.Equality.

Lemma bar : forall A Gamma, elab_typing_alg Gamma A Inf DStar TStar -> Relate A nil nil.
  induction A; intros; try (inversion H).
  apply RStar.
  admit. (* Need to add the annotation case *)
Admitted.

(* If A is well-formed (i.e. it is a type), then subtyping is reflexive *)

Lemma sub_refl : forall Gamma A, elab_typing_alg Gamma A Inf DStar TStar -> forall e, sub nil nil e A A e.
  intros.
  assert (Relate A nil nil). apply* bar.
  apply* sub_refl_aux.
Defined.


