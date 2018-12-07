Set Implicit Arguments.
Require Import LibLN definitions infrastructure.
Require Import List.

(*

Discuss

0. substitution
1. the changed subtyping breaks transitivity, ref FIXME_STAR, FIXME_LAM
2. transitivity of pi case is broken, ref FIXME_PI
3. some beta equality needed (e.g TFst (TPair e1 e2) = e1, e = TCastdn (TCastup e)
4. subtyping pi


 *)

Lemma invAnd : forall t S1 S2 t1 t2,
    usubM S1 S2 t (DAnd t1 t2) ->
    usubM S1 S2 t t1 /\ usubM S1 S2 t t2.
Proof.
  introv Ty.
  lets [W ?] : regular_usubM Ty.
  gen S1 S2 t1 t2.
  induction W; introv Ty; split; inverts* Ty.

  apply* USL1M.
  lets* : IHW1 H6.
  apply* USL2M.
  lets* : IHW2 H6.

  apply* USL1M.
  lets* : IHW1 H6.
  apply* USL2M.
  lets* : IHW2 H6.
Qed.


Ltac doAll :=
  match goal with
  | [ IH : sterm ?t1 -> _ , H : usubM nil _ ?t1 _ , SSubQ : usubM nil _ _ (DAnd _ _) |- _ ] =>
    apply* IH; lets~ [? ?]: invAnd SSubQ
  end.


Lemma sub_trans : forall Q S G S1 S2,
  usubM S1 S2 S Q -> usubM S1 S2 Q G -> usubM S1 S2 S G.
Proof.
  introv SSubQ QSubG.
  lets [TrmS TrmQ]: regular_usubM SSubQ.
  lets [? TrmG]: regular_usubM QSubG.

  gen S G S1 S2.
  induction TrmQ.

  (* Star *)
  - introv TrmS TrmG. gen S.
    induction TrmG; introv TrmS SSubQ QSubG; inverts* QSubG.

  (* Var *)
  - introv TrmS TrmG. gen S.
    induction TrmG; introv TrmS SSubQ QSubG; inverts* QSubG.

  (* Lam *)
  - introv TrmS.
    induction TrmS; introv TrmG SSubQ; gen G; inverts* SSubQ.

    (* lam <= lam *)
    introv TrmG.
    induction TrmG; introv QSubG; inverts* QSubG.
    apply_fresh USLamM as y.
    apply* H1.

  (* App *)
  - introv TrmS.
    induction TrmS; introv TrmG SSubQ; gen G; inverts* SSubQ.

    (* app <= app *)
    introv TrmG.
    induction TrmG; introv QSubG; inverts* QSubG.


  (* Castup *)
  - introv TrmS.
    induction TrmS; introv TrmG SSubQ; gen G; inverts* SSubQ.

  (* Castdown *)
  - introv TrmS.
    induction TrmS; introv TrmG SSubQ; gen G; inverts* SSubQ.

  (* Pi *)
  - introv TrmS.
    induction TrmS; introv TrmG SSubQ; gen G; inverts* SSubQ.

    introv TrmG.
    induction TrmG; introv QSubG; inverts* QSubG.
    apply_fresh USPiM as x.
    forwards~ : H13 x.
    forwards~ : H9 x.
    apply* H1.
    apply* IHTrmQ.

  (* And *)
  - introv TrmS TrmG. gen S.
    induction TrmG; introv TrmS SSubQ QSubG; inverts* QSubG; doAll.

    (* missing subtyping merge and ann *)

Admitted.



(* (* *)
(* Incomplete, we need subtyping produces closed terms *)
(*  *) *)
(* Inductive type : DExp -> Prop := *)
(* | sterm_star : type DStar *)
(* | sterm_var : forall x, type (DFVar x) *)
(* | sterm_lam : forall L t1, *)
(*     (forall x, x \notin L -> type (t1 ^ x)) -> *)
(*     type (DLam t1) *)
(* | sterm_app : forall t1 t2, *)
(*     type t1 -> type t2 -> type (DApp t1 t2) *)
(* | sterm_pi : forall L t1 t2, *)
(*     type t1 -> *)
(*     (forall x, x \notin L -> type (t2 ^ x)) -> *)
(*     type (DPi t1 t2) *)
(* | sterm_inter : forall t1 t2, *)
(*     type t1 -> type t2 -> type (DAnd t1 t2). *)


(* Hint Extern 1 (type ?t) => match goal with *)
(*   | H: sub _ _ _ t _ _ |- _ => apply (proj1 (regular_subtyping H)) *)
(*   | H: sub _ _ _ _ t _ |- _ => apply (proj2 (regular_subtyping H)) *)
(*   end. *)

(* Lemma invAnd : forall t S1 S2 e t1 t2 e', *)
(*     sub S1 S2 e t (DAnd t1 t2) e' -> *)
(*     sub S1 S2 e t t1 (TFst e') /\ sub S1 S2 e t t2 (TSnd e'). *)
(* Proof. *)
(*   introv Ty. *)
(*   asserts* W: (type t). gen S1 S2 e t1 t2 e'. *)
(*   induction W; introv Ty; split. *)

(*   inversions Ty. *)
(*   asserts_rewrite* ((TFst (TPair e1 e2) = e1)). admit. *)
(*   inversion Ty. *)
(*   asserts_rewrite* ((TSnd (TPair e1 e2) = e2)). admit. *)

(*   inversions Ty. *)
(*   asserts_rewrite* ((TFst (TPair e1 e2) = e1)). admit. *)
(*   inversion Ty. *)
(*   asserts_rewrite* ((TSnd (TPair e1 e2) = e2)). admit. *)


(*   inversions Ty. *)
(*   asserts_rewrite* ((TFst (TPair e1 e2) = e1)). admit. *)
(*   inversion Ty. *)
(*   asserts_rewrite* ((TSnd (TPair e1 e2) = e2)). admit. *)


(*   inversions Ty. *)
(*   asserts_rewrite* ((TFst (TPair e1 e2) = e1)). admit. *)
(*   inversion Ty. *)
(*   asserts_rewrite* ((TSnd (TPair e1 e2) = e2)). admit. *)

(*   inversions Ty. *)
(*   asserts_rewrite* ((TFst (TPair e1 e2) = e1)). admit. *)
(*   inversion Ty. *)
(*   asserts_rewrite* ((TSnd (TPair e1 e2) = e2)). admit. *)

(*   inversion Ty; subst. *)
(*   apply SL1. *)
(*   lets* : IHW1 H6. *)
(*   apply SL2. *)
(*   lets* : IHW2 H6. *)
(*   asserts_rewrite* ((TFst (TPair e1 e2) = e1)). admit. *)
(*   (* apply SL1. admit. (* t0 is a type, should hold as per refl*) *) *)

(*   inversions Ty. *)
(*   apply SL1. *)
(*   lets* : IHW1 H6. *)
(*   apply SL2. *)
(*   lets* : IHW2 H6. *)
(*   asserts_rewrite* ((TSnd (TPair e1 e2) = e2)). admit. *)
(*   (* apply SL2. admit. (* t0 is a type, should hold as per refl *) *) *)
(* Admitted. *)


(* Lemma sub_trans : forall Q S G S1 S2 e e' e'', *)
(*   sub S1 S2 e S Q e' -> sub S1 S2 e' Q G e'' -> sub S1 S2 e S G e''. *)
(* Proof. *)
(*   introv SSubQ QSubG. *)
(*   asserts* TQ: (type Q). *)
(*   asserts* TS: (type S). *)
(*   asserts* TG: (type G). *)

(*   gen S G S1 S2 e e' e''. *)
(*   induction TQ. *)


(*   (* Star *) *)
(*   - introv TS TG. gen S. *)
(*     induction TG; introv TS SSubQ QSubG; inversions QSubG; auto. *)


(*     (* FIXME_STAR *)

(*     Cuonter example *)

(*     e <| * & * <= * |> fst e *)
(*     fst e <| * <= * & * |> (fst e, fst e) *)

(*     e <| * & * <= * & * |> (fst e, fst e) *)


(*     disjointness should avoid that *)

(*      *) *)

(*     case_if_eq S (DAnd t1 t2). admit. *)
(*     apply* SL3. *)

(*   (* Var *) *)
(*   - introv TS TG. gen S. *)
(*     induction TG; introv TS SSubQ QSubG; inversions QSubG; auto. *)

(*     (* Counter example as Star case *) *)
(*     case_if_eq S (DAnd t1 t2). admit. *)
(*     apply* SL3. *)

(*   (* Lam *) *)
(*   - introv TS. *)
(*     induction TS; introv TG SSubQ; gen G; inversions SSubQ; auto. *)

(*     (* lam <= lam *) *)
(*     introv TG. *)
(*     induction TG; introv QSubG; inversions QSubG. *)
(*     apply_fresh SLam as x. *)
(*     apply~ H0. *)
(*     asserts_rewrite~ (e'0 = TCastdn (TCastup e'0)). admit. *)
(*     (* admit.                      (* FIXME_LAM, see H13 *) *) *)

(*     (* and <= lam *) *)
(*     intros. apply* SL1. intros. apply* SL2. *)

(*   (* App *) *)
(*   - introv TS. *)
(*     induction TS; introv TG SSubQ; gen G; inversions SSubQ; auto. *)

(*     (* app <= app *) *)
(*     introv TG. *)
(*     induction TG; introv QSubG; inversions QSubG. *)
(*     apply* SApp. *)
(*     apply* SL3. *)
(*     (* Changed *) *)
(*     (* intros RR. *) *)
(*     (* inversion RR. *) *)

(*     (* and <= app *) *)
(*     intros. apply* SL1. intros. apply* SL2. *)

(*   (* Pi *) *)
(*   - introv TS. *)
(*     induction TS; introv TG SSubQ; gen G; inversions SSubQ; auto. *)

(*     (* pi <= pi *) *)
(*     introv TG. *)
(*     induction TG; introv QSubG; inversions QSubG. *)
(*     apply_fresh SPi as x. *)
(*     forwards~ [t4Subt1 t2Subt5] : H13 x. *)
(*     forwards~ [t1Subt0 t3Subt2] : H11 x. *)
(*     split. *)
(*     apply~ IHTQ. exact t4Subt1. *)
(*     (* FIXME_PI: look at t1Subt0, we only have x <| t1 <= t0 |> e1 *) *)
(*     admit. *)
(*     apply~ H0. exact t3Subt2. *)
(*     (* look at t2Subt5 *) *)
(*     admit. *)

(*     (* pi <= and *) *)
(*     apply* SL3. *)
(*     (* Changed *) *)
(*     (* intros RR. *) *)
(*     (* inversion RR. *) *)

(*     (* and <= pi *) *)
(*     intros. apply* SL1. intros. apply* SL2. *)

(*   (* And *) *)
(*   - introv TS W. gen S. *)
(*     induction W; introv TS SSubQ QSubG; inversions QSubG; *)
(*       try ((apply IHTQ1 with (e' := TFst e'); auto; apply* invAnd || fail) || *)
(*            (apply IHTQ2 with (e' := TSnd e'); auto; apply* invAnd || fail)); auto. *)

(*       (* FIXME: wrong *) *)
(*       (* case_if_eq S (DAnd t0 t3). admit. *) *)
(*       apply* SL3. *)

(* Admitted. *)
