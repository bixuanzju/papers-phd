Require Import definitions.
Require Import refl_trans.
Require Import typing.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

(* translation of context, declarative version *)

Module Sound_Complete
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

Module M := ExprDefs VarTyp set.
Export M.

Module N := SubTyping VarTyp set.
Export N.

Module S := Typing VarTyp set.
Export S.



Fixpoint trans_ctx (c : context AExp) : context SExp :=
  match c with
    | nil => nil
    | (v, t) :: s => (v, erase t) :: trans_ctx s
  end.


Lemma l0 : forall v a s, In v (dom (a :: s)) -> v == fst a \/ In v (dom (A:=SExp) s).
  intros.
  unfold dom in H.
  fold (dom (A:=SExp) s) in H.
  apply add_spec in H.
  auto.
Qed.


Lemma l1 : forall v G, In v (dom (trans_ctx G)) -> In v (dom G).
  intros.
  induction G.
  -
    simpl in H.
    auto.
  -
    unfold trans_ctx in H.
    fold trans_ctx in H.
    destruct a.
    apply l0 in H.
    inversion H.
    simpl in H0.
    unfold dom. simpl.
    fold (dom (A:=AExp)).
    apply add_spec. auto.
    apply IHG in H0.
    unfold dom. simpl.
    fold (dom (A:=AExp)).
    apply add_spec. auto.
Qed.


Lemma ok_gamma : forall G, ok G -> ok (trans_ctx G).
  intros.
  induction G.
  unfold trans_ctx. simpl. auto.
  inversion H. subst.
  apply IHG in H2.
  unfold trans_ctx.
  fold trans_ctx.
  simpl.
  apply Ok_push. auto.
  unfold not.
  intros.
  apply H3.
  apply l1. auto.
Qed.


Lemma in_gamma : forall x T Gamma, List.In (x, T) Gamma -> List.In (x, erase T) (trans_ctx Gamma).
  intros.
  induction Gamma.
  inversion H.
  destruct a.
  inversion H.
  unfold trans_ctx.
  fold trans_ctx.
  unfold List.In.
  inversion H0. auto.
  apply IHGamma in H0.
  unfold trans_ctx.
  fold trans_ctx.
  apply in_cons. auto.
Qed.


(* Typing soundness *)
Theorem typing_sound:
  forall Gamma E D T t,
    has_type_source_alg Gamma E D T t -> has_type_source (trans_ctx Gamma) (erase E) (erase T) t.
Proof.
  intros.
  inversion H; simpl; auto; subst.

  -
    inversion H. subst.
    unfold has_type_source.
    exists AStar.
    apply DTyStar.
    apply ok_gamma. auto.

  -
    apply in_gamma in H1.
    apply ok_gamma in H0.
    pose (DTyVar (trans_ctx Gamma) x (erase T) H0 H1).
    exists (AFVar x). auto.

  -
    inversion H0; subst.
    simpl.


Abort.