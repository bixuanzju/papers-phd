Require Import definitions.

Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module SubTyping
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  Module M := ExprDefs VarTyp set.
  Export M.

  (* asuume locally-closed terms have subtyping relation *)
  (* Source-to-target *)
  Inductive sub2 : TExp -> DExp -> DExp -> TExp -> Prop :=
  | svar : forall e x, sub2 e (DBVar x) (DBVar x) e
  | sstar : forall e, sub2 e DStar DStar e
  (* not sure if (TBVar 0) suitable  *)
  | spi : forall A A' B B' e e1 e2,
      sub2 (TBVar 0) A' A e1 -> sub2 (TApp e e1) B B' e2 -> sub2 e (DPi A B) (DPi A' B') (TLam e2)
  | slam : forall e A B e',
      sub2 (TCastdn e) A B e' -> sub2 e (DLam A) (DLam B) (TCastup e')
  | sapp : forall A B E e e',
      sub2 e A B e' -> sub2 e (DApp A E) (DApp B E) e'
  | scastdn : forall e A B e',
      sub2 e A B e' -> sub2 e (DCastdn A) (DCastdn B) e'
  | scastup : forall e A B e',
      sub2 e A B e' -> sub2 e (DCastup A) (DCastup B) e'
  | sand1 : forall A B C e e',
      sub2 (TFst e) A C e' -> sub2 e (DAnd A B) C e'
  | sand2 : forall A B C e e',
      sub2 (TSnd e) B C e' -> sub2 e (DAnd A B) C e'
  | snad3 : forall A B C e e1 e2,
      sub2 e A B e1 -> sub2 e A C e2 -> sub2 e A C e2 -> sub2 e A (DAnd B C) (TPair e1 e2).


  Definition ArgStack := list DExp.


  (* asuume locally-closed terms have subtyping relation *)

  (* ------------------ *)
  (* D |- E <|  A <: B  |> E'       term E : A D produces term E' : B D   *)
  (* ------------------ *)

  Inductive sub : ArgStack -> DExp -> DExp -> DExp -> DExp -> Prop :=
  | SVar : forall D E x, sub D E (DBVar x) (DBVar x) E
  | SStar : forall E, sub nil E DStar DStar E
  (* Not correct *)
  | SPi : forall A B A' B' E E1 E2,
      sub nil (DBVar 0) A' A E1 -> sub nil (DApp E E1) B B' E2 -> sub nil E (DPi A B) (DPi A' B') (DLam E2)
  | SLam: forall D T E A B E',
      sub D (DCastdn E) A B E' -> sub (T :: D) E (DLam A) (DLam B) (DCastup E')
  | SApp: forall D T E A B E',
      sub (T :: D) E A B E' -> sub D E (DApp A T) (DApp B T) E'
  | SCastDown: forall E A B E',
      sub nil E A B E' -> sub nil E (DCastdn A) (DCastdn B) E'
  | SCastUp: forall E A B E',
      sub nil E A B E' -> sub nil E (DCastup A) (DCastup B) E'
  | SL1: forall E A C E' B,
      sub nil E A C E' -> sub nil E (DAnd A B) C E'
  | SL2: forall E A C E' B,
      sub nil E B C E' -> sub nil E (DAnd A B) C E'
  | SL3 : forall E A B C E1 E2,
      sub nil E A B E1 -> sub nil E A C E2 -> sub nil E A (DAnd B C) (DMerge E1 E2).





End SubTyping.