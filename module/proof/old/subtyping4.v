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

  (* ------------------ *)
  (* E <|  A <: B  |> E'       term E : A D produces term E' : B D   *)
  (* ------------------ *)

  (*
  Inductive Mode := 
  | Typ : Mode
  | Con : Mode.

  Inductive sub : Mode -> DExp -> DExp -> DExp -> DExp -> Prop :=
  | SVar : forall E x m, sub m E (DBVar x) (DBVar x) E
  | SStar : forall E, sub Typ E DStar DStar E
  (* Not correct *)
  | SPi : forall A B A' B' E E1 E2,
      sub Typ (DBVar 0) A' A E1 -> sub Typ (DApp E E1) B B' E2 -> sub Typ E (DPi A B) (DPi A' B') (DLam E2)
  | SLam: forall E A B E', (* I believe we need this here: A ~~> C /\ B ~~> D *) 
      sub Typ (DCastdn E) A (*C*) (*D*) B E' -> sub Con E (DLam A) (DLam B) (DCastup E')
  | SApp: forall T E A B E' m,
      sub Con E A B E' -> sub m E (DApp A T) (DApp B T) E'
  | SCastDown: forall E A B E',
      sub Typ E A B E' -> sub Typ E (DCastdn A) (DCastdn B) E'
  | SCastUp: forall E A B E',
      sub Typ E A B E' -> sub Typ E (DCastup A) (DCastup B) E'
  | SL1: forall E A C E' B,
      sub Typ E A C E' -> sub Typ E (DAnd A B) C E'
  | SL2: forall E A C E' B,
      sub Typ E B C E' -> sub Typ E (DAnd A B) C E'
  | SL3 : forall E A B C E1 E2,
            sub Typ E A B E1 -> sub Typ E A C E2 -> sub Typ E A (DAnd B C) (DMerge E1 E2).
   *)

  Inductive sub : list DExp -> list DExp -> DExp -> DExp -> DExp -> DExp -> Prop :=
  | SVar : forall E S1 S2 x, sub S1 S2 E (DBVar x) (DBVar x) E 
  | SStar : forall E S, sub nil S E DStar DStar E
  (* Not correct *)
  | SPi : forall A B A' B' E E1 E2 S,
      sub nil S (DBVar 0) A' A E1 -> sub nil S (DApp E E1) B B' E2 -> sub nil S E (DPi A B) (DPi A' B') (DLam E2)
  | SLam: forall E A B E' T D S, (* I believe we need this here: A T ~~> C /\ B T ~~> D *) 
      sub D (T :: S) (DCastdn E) A (*C*) (*D*) B E' -> sub (T :: D) S E (DLam A) (DLam B) (DCastup E')
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


End SubTyping.