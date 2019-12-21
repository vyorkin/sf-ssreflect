Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Coq Require Import ssreflect.

Require Import Maps.

Inductive aexp : Type :=
(* | AAny : aexp *)
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| ADiv : aexp -> aexp -> aexp.

Reserved Notation "t ==> t'" (at level 50).

Inductive aevalR : aexp -> nat -> Prop :=
(* | E_Any : forall (n : nat), *)
(*     AAny ==> n *)
| E_ANum : forall (n : nat),
    (ANum n) ==> n
| E_APlus : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
| E_AMinus : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
| E_AMult : forall (a1 a2 : aexp) (n1 n2 : nat),
    (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
| E_ADiv : forall (a1 a2 : aexp) (n1 n2 n3 : nat),
    (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
    (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3
where "a ==> n" := (aevalR a n).

Definition state := total_map nat.
