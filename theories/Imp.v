Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From mathcomp Require Import ssreflect ssrnat.

Require Import Coq.Strings.String.
Require Import Nat.
Require Import Maps.

Definition state := total_map nat.

Definition empty_state : state := t_empty 0.

Notation "[<>]" := empty_state (at level 30) : type_scope.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive aexp : Type :=
(* | AAny : aexp *)
| ANum : nat -> aexp
| AId : string -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.
(* | ADiv : aexp -> aexp -> aexp. *)

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
(* | E_ADiv : forall (a1 a2 : aexp) (n1 n2 n3 : nat), *)
(*     (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) -> *)
(*     (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3 *)
where "a ==> n" := (aevalR a n).

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.

Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.

Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.

Bind Scope bexp_scope with bexp.

Notation "a '<.=' b" := (BLe a b) (at level 60) : bexp_scope.
Notation "a '=.=' b" := (BEq a b) (at level 60) : bexp_scope.
Notation "a '&.&' b" := (BAnd a b) (at level 60) : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => eqn (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval ([<>] [<X ~~>> 5>]) (3 + (X * 2)) = 13.
Proof. by []. Qed.

Example bexp1 :
  beval ([<>] [<X ~~>> 5>]) (true &.& !(X <.= 4)) = true.
Proof. by []. Qed.

Inductive com : Type :=
| CSkip : com
| CAss : string -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE !(Z =.= 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END.

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1;;
  X ::= X - 1.

Definition subtract_slowly : com :=
  WHILE !(X =.= 0) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3;;
  Z ::= 5;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition exp_body : com :=
  Z ::= Z * X;;
  Y ::= Y - 1.

Definition pexp : com :=
  WHILE !(Y =.= 0) DO
    exp_body
  END.

Reserved Notation "c1 '/' st '==>' st'"
         (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
    SKIP / st ==> st
| E_Ass : forall st a1 v k,
    aeval st a1 = v ->
    (k ::= a1) / st ==> st [< k ~~>> v >]
| E_Seq : forall c1 c2 st st' st'',
    c1 / st  ==> st'  ->
    c2 / st' ==> st'' ->
    (c1 ;; c2) / st ==> st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    c1 / st ==> st' ->
    (IFB b THEN c1 ELSE c2 FI) / st ==> st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    c2 / st ==> st' ->
    (IFB b THEN c1 ELSE c2 FI) / st ==> st'
| E_WhileEnd : forall b st c,
    beval st b = false ->
    (WHILE b DO c END) / st ==> st
| E_WhileLoop : forall st st' st'' b c,
    beval st b = true ->
    c / st ==> st' ->
    (WHILE b DO c END) / st' ==> st'' ->
    (WHILE b DO c END) / st  ==> st''

where "c1 '/' st '==>' st'" := (ceval c1 st st').

Inductive cevalR (c : com) (st st' : state) : Prop :=
  | E_Skip' of (c = SKIP) & (st = st')
  | E_Ass' : forall a1 v k,
      aeval st a1 = v ->
      c = (k ::= a1) ->
      st' = (st [< k ~~>> v >]) ->
      cevalR c st st'
  | E_Seq' : forall c1 c2 st'',
      cevalR c1 st st'' ->
      cevalR c2 st'' st' ->
      c = (c1 ;; c2) ->
      cevalR c st st'
  | E_IfTrue' : forall b c1 c2,
      beval st b = true ->
      cevalR c1 st st' ->
      c = (IFB b THEN c1 ELSE c2 FI) ->
      cevalR c st st'
  | E_IfFalse' : forall b c1 c2,
      beval st b = false ->
      cevalR c2 st st' ->
      c = (IFB b THEN c1 ELSE c2 FI) ->
      cevalR c st st'
  | E_WhileEnd' : forall b d,
      beval st b = false ->
      c = (WHILE b DO d END) ->
      st' = st ->
      cevalR c st st'
  | E_WhileLoop' : forall st'' b d,
      beval st b = true ->
      cevalR d st st'' ->
      cevalR c st'' st' ->
      c = (WHILE b DO d END) ->
      cevalR c st st'.

Example ceval_example1 :
  (X ::= 2;;
   IFB X <.= 1
     THEN Y ::= 3
     ELSE Z ::= 4
   FI)
  / [<>]
  ==> [<>] [<X ~~>> 2>] [<Z ~~>> 4>].
Proof.
  apply: E_Seq.
  Unshelve.
Qed.
