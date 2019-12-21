From Coq Require Import ssreflect ssrbool ssrfun.

Module Maps.
  Require Import Coq.Bool.Bool.
  Require Import Coq.Strings.String.
  Require Import Coq.Logic.FunctionalExtensionality.

  Definition beq_string x y :=
    if string_dec x y then true else false.

  Check string_dec.

  Lemma beq_stringP {x y} :
    reflect (x = y) (beq_string x y).
  Proof.
    case E: (beq_string x y).
    - constructor.
      rewrite /beq_string in E.
      (* {s1 = s2} + {s1 <> s2}  *)
      (*     ^            ^      *)
      (* left H_beq  right H_beq *)
      case S: (string_dec x y)=> [H_beq | H_beq].
      + exact: H_beq.
      + rewrite S in E.
        rewrite /is_left in E.
        discriminate.
    - constructor.
      rewrite /beq_string in E.
      case S: (string_dec x y)=> [H_beq | H_beq].
      + rewrite S in E.
        rewrite /is_left in E.
        discriminate.
      + exact: H_beq.

    Restart.

    case E: (beq_string x y); constructor;
      case S: (string_dec x y) => [hP | hP] //;
        rewrite /beq_string S /is_left in E; discriminate.
  Defined.


  Theorem beq_string_refl :
    forall s, true = beq_string s s.
  Proof.
    move=> s.
    case E: (beq_string s s)=> //.
    move /beq_stringP in E.
    by [].

    Restart.

    move=> s. case E: (beq_string s s)=> //.
    by move /beq_stringP in E.
  Qed.

  Theorem beq_string_true_iff :
    forall x y : string,
      beq_string x y = true <-> x = y.
  Proof.
    split.
    - move /beq_stringP.
      apply.
    - move=> H.
      rewrite H.
      rewrite -beq_string_refl.
      done.

    Restart.

    split.
    - by move /beq_stringP.
    - by move=> ->; rewrite -beq_string_refl.
  Qed.

  Theorem beq_string_false_iff :
    forall x y : string,
      beq_string x y = false <-> x <> y.
  Proof.
    move=> x y.
    rewrite -beq_string_true_iff.
    rewrite not_true_iff_false.
    done.
  Qed.

  Theorem false_beq_string :
    forall x y : string,
      x <> y -> beq_string x y = false.
  Proof.
    move=> x y.
    rewrite beq_string_false_iff.
    apply.
  Qed.

  Definition total_map (A : Type) := string -> A.

  Definition t_empty {A : Type} (v : A) : total_map A :=
    (fun _ => v).

  Definition t_update {A : Type} (m : total_map A) (k : string) (v : A) :=
    fun k' => if beq_string k k' then v else m k'.

  Definition examplemap :=
    t_update (t_update (t_empty false) "foo" true) "bar" true.

  Compute (examplemap "foo").
  Compute (examplemap "bar").
  Compute (examplemap "baz").

  Notation "[< v >]" := (t_empty v) (at level 30).
  Notation "st [< k ~~>> v >]" := (t_update st k v) (at level 21, left associativity).

  Print examplemap.

  Lemma t_update_eq :
    forall A (m : total_map A) k v,
      m [<k ~~>> v>] k = v.
  Proof.
    move=> A m k v.
    rewrite /t_update.
    rewrite -beq_string_refl.
    done.
  Qed.

  Lemma t_update_neq :
    forall (A : Type) v k1 k2 (m : total_map A),
      k1 <> k2 -> m [<k1 ~~>> v>] k2 = m k2.
  Proof.
    move=> A v k1 k2 m.
    move=> /beq_stringP.
    rewrite /t_update.
    (* negbTE b : ~~ b -> b = false. *)
    move/negbTE.
    move=>->.
    done.
  Qed.

  Lemma t_update_shadow :
    forall A (m : total_map A) v1 v2 k,
      m [<k ~~>> v1>] [<k ~~>> v2>] = m [<k ~~>> v2>].
  Proof.
    move=> A m v1 v2 k.
    apply: functional_extensionality=> k'.
    rewrite /t_update.
    case: beq_stringP.
    move=> H_eq_k.
    done.
    move=> H_neq_k.
    done.

    Restart.

    move=> ? ? ? ? x1. apply: functional_extensionality => x2.
    by rewrite /t_update; case: beq_stringP.
  Qed.

  (* TODO *)

End Maps.
