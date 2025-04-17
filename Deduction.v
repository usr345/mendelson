Require Import Classical.
From Mendelson Require Import Formula.
From Mendelson Require Import Syntactic.
From Coq Require Import Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Module Deduction.
Theorem T1 {atom : Set} (A B : @formula atom) : (empty,, $~B -> ~A$),, A |- B.
Proof.
  assert (H1 : (empty,, $~B -> ~A$),, A |- $~B -> ~A$).
  { hypo. }
  assert (H2 : (empty,, $~B -> ~A$),, A |- A).
  { hypo. }
  specialize_axiom (@axiom3 _ ((empty,, $~B -> ~A$),, A) A B) H3.
  specialize (mp $~ B -> ~ A$ H1 H3) as H4.
  specialize_axiom (@axiom1 _ ((empty,, $~B -> ~A$),, A) A $~B$) H5.
  specialize (mp A H2 H5) as H6.
  specialize (mp $~B -> A$ H6 H4) as H7.
  exact H7.
Defined.

Axiom atom : Set.
Axiom A : @formula atom.
Axiom B : @formula atom.

Check (T1 A B).
Compute (T1 A B).

Fixpoint traveler {F : @formula atom} {Gamma : @formula atom -> Prop} (T : @entails atom Gamma F) {struct T} : nat :=
  match T with
    | hypo A H => 1
    | axiom1 A B => 1
    | axiom2 A B C => 1
    | axiom3 A B => 1
    | @mp _ _ A B H1 H2 => 1 + max (traveler H1) (traveler H2)
    end.

Compute (traveler (T1 A B)).
Compute (
    match (T1 A B) with
    | hypo A H => 1
    | axiom1 A B => 2
    | axiom2 A B C => 3
    | axiom3 A B => 4
    | mp B H1 H2 => 5
    end
  ).

End Deduction.
