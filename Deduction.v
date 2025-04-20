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

Fixpoint stringify (F : @formula string) {struct F} : string :=
  match F with
  | f_atom A => A
  | f_not F' => "\neg " ++ (stringify F')
  | f_imp A B => (stringify A) ++ " \supset " ++ (stringify B)
  end.

Definition F1 : @formula string := f_atom "A"%string.
Compute (stringify F1).

Definition F2 : @formula string := (f_not (f_atom "A"%string)).
Compute (stringify F2).

Definition F3 : @formula string := (f_imp F1 F2).
Compute (stringify F3).

Fixpoint traveler1 {F : @formula atom} {Gamma : @formula atom -> Prop} (T : @entails atom Gamma F) (accum : list string) {struct T} : list string :=
  match T with
  | hypo A H => "hypo"%string :: accum
  | axiom1 A B => "axiom1"%string :: accum
  | axiom2 A B C => "axiom2"%string :: accum
  | axiom3 A B => "axiom3"%string :: accum
  | @mp _ _ A B H1 H2 => let x := traveler1 H2 (")"%string :: accum) in
                        let y := traveler1 H1 (") ("%string :: x) in
                        "mp ("%string :: y
  end.

Compute (traveler1 (T1 A B)).

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
