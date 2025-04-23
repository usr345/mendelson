Require Import Classical.
From Coq Require Import Arith.
From Mendelson Require Import Sets.
From Mendelson Require Import FSignature.
From Mendelson Require Import Formula.
From Mendelson Require Import Syntactic.
From Coq Require Import Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Module Deduction.

Theorem T1 {atom : Set} (A B : @formula string) : (empty,, $~B -> ~A$),, A |- B.
Proof.
  assert (H1 : (empty,, $~B -> ~A$),, A |- $~B -> ~A$).
  { hypo. }
  assert (H2 : (empty,, $~B -> ~A$),, A |- A).
  { hypo. }
  specialize_axiom (@axiom3 _ ((empty,, $~B -> ~A$),, A) A B) H3.
  specialize (mp H3 H1) as H4.
  specialize_axiom (@axiom1 _ ((empty,, $~B -> ~A$),, A) A $~B$) H5.
  specialize (mp H5 H2) as H6.
  specialize (mp H4 H6) as H7.
  exact H7.
Defined.

Lemma T1_7ex2 {atom : Set} (Γ : @formula atom -> Prop) A B C : Γ ,, $A -> B$ ,, $B -> C$ |- $A -> C$.
Proof.
  (* 1 *)
  specialize_axiom (@axiom1 _ (Γ ,, $A -> B$ ,, $B -> C$) $B -> C$ A) H1.
  (* 2 *)
  assert (H2 : Γ,, $A -> B$,, $B -> C$ |- $A -> (B -> C)$).
  {
    apply @mp with (A := $B -> C$).
    - apply H1.
    - hypo.
  }
  (* 3  *)
  specialize_axiom (@axiom2 _ (Γ ,, $A -> B$ ,, $B -> C$) A B C) H3.
  (* 4 *)
  specialize (mp H3 H2) as H4.
  (* 5 *)
  assert (H5 : Γ,, $A -> B$,, $B -> C$ |- $A -> C$).
  {
    apply @mp with (A := $A -> B$).
    exact H4.
    hypo.
  }
  (* 6 *)
  exact H5.
Defined.

Open Scope string_scope.
Definition A : @formula string := f_atom "A"%string.
Definition B : @formula string := f_atom "B"%string.
Definition C : @formula string := f_atom "C"%string.

(* Check (T1 A B). *)
(* Compute (T1 A B). *)

Fixpoint traveler {atom : Set} {F : @formula atom} {Gamma : @formula atom -> Prop} (T : @entails atom Gamma F) {struct T} : nat :=
  match T with
    | hypo A H => 1
    | axiom1 A B => 1
    | axiom2 A B C => 1
    | axiom3 A B => 1
    | @mp _ _ A B H1 H2 => 1 + max (traveler H1) (traveler H2)
  end.

Fixpoint stringify (F : @formula string) (prefix suffix : string) {struct F} : string :=
  match F with
  | f_atom A => A
  | f_not F' => "\neg " ++ (stringify F' "" "")
  | f_imp A B => prefix ++ (stringify A "(" ")") ++ " \supset " ++ (stringify B "(" ")") ++ suffix
  end.

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Fixpoint traveler1 {F : @formula string} {Gamma : @formula string -> Prop} (T : @entails string Gamma F) (accum : nat * list string) {struct T} : nat * list string :=
  let tek := (fst accum) + 1 in
  let str_tek := (string_of_nat tek) ++ ". " in
  match T with
  | hypo A H => (tek, (str_tek ++ "$" ++ (stringify A "" "") ++ "$ & гипотеза\\") :: (snd accum))
  | axiom1 A B => (tek, (str_tek ++ "$" ++ (stringify (f_axiom1 A B) "" "") ++ "$ & A1\\") :: (snd accum))
  | axiom2 A B C => (tek, (str_tek ++ "$" ++ (stringify (f_axiom2 A B C) "" "") ++ "$ & A2\\") :: (snd accum))
  | axiom3 A B => (tek, (str_tek ++ "$" ++ (stringify (f_axiom3 A B) "" "") ++ "$ & A3\\") :: (snd accum))
  | @mp _ _ A B H1 H2 => let text := snd accum in
                        let (n1, new_text) := traveler1 H1 ((fst accum), text) in
                        let (n2, newest_text) := traveler1 H2 (n1, new_text) in
                        let n1_str := (string_of_nat n1) in
                        let n2_str := (string_of_nat n2) in
                        (n2 + 1, ((string_of_nat (n2 + 1)) ++ ". $" ++ (stringify B "" "") ++ "$ & MP (" ++ n1_str ++ ", " ++ n2_str ++ ")\\") :: newest_text)
  end.

Definition caller {F : @formula string} {Gamma : @formula string -> Prop} (T : @entails string Gamma F) (accum : nat * list string) : list string :=
  let res := traveler1 T (0, nil) in
  ("$\vdash " ++ (stringify F "" "") ++ "$\\") :: (rev (snd res)).

Compute fold_left append (caller (T1_7ex2 empty A B C) (0, nil)) "".

(* Compute (traveler (T1 A B)). *)
(* Compute ( *)
(*     match (T1 A B) with *)
(*     | hypo A H => 1 *)
(*     | axiom1 A B => 2 *)
(*     | axiom2 A B C => 3 *)
(*     | axiom3 A B => 4 *)
(*     | mp B H1 H2 => 5 *)
(*     end *)
(*   ). *)

End Deduction.
