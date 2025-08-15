From Mendelson Require Import FSignature.
From Mendelson Require Import EqDec.
From Mendelson Require Import Fitting_Mendelson.
Import Syntactic.
(* A type with three atoms. *)
Inductive atom3 : Set :=
  | x1 : atom3
  | x2 : atom3
  | x3 : atom3.

Definition atom3_eq (A B : atom3) : bool :=
  match A, B with
  | x1, x1 => true
  | x2, x2 => true
  | x3, x3 => true
  | _, _ => false
  end.

Lemma atom3_eq_correct (A B : atom3) :
    (atom3_eq A B) = true <-> A = B.
Proof.
  split ; intro H.
  - destruct A.
    + destruct B.
      * reflexivity.
      * simpl in H.
        discriminate H.
      * simpl in H.
        discriminate H.
    + destruct B.
      * simpl in H.
        discriminate H.
      * reflexivity.
      * simpl in H.
        discriminate H.
    + destruct B.
      * simpl in H.
        discriminate H.
      * simpl in H.
        discriminate H.
      * reflexivity.
  - rewrite <-H.
    destruct A ; simpl ; reflexivity.
Qed.

#[local] Instance eqAtom3 : EqDec atom3  :=
  {
    eqb := atom3_eq;
    eqb_eq := atom3_eq_correct;
  }.

Definition x : @formula atom3 := f_atom x1.
Definition y : @formula atom3 := f_atom x2.
Definition z : @formula atom3 := f_atom x3.
Definition F1 : @formula atom3 := f_imp (f_conj (f_atom x1) (f_atom x2)) (f_imp (f_atom x2) (f_atom x3)).

Definition F2 : @formula atom3 := f_not (f_atom x3).
Definition F3 : @formula atom3 := f_atom x1.

Example test1: (replace_subformula_int F3 F2 F1 1) = ((f_imp (f_conj (f_not (f_atom x3)) (f_atom x2)) (f_imp (f_atom x2) (f_atom x3))), 0).
Proof. simpl. reflexivity. Qed.

Definition F4 : @formula atom3 := f_conj (f_atom x1) (f_atom x2).
Example test2: (replace_subformula_int F4 F2 F1 1) = ((f_imp (f_not (f_atom x3)) (f_imp (f_atom x2) (f_atom x3))), 0).
Proof. simpl. reflexivity. Qed.

Definition F5 : @formula atom3 := (f_atom x2).
Example test3: (replace_subformula_int F5 F2 F1 2) = ((f_imp (f_conj (f_atom x1) (f_atom x2)) (f_imp (f_not (f_atom x3)) (f_atom x3))), 0).
Proof. simpl. reflexivity. Qed.

Definition F6 : @formula atom3 := f_conj (f_atom x1) (f_atom x2).
Definition F7 : @formula atom3 := f_imp F6 F6.

Example test4: (replace_subformula_int F6 F2 F7 2) = ((f_imp F6 F2), 0).
Proof. simpl. reflexivity. Qed.

Compute (replace_subformula_int F3 F2 F1 1).

Example test5: (subformula F6 F7) = true.
Proof. simpl. reflexivity. Qed.

(* $~ x3$ \not \in (x1 /\ x2) -> (x1 /\ x2) *)
Example test6: (subformula F2 F7) = false.
Proof. simpl. reflexivity. Qed.

Compute subformula
