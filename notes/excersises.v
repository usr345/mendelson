From Coq Require Import Fin.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Coq.Logic.Eqdep_dec.

Definition is_zero (n: nat) : bool :=
match n with
| 0 => true
| S _ => false
end.

Definition is_zero_dec (n : nat) : sumbool (eq n 0) ((eq n 0) -> False) :=
  match n as m return (sumbool (m = 0) ((m = 0) -> False)) with
  | 0 => left eq_refl
  | S k => right (fun H : (eq (S k) 0) => match H with end)
  end.

Definition choose_type (n : nat) : Type :=
match n with
| 0 => nat
| S _ => bool
end.

Definition choose_value (n : nat) : choose_type n :=
match n as m return choose_type m with
| 0 => 1
| S _ => true
end.

Definition nat_case (n : nat) : Type :=
match n with
| 0 => unit
| S _ => bool
end.

Definition nat_case_value (n : nat) : nat_case n :=
match n as m return nat_case m with
| 0 => tt
| S _ => true
end.

Compute nat_case_value 1.

Definition is_zero_dec' (n : nat) : {n = 0} + {n <> 0} :=
match n as m return ({eq m 0} + {m <> 0}) with
| 0 => left eq_refl
| S n' => right (fun H : S n' = 0 => match H with end)
end.

Compute is_zero_dec' 0.

Definition head_or_tt {A : Type} (l : list A) :
  match l with
  | nil => unit
  | _ :: _ => A
  end : Type (* force universe *)
  :=
  match l with
  | nil => tt
  | cons h _ => h
  end.

Compute head_or_tt [1;5].

Lemma fin_S_cases : forall n (i : Fin.t (S n)),
  i = Fin.F1 \/ exists j, i = Fin.FS j.
Proof.
  intros n i.
  refine (
    match i with
    | Fin.F1 => _
    | Fin.FS m => _
    end).
  - left.
    reflexivity.
  - right.
    exists m.
    reflexivity.
Qed.

Lemma fin0_absurd : Fin.t 0 -> False.
Proof.
  intro i.
  exact (match i with end).
Qed.

Definition fin_shift {n : nat} (i : Fin.t n) : Fin.t (S n) :=
  FS i.

(* Last element
Define the last index of Fin.t (S n):
*)
Fixpoint fin_last {n : nat} : Fin.t (S n) :=
match n with
| 0 => Fin.F1
| S n' => Fin.FS (@fin_last n')
end.

(* Convert to nat *)
Fixpoint fin_to_nat {n : nat} (fin_set : Fin.t n) : nat :=
match fin_set with
| Fin.F1 => 0
| Fin.FS fin_set' => S (fin_to_nat fin_set')
end.

Compute fin_to_nat Fin.F1.

Definition fin_eq_dec {n} (x y : Fin.t n) : {x = y} + {x <> y}.
Proof.
 revert y.
 induction x.
  - (* x = F1 *)
    intros y.
    refine (
      match y as y0 in Fin.t n0
      return ({Fin.F1 = y0} + {Fin.F1 <> y0})
      with
      | Fin.F1 => _
      | Fin.FS _ => _
      end).
    + left.
      reflexivity.
    + right. 
      discriminate.
  - (* x = FS x' *)
    intros y.
    refine (
    match y with
    | Fin.F1 => _
    | Fin.FS m => _
    end).
    + right.
      discriminate.
    + destruct (IHx y) as [H | H].
      * left. f_equal. exact H.
      * right. intro E. inversion E. apply H. assumption.
Defined.

Defined.

Module NatEqDep := DecidableEqDep NatDec.
Import NatEqDep.
(* 
Injectivity of FS 
Fin.FS
*)
Lemma FS_inj : forall n (i j : Fin.t n), Fin.FS i = Fin.FS j -> i = j.
Proof.
  intros n set1 set2 H.
  injection H.
  intro H1.
  apply inj_pairT2 in H1.

fin_to_nat is bounded
Prove:

Lemma fin_to_nat_lt : forall n (i : Fin.t n), fin_to_nat i < n.
Dependent pattern matching practice

Case analysis on Fin.t (S n)
Define a function that returns either “first” or “later”:

Definition fin_case {n : nat} (i : Fin.t (S n)) :
  match i with
  | Fin.F1 => True
  | Fin.FS _ => False
  end := ...

Predecessor as option
Define:

Definition fin_pred {n : nat} (i : Fin.t (S n)) : option (Fin.t n) := ...

Hint: F1 should map to None, and FS j to Some j.

Decidable equality on Fin.t n
Prove:

Lemma fin_eq_dec : forall n (i j : Fin.t n), {i = j} + {i <> j}.