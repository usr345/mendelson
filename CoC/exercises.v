From Coq Require Import Fin.
From Coq Require Import Lists.List.
Import ListNotations.

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

