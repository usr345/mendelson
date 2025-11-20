Require Import Lists.List.
Import ListNotations.

Inductive snoc_list (A : Type) : Type :=
| snil : snoc_list A
| snoc : snoc_list A -> A -> snoc_list A.

Arguments snil {_}.
Arguments snoc {_} (_) (_).
(* В функции snoc обратный порядом аргументов по сравнению c list.cons *)

Definition lst1 : snoc_list nat := snoc snil 1.
Definition lst2 : snoc_list nat := snoc (snoc (snoc snil 1) 2) 3.


Fixpoint snoc_to_cons {A : Type} (lst : snoc_list A) : list A :=
  match lst with
  | snil => nil
  | snoc xs x => (snoc_to_cons xs) ++ [x]
  end.

Compute snoc_to_cons lst2.

(* Неправильно - возвращает список в обратном порядке *)
Fixpoint cons_to_snoc_rev {A : Type} (lst : list A) : snoc_list A :=
  match lst with
  | nil => snil
  | x :: xs => snoc (cons_to_snoc_rev xs) x
  end.

Fixpoint cons_to_snoc_int {A : Type} (lst : list A) (accum : snoc_list A) : snoc_list A :=
  match lst with
  | nil => accum
  | x :: xs => cons_to_snoc_int xs (snoc accum x)
  end.

Fixpoint cons_to_snoc {A : Type} (lst : list A) : snoc_list A :=
  cons_to_snoc_int lst snil.

Compute cons_to_snoc [1; 2; 3].

(* Exercise 1: Define a function length_snoc that computes the length of a SNOC list. *)
Fixpoint length_snoc {A : Type} (lst : snoc_list A) : nat :=
  match lst with
  | snil => 0
  | snoc xs x => S (length_snoc xs)
  end.

(* Exercise 2: Prove that converting a SNOC list to a list preserves length: *)
Lemma snoc_list_to_list_length : forall {A : Type} (lst : snoc_list A),
  length_snoc lst = length (snoc_to_cons lst).
Proof.
  intros A lst.
  induction lst as [|xs IH x].
  - unfold length_snoc.
    unfold snoc_to_cons.
    simpl.
    reflexivity.
  - simpl.
    rewrite length_app.
    simpl.
    rewrite IH.
    rewrite <-plus_n_Sm.
    rewrite <-plus_n_O.
    reflexivity.
Qed.

(* Exercise 3: Define a function append_snoc that concatenates two SNOC lists. *)
Fixpoint append_snoc {A : Type} (l1 l2 : snoc_list A) : snoc_list A :=
  match l2 with
  | snil => l1
  | snoc xs x => snoc (append_snoc l1 xs) x
  end.

Definition lst3 : snoc_list nat := snoc (snoc snil 4) 5.
Compute append_snoc lst2 lst3.

(* Exercise 4: Prove that converting concatenated SNOC lists to a list is the same as concatenating their list representations *)
Lemma append_snoc_correct : forall {A : Type} (l1 l2 : snoc_list A),
  snoc_to_cons (append_snoc l1 l2) = snoc_to_cons l1 ++ snoc_to_cons l2.
Proof.
  intros.
  induction l2 as [|xs IH x].
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite IH.
    rewrite <-app_assoc.
    reflexivity.
Qed.
