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
