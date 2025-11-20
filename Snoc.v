Module Snoc.

Inductive snoc_list (A : Type) : Type :=
| snil : snoc_list A
| snoc : snoc_list A -> A -> snoc_list A.

Arguments snil {_}.
Arguments snoc {_} (_) (_).

Fixpoint length_snoc {A : Type} (lst : snoc_list A) : nat :=
  match lst with
  | snil => 0
  | snoc xs x => S (length_snoc xs)
  end.

Fixpoint append_snoc {A : Type} (l1 l2 : snoc_list A) : snoc_list A :=
  match l2 with
  | snil => l1
  | snoc xs x => snoc (append_snoc l1 xs) x
  end.

End Snoc.
Export Snoc.
