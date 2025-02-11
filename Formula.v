Module Formula.

(* We assume atomic propositions form a set with decidable equality. *)
Definition atom : Type := nat.
Parameter atom_eq : forall (a b : atom), {a = b} + {a <> b}.

(* Propositional formulas *)
Inductive formula : Type :=
| f_atom : atom -> formula
| f_not  : formula -> formula
| f_imp  : formula -> formula -> formula.

Declare Scope formula_scope.
Open Scope formula_scope.
Declare Custom Entry formula_view.

(* Заполняем нотации с учетом приоритета *)
Notation "x" := x (x ident, in custom formula_view at level 0).
Notation "( p )" := p (p custom formula_view at level 5, in custom formula_view at level 0).
Notation "~ p" := (f_not p) (p custom formula_view at level 1, in custom formula_view at level 1).

(*
Импликация слабее конъюнкции и дизъюнкции, но она нужна для их определений
поэтому нотацию для неё вводим раньше.
 *)
Notation "p -> q" := (f_imp p q) (q custom formula_view at level 4, in custom formula_view at level 4).

Notation "'$' p '$'" := p (format "'$' p '$'", p custom formula_view at level 5, at level 0).

Definition conjunction (A B: formula) : formula := $~(A -> ~B)$.
Notation "A /\ B" := (conjunction A B) (B custom formula_view at level 2, in custom formula_view at level 2, left associativity) : formula_scope.

Definition disjunction (A B: formula) : formula := $~A -> B$.
Notation "A \/ B" := (disjunction A B) (B custom formula_view at level 3, in custom formula_view at level 3, left associativity) : formula_scope.

Definition equivalence (A B: formula) : formula := $(A -> B) /\ (B -> A)$.
Notation "A <-> B" := (equivalence A B) (B custom formula_view at level 5, in custom formula_view at level 5, left associativity) : formula_scope.

(* Equality of formulas is decidable. *)
Lemma formula_eq (A B : formula) : {A = B} + {A <> B}.
Proof.
  decide equality.
  now apply atom_eq.
Qed.

(* Instead of working with lists of assumptions we shall work with
   sets of assumptions. A set of formulas can be represented by its
   characteristic map formula -> Prop. *)

(* Element-hood relation between a formula and a set of formulas. *)
Definition elem (A : formula) (Γ : formula  -> Prop) := Γ A.
Infix "∈" := elem (at level 77) : formula_scope.

(* The empty context. *)
Definition empty : formula -> Prop := fun _ => False.

(* The union of two sets of formulas. *)
Definition union (Γ Δ : formula -> Prop) (A : formula) := A ∈ Γ \/ A ∈ Δ.
Infix "∪" := union (at level 78, left associativity) : formula_scope.

(* The subset relation between sets of formulas. *)
Definition subset (Γ Δ : formula -> Prop) :=
  forall A, A ∈ Γ -> A ∈ Δ.
Infix "⊆" := subset (at level 79) : formula_scope.

End Formula.
Export Formula.
