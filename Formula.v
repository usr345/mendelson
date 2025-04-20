Module Formula.

(* We assume atomic propositions form a set with decidable equality. *)
Parameter atom_eq : forall {atom : Set} (a b : atom), {a = b} + {a <> b}.

(* Propositional formulas *)
Inductive formula {atom : Set} : Type :=
| f_atom : atom -> formula
| f_not  : formula -> formula
| f_imp  : formula -> formula -> formula.

Declare Scope formula_scope.
Declare Custom Entry formula_view.
Open Scope formula_scope.

(* Заполняем нотации с учетом приоритета *)
Notation "x" := x (x ident, in custom formula_view at level 0).
Notation "( p )" := p (p custom formula_view at level 5, in custom formula_view at level 0).
Notation "~ p" := (f_not p) (p custom formula_view at level 1, in custom formula_view at level 1).

(*
Импликация слабее конъюнкции и дизъюнкции, но она нужна для их определений
поэтому нотацию для неё вводим раньше.
 *)
Notation "p -> q" := (f_imp p q) (q custom formula_view at level 4, in custom formula_view at level 4, right associativity).

Notation "'$' p '$'" := p (format "'$' p '$'", p custom formula_view at level 5, at level 0).

Definition conjunction {atom : Set} (A B: @formula atom) : formula := $~(A -> ~B)$.
Notation "A /\ B" := (conjunction A B) (B custom formula_view at level 2, in custom formula_view at level 2, left associativity) : formula_scope.

Definition disjunction {atom : Set} (A B: @formula atom) : formula := $~A -> B$.
Notation "A \/ B" := (disjunction A B) (B custom formula_view at level 3, in custom formula_view at level 3, left associativity) : formula_scope.

Definition equivalence {atom : Set} (A B: @formula atom) : formula := $(A -> B) /\ (B -> A)$.
Notation "A <-> B" := (equivalence A B) (B custom formula_view at level 5, in custom formula_view at level 5, left associativity) : formula_scope.

(* Equality of formulas is decidable. *)
Lemma formula_eq {atom : Set} (A B : @formula atom) : {A = B} + {A <> B}.
Proof.
  decide equality.
  now apply atom_eq.
Qed.
End Formula.
Export Formula.
