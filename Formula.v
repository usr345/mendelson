From Mendelson Require Import FSignature.

Module Formula1 <: TFormula.
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_imp  : formula -> formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition implication {atom : Type} := @f_imp atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} (A B: @formula atom) : formula := negation (implication A (negation B)).
  Definition disjunction {atom : Type} (A B: @formula atom) : formula := implication (negation A) B.
  Definition equivalence {atom : Type} (A B: @formula atom) : formula := conjunction (implication A B) (implication B A).
End Formula1.
Export Formula1.

Module Formula.

  Module F1:= Make_Formula(Formula1).
  Import F1.
  Export F1.

  (* We assume atomic propositions form a set with decidable equality. *)
  Parameter atom_eq : forall {atom : Set} (a b : atom), {a = b} + {a <> b}.

  (* Equality of formulas is decidable. *)
  Lemma formula_eq {atom : Set} (A B : @formula atom) : {A = B} + {A <> B}.
  Proof.
    decide equality.
    now apply atom_eq.
  Qed.

  Definition f_axiom1 {atom : Set} (A B : @formula atom) : formula :=
  $A -> (B -> A)$.

End Formula.
Export Formula.
