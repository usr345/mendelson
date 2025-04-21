Declare Scope formula_scope.
Declare Custom Entry formula_view.
Open Scope formula_scope.
Notation "x" := x (x ident, in custom formula_view at level 0).
Notation "( p )" := p (p custom formula_view at level 5, in custom formula_view at level 0).
Notation "'$' p '$'" := p (format "'$' p '$'", p custom formula_view at level 5, at level 0).

Module Type TFormula.
  Section S.
    Parameter t: Type -> Type.
    Context {atom: Type}.
    Local Notation formula := (t atom).
    Parameter implication: formula -> formula -> formula.
    Parameter conjunction: formula -> formula -> formula.
    Parameter disjunction: formula -> formula -> formula.
    Parameter equivalence: formula -> formula -> formula.
    Parameter negation: formula -> formula.
  End S.
End TFormula.

Module Make_Formula(ARG:TFormula).
  Module F := ARG.
  Export F.
  (* Filling notations according to priority *)
  #[global] Notation "~ p" := (negation p) (p custom formula_view at level 1, in custom formula_view at level 1).
  #[global] Notation "A /\ B" := (conjunction A B) (B custom formula_view at level 2, in custom formula_view at level 2, left associativity) : formula_scope.
  #[global] Notation "A \/ B" := (disjunction A B) (B custom formula_view at level 3, in custom formula_view at level 3, left associativity) : formula_scope.
  #[global] Notation "p -> q" := (implication p q) (q custom formula_view at level 4, in custom formula_view at level 4, right associativity).
  #[global] Notation "A <-> B" := (equivalence A B) (B custom formula_view at level 5, in custom formula_view at level 5, left associativity) : formula_scope.
End Make_Formula.
