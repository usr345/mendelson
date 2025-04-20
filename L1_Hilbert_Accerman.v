Require Import Classical.
From Mendelson Require Import Sets.

Module L1_Hilbert_Accerman.

(* We assume atomic propositions form a set with decidable equality. *)
Parameter atom_eq : forall {atom : Set} (a b : atom), {a = b} + {a <> b}.

(* Propositional formulas *)
Inductive formula {atom : Set} : Type :=
| f_atom : atom -> formula
| negation  : formula -> formula
| disjunction  : formula -> formula -> formula.

Declare Scope formula_scope.
Declare Custom Entry formula_view.
Open Scope formula_scope.

(* Заполняем нотации с учетом приоритета *)
Notation "x" := x (x ident, in custom formula_view at level 0).
Notation "( p )" := p (p custom formula_view at level 5, in custom formula_view at level 0).
Notation "~ p" := (negation p) (p custom formula_view, in custom formula_view at level 1).
Notation "A \/ B" := (disjunction A B) (B custom formula_view, in custom formula_view at level 3, left associativity) : formula_scope.
Notation "'$' p '$'" := p (format "'$' p '$'", p custom formula_view, at level 0).

Definition implication {atom : Set} (A B: @formula atom) : formula := $~A \/ B$.
Notation "p -> q" := (implication p q) (q custom formula_view, in custom formula_view at level 4, right associativity).

Definition conjunction {atom : Set} (A B: @formula atom) : formula := $~(A -> ~B)$.
Notation "A /\ B" := (conjunction A B) (B custom formula_view, in custom formula_view at level 2, left associativity) : formula_scope.

Definition equivalence {atom : Set} (A B: @formula atom) : formula := $(A -> B) /\ (B -> A)$.
Notation "A <-> B" := (equivalence A B) (B custom formula_view, in custom formula_view at level 5, left associativity) : formula_scope.

Definition f_axiom1 {atom : Set} (A B : @formula atom) : formula :=
  $(A \/ A) -> A$.

Definition f_axiom2 {atom : Set} (A B : @formula atom) : formula :=
  $A -> A \/ B$.

Definition f_axiom3 {atom : Set} (A B : @formula atom) : formula :=
  $A \/ B -> B \/ A$.

Definition f_axiom4 {atom : Set} (A B C: @formula atom) : formula :=
  $(B -> C) -> (A \/ B -> A \/ C)$.

Reserved Notation "Γ |- A" (at level 32).
Inductive entails {atom : Set} (Γ : @formula atom -> Prop) : @formula atom -> Type :=
| hypo : forall A, A ∈ Γ -> Γ |- A (* every hypothesis is provable *)
| axiom1 : forall A B , Γ |- f_axiom1 A B
| axiom2 : forall A B, Γ |- f_axiom2 A B
| axiom3 : forall A B, Γ |- f_axiom3 A B
| axiom4 : forall A B C, Γ |- f_axiom4 A B C
| mp {A B : formula} : Γ |- $B -> A$ -> Γ |- B -> Γ |- A (* modus ponens *)
where "Γ |- A" := (entails Γ A).

(* It is convenient to make some parameters implicit. *)
Arguments hypo {_} {_} _.
Arguments axiom1 {_} {_} _ _.
Arguments axiom2 {_} {_} _ _.
Arguments axiom3 {_} {_} _ _.
Arguments axiom4 {_} {_} _ _ _.
Arguments mp {_} {_} {_} {_} (_) (_).

Ltac hypo := (apply hypo ; cbv in * ; auto 6).
Ltac specialize_axiom A H :=
  pose proof A as H;
  try match type of H with
    | (_ |- f_axiom1 _ _) => unfold f_axiom1 in H
    | (_ |- f_axiom2 _ _) => unfold f_axiom2 in H
    | (_ |- f_axiom3 _ _) => unfold f_axiom3 in H
    | (_ |- f_axiom4 _ _ _) => unfold f_axiom4 in H
  end.

Theorem weaken {atom : Set} (Γ : @formula atom -> Prop) Δ A : Γ ⊆ Δ -> Γ |- A -> Δ |- A.
Proof.
  intros S H.
  induction H as [A H|A B|A B|A B|A B C|A B H1 H2 IH1 IH2].
  (* Пусть A ∈ Γ *)
  - unfold subset in S.
    specialize (S A H).
    apply hypo.
    exact S.
  - apply (axiom1 A B).
  - apply (axiom2 A B).
  - apply (axiom3 A B).
  - apply (axiom4 A B C).
  - pose proof (mp H2 IH2) as H3.
    exact H3.
Qed.

Lemma imply_self {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A -> A$.
Proof.
  unfold implication.
  (* (1) $(A \supset ((A \supset A) \supset A)) \supset ((A \supset (A \supset A)) \supset (A \supset A))$ --- подстановка в схему аксиом A4 *)
  specialize_axiom (@axiom4 _ Γ $~A$ $A \/ A$ A) H1.
  (* (2) $A \or A \supset A$ --- схема аксиом A1 *)
  specialize_axiom (@axiom1 _ Γ A A) H2.
  (* (3) $((A \supset (A \supset A)) \supset (A \supset A))$ --- из (1) и (2) по MP *)
  specialize (mp H1 H2) as H3.
  (* (4) $A \supset (A \supset A)$ --- схема аксиом A1 *)
  specialize_axiom (@axiom2 _ Γ A A) H4.
  unfold implication in H4.
  (* (5) $A \supset A$ --- из (3) и (4) по MP *)
  specialize (mp H3 H4) as H5.
  exact H5.
Qed.

Lemma T1 {atom : Set} (Γ : @formula atom -> Prop) (A B C : @formula atom) : Γ,, $A -> B$ |- $C \/ A -> C \/ B$.
Proof.
  specialize_axiom (@axiom4 _ (Γ,, $A -> B$) C A B) H1.
  assert (H2: Γ,, $A -> B$ |- $A -> B$).
  {
    hypo.
  }

  specialize (mp H1 H2) as H3.
  exact H3.
Qed.

End L1_Hilbert_Accerman.
