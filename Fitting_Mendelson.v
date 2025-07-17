Require Import Setoid.
From Mendelson Require Import Sets.
From Mendelson Require Import FSignature.
From Mendelson Require Import EqDec.

Module Formula1 <: TFormula.
  (* Синтаксис модальной формулы *)
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula
  | f_imp  : formula -> formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} := @f_imp atom.
  Definition disjunction {atom : Type} := @f_imp atom.
  Definition implication {atom : Type} := @f_imp atom.
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

  Fixpoint formula_beq {atom : Set} `{EqDec atom} (A B : @formula atom) : bool :=
    match A, B with
    | f_atom a, f_atom b  => eqb a b
    | f_not A', f_not B' => formula_beq A' B'
    | f_conj A1 A2, f_conj B1 B2 => andb (formula_beq A1 B1) (formula_beq A2 B2)
    | f_disj A1 A2, f_disj B1 B2 => andb (formula_beq A1 B1) (formula_beq A2 B2)
    | f_imp A1 A2, f_imp B1 B2 => andb (formula_beq A1 B1) (formula_beq A2 B2)
    | _, _ => false
    end.

  Lemma formula_beq_eq {atom : Set} `{EqDec atom} (A B : @formula atom) :
    (formula_beq A B) = true <-> A = B.
  Proof.
    split ; intro H1.
    - generalize dependent B.
      induction A.
      + intros B H1.
        destruct B ; unfold formula_beq in H1 ; try discriminate H1.
        * apply eqb_eq in H1.
          rewrite H1.
          reflexivity.
      + intros B H1.
        destruct B.
        * unfold formula_beq in H1.
          discriminate H1.
        * simpl in H1.
          specialize (IHA B).
          specialize (IHA H1).
          rewrite IHA.
          reflexivity.
        * simpl in H1.
          discriminate H1.
        * simpl in H1.
          discriminate H1.
        * simpl in H1.
          discriminate H1.
      + intros B H1.
        destruct B.
        (* atom *)
        * simpl in H1.
          discriminate H1.
        (* conj *)
        * simpl in H1.
          discriminate H1.
        (* disj *)
        * simpl in H1.
          apply andb_prop in H1.
          destruct H1 as [H1 H2].
          specialize (IHA1 B1).
          specialize (IHA1 H1).
          specialize (IHA2 B2).
          specialize (IHA2 H2).
          rewrite IHA1.
          rewrite IHA2.
          reflexivity.
        (* impl *)
        * simpl in H1.
          discriminate H1.
        * simpl in H1.
          discriminate H1.
    - generalize dependent B.
      induction A.
      + intros B H1.
        rewrite <-H1.
        simpl.
        apply eqb_reflexive.
      + intros B H1.
        rewrite <-H1.
        simpl.
        specialize (IHA A).
        assert (Ha : A = A).
        { reflexivity. }
        specialize (IHA Ha).
        apply IHA.
      + intros B H1.
        rewrite <-H1.
        simpl.
        apply andb_true_intro.
        split.
        * specialize (IHA1 A1).
        assert (Ha : A1 = A1).
        { reflexivity. }
        specialize (IHA1 Ha).
        apply IHA1.
        * specialize (IHA2 A2).
        assert (Ha : A2 = A2).
        { reflexivity. }
        specialize (IHA2 Ha).
        apply IHA2.
  Qed.

  #[export] Instance eqFormula {atom : Set} `{EqDec atom} : EqDec (@formula atom)  :=
    {
      eqb := formula_beq;
      eqb_eq := formula_beq_eq;
    }.

  Fixpoint replace_atom {atom : Set} `{EqDec atom} (F : @formula atom) (a : atom) (G : @formula atom) {struct F} : @formula atom :=
    match F with
    | f_atom a' => if (eqb a' a) then G else F
    | f_not F' => f_not (replace_atom F' a G)
    | f_imp F1 F2 => f_imp (replace_atom F1 a G) (replace_atom F2 a G)
    end.

  (* Заменяет все вхождения атомов, для которых v a = true на F1
     и атомов с v a = false на F2
  *)
  Fixpoint replace_true_false {atom : Set} `{EqDec atom} (F : @formula atom) (v : atom -> bool) (F1 F2 : @formula atom) {struct F} : @formula atom :=
    match F with
    | f_atom a => if (v a) then F1 else F2
    | f_not F' => f_not (replace_true_false F' v F1 F2)
    | f_imp A B => f_imp (replace_true_false A v F1 F2) (replace_true_false B v F1 F2)
    end.


End Formula.
Export Formula.



Module Fitting_Mendelson.

Definition f_axiom1 {atom : Set} (A B : @formula atom) : formula :=
  $A -> (B -> A)$.

Definition f_axiom2 {atom : Set} (A B C : @formula atom) : formula :=
  $(A -> B -> C) -> (A -> B) -> (A -> C)$.

Definition f_axiom3 {atom : Set} (A B : @formula atom) : formula :=
  $(~ B -> ~ A) -> (~ B -> A) -> B$.

Reserved Notation "Γ |- A" (at level 98).
Inductive entails {atom : Set} (Γ : @formula atom -> Prop) : @formula atom -> Type :=
  | hypo : forall A, A ∈ Γ -> Γ |- A (* every hypothesis is provable *)
  | axiom1 : forall A B , Γ |- f_axiom1 A B
  | axiom2 : forall A B C, Γ |- f_axiom2 A B C
  | axiom3 : forall A B, Γ |- f_axiom3 A B
  | axiom4 : forall A B , Γ |- f_axiom4 A B
  | axiom5 : forall A B C, Γ |- f_axiom5 A B C
  | axiom6 : forall A B, Γ |- f_axiom6 A B
  | axiom7 : forall A B , Γ |- f_axiom7 A B
  | axiom8 : forall A B C, Γ |- f_axiom8 A B C
  | axiom9 : forall A B, Γ |- f_axiom9 A B
  | axiom10 : forall A B, Γ |- f_axiom10 A B
  | mp : forall A B, Γ |- $A -> B$ -> Γ |- A -> Γ |- B (* modus ponens *)
where "Γ |- A" := (entails Γ A).

(* It is convenient to make some parameters implicit. *)
Arguments hypo {_} {_} _.
Arguments axiom1 {_} {_} _ _.
Arguments axiom2 {_} {_} _ _ _.
Arguments axiom3 {_} {_} _ _.
Arguments mp {_} {_} {_} {_} (_) (_).


End Fitting_Mendelson.
