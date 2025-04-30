From Mendelson Require Import FSignature.
From Mendelson Require Import EqDec.

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

  Fixpoint formula_beq {atom : Set} `{EqDec atom} (A B : @formula atom) : bool :=
    match A, B with
    | f_atom a, f_atom b  => eqb a b
    | f_not A', f_not B' => formula_beq A' B'
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
        destruct B ; unfold formula_beq in H1.
        * apply eqb_eq in H1.
          rewrite H1.
          reflexivity.
        * discriminate H1.
        * discriminate H1.
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
      + intros B H1.
        destruct B.
        * simpl in H1.
          discriminate H1.
        * simpl in H1.
          discriminate H1.
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

End Formula.
Export Formula.
