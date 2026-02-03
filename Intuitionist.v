Require Import Setoid.
From Mendelson Require Import MSets.
From Mendelson Require Import FSignature.
From Mendelson Require Import EqDec.
From Stdlib Require Import Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Logic.
From Coq Require Import List.
Import ListNotations.

Module Formula1 <: TFormula.
  (* Синтаксис интуиционистской формулы *)
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula
  | f_imp  : formula -> formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} := @f_conj atom.
  Definition disjunction {atom : Type} := @f_disj atom.
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
        (* f_atom *)
        * apply eqb_eq in H1.
          rewrite H1.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* f_not *)
        * specialize (IHA B).
          specialize (IHA H1).
          rewrite IHA.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* conj *)
        * apply andb_prop in H1.
          destruct H1 as [H1 H2].
          specialize (IHA1 B1).
          specialize (IHA1 H1).
          specialize (IHA2 B2).
          specialize (IHA2 H2).
          rewrite IHA1.
          rewrite IHA2.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* disj *)
        * apply andb_prop in H1.
          destruct H1 as [H1 H2].
          specialize (IHA1 B1).
          specialize (IHA1 H1).
          specialize (IHA2 B2).
          specialize (IHA2 H2).
          rewrite IHA1.
          rewrite IHA2.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* impl *)
        * apply andb_prop in H1.
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
      (* atom *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        apply eqb_reflexive.
      (* not *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        specialize (IHA A).
        assert (Ha : A = A).
        { reflexivity. }
        specialize (IHA Ha).
        apply IHA.
      (* conj *)
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
      (* disj *)
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
      (* impl *)
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

  #[export] Instance eqFormula {atom : Set} `{EqDec atom} : EqDec (@formula atom) :=
  {
     eqb := formula_beq;
     eqb_eq := formula_beq_eq;
  }.

End Formula.
Export Formula.

Module Semantic.

Import Formula.
Import Relation.

Class Frame :=
{
  worlds : Type;
  worlds_inh : inhabited worlds;
  accessible : worlds -> worlds -> Prop;
}.

Axiom transitive (@accessible frame)

Class Model {atom : Type} :=
{
  frame :: Frame;
  valuation : worlds -> atom -> Prop;
}.



Fixpoint valid {atom : Set} `(M : @Model atom) (Γ : worlds) (f : @formula atom) : Prop :=
  match f with
  | f_atom p => valuation Γ p
  | f_not f' => forall w, ~(valid M Γ f')
  | f_conj f1 f2 => (valid M Γ f1) /\ (valid M Γ f2)
  | f_disj f1 f2 => (valid M Γ f1) \/ (valid M Γ f2)
  | f_imp f1 f2 => (valid M Γ f1) -> (valid M Γ f2)
  | f_box f' => forall w, (accessible Γ w) -> (valid M w f')
  | f_diamond f' => exists w, (accessible Γ w) /\ (valid M w f')
  end.

Definition valid_in_frame {atom : Set} `(Fr : Frame) (f : @formula atom) : Prop :=
  forall (V : worlds -> atom -> Prop),
    forall w, valid {| frame := Fr;
                  valuation := V |} w f.

Definition consequence {atom : Set} `(Fr : Frame) {Set_obj1 : TSet (@formula atom)} {Set_obj2 : TSet (@formula atom)} (G : Set_obj1) (L : Set_obj2) (f : @formula atom)
