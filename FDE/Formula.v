From Basis Require Import FSignature.
From Basis Require Import EqDec.
From Coq Require Bool.Bool.
Open Scope formula_scope.

Module FormulaDef <: TFormula.
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} := @f_conj atom.
  Definition disjunction {atom : Type} := @f_disj atom.
  Definition implication {atom : Type} (A B: @formula atom) :=
    disjunction (negation A) B.
  Definition equivalence {atom : Type} (A B: @formula atom) : formula := conjunction (implication A B) (implication B A).

  Fixpoint formula_eqb {atom : Type} `{EqDec atom} (f g : @formula atom) : bool :=
    match f, g with
    | f_atom a, f_atom b => eqb a b
    | f_not f1, f_not g1 => formula_eqb f1 g1
    | f_conj f1 f2, f_conj g1 g2 => formula_eqb f1 g1 && formula_eqb f2 g2
    | f_disj f1 f2, f_disj g1 g2 => formula_eqb f1 g1 && formula_eqb f2 g2
    | _, _ => false
    end.

  Lemma formula_eqb_eq_left {atom : Type} `{Heq : EqDec atom} : 
    forall f g : @formula atom, formula_eqb f g = true -> f = g.
  Proof.
    intros f.
    induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2].
    - intros g H.
      destruct g ; simpl ; simpl in H ; try discriminate H.
      simpl in H.
      apply eqb_eq in H.
      rewrite H.
      reflexivity.
    - intros g H.
      destruct g ; simpl ; simpl in H ; try discriminate H.
      specialize (IH g).
      specialize (IH H).
      rewrite IH.
      reflexivity.
    - intros g H.
      destruct g ; simpl ; simpl in H ; try discriminate H.
      rewrite Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      specialize (IH1 g1 H1).
      specialize (IH2 g2 H2).
      rewrite IH1, IH2.
      reflexivity.
    - intros g H.
      destruct g ; simpl ; simpl in H ; try discriminate H.
      rewrite Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      specialize (IH1 g1 H1).
      specialize (IH2 g2 H2).
      rewrite IH1, IH2.
      reflexivity.
  Qed.

  Lemma formula_eqb_eq_right {atom : Type} `{Heq : EqDec atom} : 
    forall f g : @formula atom, f = g -> formula_eqb f g = true.
  Proof.
    intros f g H.
    revert g H.
    induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2] ; intros g H.
    (* atom *)
    - rewrite <-H.
      simpl.
      rewrite eqb_reflexive.
      reflexivity.
    (* f_not *)
    - simpl.
      rewrite <-H.
      specialize (IH f').
      specialize (IH eq_refl).
      exact IH.
    (* f_conj *)
    - simpl.
      rewrite <-H.
      rewrite Bool.andb_true_iff.
      split.
      + specialize (IH1 f1).
        specialize (IH1 eq_refl).
        exact IH1.
      + specialize (IH2 f2).
        specialize (IH2 eq_refl).
        exact IH2.
    (* f_disj *)
    - simpl.
      rewrite <-H.
      rewrite Bool.andb_true_iff.
      split.
      + specialize (IH1 f1).
        specialize (IH1 eq_refl).
        exact IH1.
      + specialize (IH2 f2).
        specialize (IH2 eq_refl).
        exact IH2.
  Qed.

  Lemma formula_eqb_eq {atom : Type} `{Heq : EqDec atom} : 
    forall f g : @formula atom, formula_eqb f g = true <-> f = g.
  Proof.
    split.
    - apply formula_eqb_eq_left.
    - apply formula_eqb_eq_right.
  Qed.

  Global Instance EqDec_formula {atom : Type} `{EqDec atom} : EqDec (@formula atom) :=
  {
    eqb := formula_eqb;
    eqb_eq := formula_eqb_eq
  }.
End FormulaDef.

Module FDE_Formula := Make_Formula(FormulaDef).

Export FDE_Formula.