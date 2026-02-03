From Mendelson Require Import FSignature.
From Mendelson Require Import FDE_formula.
From Mendelson Require Import FDE_semantics.
From Mendelson Require Import FDE_syntactic.
From Mendelson Require Import FDE_semantic_equiv.
From Stdlib Require Import Lists.List.
Import ListNotations.
Import FDE_FormulaDef.
Import FDE_Formula.
Import Syntactic.
Import StarSemantic.
Import RelStarEquiv.

Module Meta_star.

  Open Scope star_scope.
  Proposition axiom1_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= A.
  Proof.
    unfold consequence.
    intros M w H.

    rewrite HoldsAll1 in H.
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H _].
    exact H.
  Qed.

  Proposition axiom2_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= B.
  Proof.
    unfold consequence.
    intros M w H.

    rewrite HoldsAll1 in H.
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [_ H].
    exact H.
  Qed.

  Proposition axiom3_tautology {atom : Set} (A B: @formula atom) : [A] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M w H.

    rewrite HoldsAll1 in H.
    simpl.
    rewrite Bool.orb_true_iff.
    left.
    exact H.
  Qed.

  Proposition axiom4_tautology {atom : Set} (A B: @formula atom) : [B] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M w H.

    rewrite HoldsAll1 in H.
    simpl.
    rewrite Bool.orb_true_iff.
    right.
    exact H.
  Qed.

  Proposition axiom5_tautology {atom : Set} (A B C: @formula atom) : [$A /\ (B \/ C)$] |= $(A /\ B) \/ C$.
  Proof.
    unfold consequence.
    intros M w H.

    rewrite HoldsAll1 in H.
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    rewrite Bool.orb_true_iff in H.
    destruct H as [H1 H2].

    simpl.
    rewrite Bool.orb_true_iff.
    rewrite Bool.andb_true_iff.

    destruct H2 as [H2 | H2].
    - left.
      exact (conj H1 H2).
    - right.
      exact H2.
  Qed.

  Proposition axiom6_tautology {atom : Set} (A: @formula atom) : [A] |= $~~A$.
  Proof.
    unfold consequence.
    intros M w H.

    rewrite HoldsAll1 in H.
    simpl in H.
    simpl.
    rewrite Bool.negb_involutive.
    rewrite star_involutive.
    exact H.
  Qed.


  Proposition axiom7_tautology {atom : Set} (A: @formula atom) : [$~~A$] |= A.
  Proof.
    unfold consequence.
    intros M w H.

    rewrite HoldsAll1 in H.
    simpl in H.
    rewrite Bool.negb_involutive in H.
    rewrite star_involutive in H.
    exact H.
  Qed.

  Proposition trans_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= B -> [B] |= C -> [A] |= C.
  Proof.
    unfold consequence.
    intros H1 H2.
    intros M w.
    intro H3.

    specialize (H1 M w).
    specialize (H2 M w).
    rewrite HoldsAll1 in H1.
    rewrite HoldsAll1 in H2.
    rewrite HoldsAll1 in H3.

    specialize (H1 H3).
    specialize (H2 H1).
    exact H2.
  Qed.

  Proposition conj_intro_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= B -> [A] |= C -> [A] |= $B /\ C$.
  Proof.
    unfold consequence.
    intros H1 H2.
    intros M w.
    intro H3.

    specialize (H1 M w).
    specialize (H2 M w).
    rewrite HoldsAll1 in H1.
    rewrite HoldsAll1 in H2.
    rewrite HoldsAll1 in H3.

    specialize (H1 H3).
    specialize (H2 H3).

    simpl.
    rewrite Bool.andb_true_iff.
    exact (conj H1 H2).
  Qed.


  Proposition case_analysis_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= C -> [B] |= C -> [$A \/ B$] |= C.
  Proof.
    unfold consequence.
    intros H1 H2.
    intros M w.
    intro H3.

    specialize (H1 M w).
    specialize (H2 M w).
    rewrite HoldsAll1 in H1.
    rewrite HoldsAll1 in H2.
    rewrite HoldsAll1 in H3.

    simpl in H3.
    rewrite Bool.orb_true_iff in H3.
    destruct H3 as [H3 | H3].
    - specialize (H1 H3).
      exact H1.
    - specialize (H2 H3).
      exact H2.
  Qed.

  Proposition contrapos_tautology {atom : Set} (A B: @formula atom) :
    [A] |= B -> [$~B$] |= $~A$.
  Proof.
    intro H.
    unfold consequence.
    unfold consequence in H.

    intros M w H1.
    rewrite HoldsAll1 in H1.
    simpl in H1.
    rewrite Bool.negb_true_iff in H1.

    simpl.
    rewrite Bool.negb_true_iff.
    specialize (H M (star M w)).

    rewrite HoldsAll1 in H.
    destruct (eval M A (star M w)) eqn:Heq.
    - assert (H2 : true = true).
      {
        reflexivity.
      }

      specialize (H H2).
      rewrite H in H1.
      exact H1.
    - reflexivity.
  Qed.

  Theorem soundness {atom : Set} : forall (A B : @formula atom), A |- B -> [A] |= B.
  Proof.
    intros A B.
    intro H.
    induction H.
    - apply axiom1_tautology.
    - apply axiom2_tautology.
    - apply axiom3_tautology.
    - apply axiom4_tautology.
    - apply axiom5_tautology.
    - apply axiom6_tautology.
    - apply axiom7_tautology.
    - specialize (trans_tautology A B C) as H1.
      specialize (H1 IHentails1 IHentails2).
      exact H1.
    - specialize (conj_intro_tautology A B C) as H1.
      specialize (H1 IHentails1 IHentails2).
      exact H1.
    - specialize (case_analysis_tautology A B C) as H1.
      specialize (H1 IHentails1 IHentails2).
      exact H1.
    - specialize (contrapos_tautology A B) as H1.
      specialize (H1 IHentails).
      exact H1.
  Qed.

End Meta_star.

Import RelSemantic.

Module Meta_relational.
  Open Scope rel_scope.
  Proposition axiom1_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= A.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ B$).
    specialize (in_eq $A /\ B$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H _].
    exact H.
  Qed.

  Proposition axiom2_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= B.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ B$).
    specialize (in_eq $A /\ B$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [_ H].
    exact H.
  Qed.

  Proposition axiom3_tautology {atom : Set} (A B: @formula atom) : [A] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H A).
    specialize (in_eq A nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    rewrite Bool.orb_true_iff.
    left.
    exact H.
  Qed.

  Proposition axiom4_tautology {atom : Set} (A B: @formula atom) : [B] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H B).
    specialize (in_eq B nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    rewrite Bool.orb_true_iff.
    right.
    exact H.
  Qed.

  Proposition axiom5_tautology {atom : Set} (A B C: @formula atom) : [$A /\ (B \/ C)$] |= $(A /\ B) \/ C$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ (B \/ C)$).
    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    rewrite Bool.orb_true_iff.
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite Bool.orb_true_iff in H2.
    destruct H2 as [H2 | H2].
    - left.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
    - right.
      exact H2.
  Qed.

  Proposition axiom6_tautology {atom : Set} (A: @formula atom) : [A] |= $~~A$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H A).
    specialize (in_eq A nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    exact H.
  Qed.

  Proposition axiom7_tautology {atom : Set} (A: @formula atom) : [$~~A$] |= A.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $~~A$).
    specialize (in_eq $~~A$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
    exact H.
  Qed.

  Proposition trans_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= B -> [B] |= C -> [A] |= C.
  Proof.
    intros H1 H2.
    unfold consequence.
    intros M H3.
    unfold holds_all in H3.

    specialize (H3 A).
    specialize (in_eq A nil) as H4.
    specialize (H3 H4).
    clear H4.

    unfold consequence in H1.
    specialize (H1 M).

    rewrite HoldsAll1 in H1.
    specialize (H1 H3).

    unfold consequence in H2.
    specialize (H2 M).
    rewrite HoldsAll1 in H2.

    specialize (H2 H1).
    exact H2.
  Qed.

  Proposition conj_intro_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= B -> [A] |= C -> [A] |= $B /\ C$.
  Proof.
    intros H1 H2.
    unfold consequence.
    intros M H3.
    unfold holds_all in H3.

    specialize (H3 A).
    specialize (in_eq A nil) as H4.
    specialize (H3 H4).
    clear H4.

    unfold consequence in H1.
    specialize (H1 M).
    unfold consequence in H2.
    specialize (H2 M).

    rewrite HoldsAll1 in H1.
    specialize (H1 H3).

    rewrite HoldsAll1 in H2.
    specialize (H2 H3).

    simpl.
    rewrite Bool.andb_true_iff.
    exact (conj H1 H2).
  Qed.

  Proposition case_analysis_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= C -> [B] |= C -> [$A \/ B$] |= C.
  Proof.
    intros H1 H2.
    unfold consequence.
    intros M H3.
    unfold holds_all in H3.

    specialize (H3 $A \/ B$).
    specialize (in_eq $A \/ B$ nil) as H4.
    specialize (H3 H4).
    clear H4.

    simpl in H3.
    rewrite Bool.orb_true_iff in H3.
    destruct H3 as [H3 | H3].
    - unfold consequence in H1.
      specialize (H1 M).
      rewrite HoldsAll1 in H1.
      specialize (H1 H3).
      exact H1.
    - unfold consequence in H2.
      specialize (H2 M).
      rewrite HoldsAll1 in H2.
      specialize (H2 H3).
      exact H2.
  Qed.

  Proposition contrapos_tautology {atom : Set} (A B: @formula atom) :
    [A] |= B -> [$~B$] |= $~A$.
  Proof.
    intro H.
    rewrite RelStarEquiv.rel_star_equiv in H.
    rewrite RelStarEquiv.rel_star_equiv.
    specialize (Meta_star.contrapos_tautology A B) as H1.
    specialize (H1 H).
    exact H1.
  Qed.

  Theorem soundness {atom : Set} : forall (A B : @formula atom), A |- B -> [A] |= B.
  Proof.
    intros A B.
    intro H.
    induction H.
    - apply axiom1_tautology.
    - apply axiom2_tautology.
    - apply axiom3_tautology.
    - apply axiom4_tautology.
    - apply axiom5_tautology.
    - apply axiom6_tautology.
    - apply axiom7_tautology.
    - specialize (trans_tautology A B C) as H1.
      specialize (H1 IHentails1 IHentails2).
      exact H1.
    - specialize (conj_intro_tautology A B C) as H1.
      specialize (H1 IHentails1 IHentails2).
      exact H1.
    - specialize (case_analysis_tautology A B C) as H1.
      specialize (H1 IHentails1 IHentails2).
      exact H1.
    - specialize (contrapos_tautology A B) as H1.
      specialize (H1 IHentails).
      exact H1.
  Qed.

End Meta_relational.
