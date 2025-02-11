Require Import Classical.
From Mendelson Require Import Formula.

Module Semantic.
Fixpoint eval (value : atom -> bool) (f : formula) : bool :=
  match f with
  | f_atom a => value a
  | f_not f => negb (eval value f)
  | f_imp f1 f2 => implb (eval value f1) (eval value f2)
end.

Lemma eval_neg (v : atom -> bool) (A : formula) :
  (eval v $~A$) = negb (eval v A).
Proof.
  simpl.
  destruct (eval v A) ; reflexivity.
Qed.

Lemma eval_implication (v : atom -> bool) (A B : formula) :
  (eval v $A -> B$) = implb (eval v A) (eval v B).
Proof.
  simpl.
  destruct (eval v A), (eval v B) ; reflexivity.
Qed.

Lemma eval_disjunction (v : atom -> bool) (A B : formula) :
  (eval v $A \/ B$) = orb (eval v A) (eval v B).
Proof.
  simpl.
  destruct (eval v A), (eval v B) ; reflexivity.
Qed.

Lemma eval_conjunction (v : atom -> bool) (A B : formula) :
  (eval v $A /\ B$) = andb (eval v A) (eval v B).
Proof.
  simpl.
  destruct (eval v A), (eval v B) ; reflexivity.
Qed.

Lemma eval_equivalence (v : atom -> bool) (A B : formula) :
  (eval v $A <-> B$) = andb (implb (eval v A) (eval v B)) (implb (eval v B) (eval v A)).
Proof.
  simpl.
  destruct (eval v A), (eval v B) ; reflexivity.
Qed.

Lemma impl_false (v : atom -> bool) (A B : formula) :
  (eval v $A -> B$) = false <-> (eval v A) = true /\ (eval v B) = false.
Proof.
  split.
  - intros.
    simpl in H.
    destruct (eval v A), (eval v B) ; simpl in H; try discriminate H.
    split ; reflexivity.
  - intro H.
    destruct H as [H1 H2].
    simpl.
    rewrite H1, H2.
    simpl.
    reflexivity.
Qed.

Lemma disj_false (v : atom -> bool) (A B : formula) :
  (eval v $A \/ B$) = false <-> (eval v A) = false /\ (eval v B) = false.
Proof.
  split.
  - intro H.
    simpl in H.
    destruct (eval v A), (eval v B) ; simpl in H; try discriminate H.
    split ; reflexivity.
  - intro H.
    destruct H as [H1 H2].
    simpl.
    rewrite H1, H2.
    simpl.
    reflexivity.
Qed.

Lemma conj_true (v : atom -> bool) (A B : formula) :
  (eval v $A /\ B$) = true <-> (eval v A) = true /\ (eval v B) = true.
Proof.
  split.
  - intro H.
    simpl in H.
    destruct (eval v A), (eval v B) ; simpl in H; try discriminate H.
    split ; reflexivity.
  - intro H.
    destruct H as [H1 H2].
    simpl.
    rewrite H1, H2.
    simpl.
    reflexivity.
Qed.

Definition tautology (f : formula) :=
  forall v : atom -> bool, is_true (eval v f).

Definition contradictory (f : formula) :=
  forall v : atom -> bool, (eval v f) = false.

Definition logically_implies (A : formula) (B : formula) :=
  forall v : atom -> bool, is_true (eval v A) -> is_true (eval v B).

Definition logically_equivalent (A : formula) (B : formula) :=
  forall v : atom -> bool, (eval v A) = (eval v B).

Proposition P1_1 (A B: formula) : logically_implies A B <-> tautology $A -> B$.
Proof.
  unfold logically_implies, tautology.
  split.
  - intros.
    specialize H with v.
    unfold is_true.
    unfold is_true in H.
    simpl.
    destruct (eval v A), (eval v B).
    * simpl. reflexivity.
    * simpl.
      apply H.
      reflexivity.
    * simpl.
      reflexivity.
    * simpl.
      reflexivity.
  - intros.
    unfold is_true.
    specialize H with v.
    unfold is_true in H.
    unfold is_true in H0.
    simpl in H.
    rewrite H0 in H.
    destruct (eval v B).
    * reflexivity.
    * simpl in H.
      exact H.
Qed.

Proposition P1_2 (A B: formula) : logically_equivalent A B <-> tautology $A <-> B$.
Proof.
  unfold logically_equivalent.
  unfold tautology.
  split.
  - intros.
    unfold is_true.
    specialize H with v.
    simpl.
    destruct (eval v A), (eval v B).
    simpl in H.
    * simpl. reflexivity.
    * simpl.
      symmetry.
      exact H.
    * simpl.
      exact H.
    * simpl. reflexivity.
  - intros.
    specialize H with v.
    unfold is_true in H.
    simpl in H.
    destruct (eval v A), (eval v B).
    * reflexivity.
    * simpl in H.
      symmetry.
      exact H.
    * simpl in H.
      exact H.
    * reflexivity.
Qed.

Proposition P1_3 (A B C: formula) : tautology $(A <-> (~B \/ C)) -> (~A -> B)$.
Proof.
  unfold tautology.
  intros.
  unfold is_true.
  simpl.
  destruct (eval v A), (eval v B), (eval v C) ; reflexivity.
Qed.

Proposition P1_4 (v : atom -> bool) (Hatom: inhabited atom) : exists (A B C : formula), ~(tautology $(A -> (B \/ C)) \/ (A -> B)$).
Proof.
  destruct Hatom as [x].
  pose (T := f_imp (f_atom x) (f_atom x)).
  pose (F := f_not T).
  exists T.
  exists F.
  exists F.
  unfold tautology.
  intro H.
  specialize H with (fun _ => true).
  simpl in H.
  unfold is_true in H.
  discriminate H.
Qed.

Proposition P1_27 (A B C: formula) : logically_equivalent $A -> B -> C$ $(A /\ B) -> C$.
Proof.
  unfold logically_equivalent.
  intros.
  simpl.
  destruct (eval v A), (eval v B), (eval v C); simpl ; reflexivity.
Qed.

Proposition P1_27_2 (A B C: formula) : logically_equivalent $A /\ (B \/ C)$ $(A /\ B) \/ (A /\ C)$.
Proof.
  unfold logically_equivalent.
  intros.
  simpl.
  destruct (eval v A), (eval v B), (eval v C); simpl ; reflexivity.
Qed.

Proposition P1_27_3 (T A: formula) : tautology T -> logically_equivalent $T /\ A$ A.
Proof.
  unfold tautology.
  unfold logically_equivalent.
  intros.
  simpl.
  specialize H with v.
  unfold is_true in H.
  rewrite H.
  destruct (eval v A).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Proposition P1_27_4 (T A: formula) : tautology T -> logically_equivalent $T \/ A$ T.
Proof.
  unfold tautology.
  unfold logically_equivalent.
  intros.
  simpl.
  specialize H with v.
  unfold is_true in H.
  rewrite H.
  simpl.
  destruct (eval v A).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Proposition P1_27_5 (T A: formula) : contradictory T -> logically_equivalent $T /\ A$ T.
Proof.
  unfold contradictory.
  unfold logically_equivalent.
  intros.
  simpl.
  specialize H with v.
  unfold is_true in H.
  rewrite H.
  simpl.
  destruct (eval v A).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Proposition P1_27_6 (T A: formula) : contradictory T -> logically_equivalent $T \/ A$ A.
Proof.
  unfold contradictory.
  unfold logically_equivalent.
  intros.
  simpl.
  specialize H with v.
  unfold is_true in H.
  rewrite H.
  simpl.
  destruct (eval v A).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End Semantic.
Export Semantic.
