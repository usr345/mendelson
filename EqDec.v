Require Import Setoid.

Module Export EqDec.

  Class EqDec A :=
  {
    eqb: A -> A -> bool;
    eqb_eq : forall x y, (eqb x y) = true <-> x = y
  }.

  Proposition eqb_reflexive {A : Type} `{EqDec A}: forall x : A, (eqb x x) = true.
  Proof.
    intro x.
    rewrite eqb_eq.
    reflexivity.
  Qed.

  Proposition eqb_symmetric {A : Type} `{EqDec A}: forall x y : A, (eqb x y) = (eqb y x).
  Proof.
    intros x y.
    destruct (eqb x y) eqn:Heq.
    - rewrite eqb_eq in Heq.
      rewrite Heq.
      rewrite eqb_reflexive.
      reflexivity.
    - destruct (eqb y x) eqn:Heq1.
      + rewrite eqb_eq in Heq1.
        rewrite Heq1 in Heq.
        rewrite eqb_reflexive in Heq.
        discriminate Heq.
      + reflexivity.
  Qed.

  Proposition eqb_transitive {A : Type} `{EqDec A}: forall x y z : A, (eqb x y) = true -> (eqb y z) = true -> (eqb x z) = true.
  Proof.
    intros x y z H1 H2.
    rewrite eqb_eq in H1.
    rewrite <-H1 in H2.
    apply H2.
  Qed.

End EqDec.
Export EqDec.
