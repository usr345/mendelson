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

  Proposition eqb_symmetric {A : Type} `{EqDec A}: forall x y : A, (eqb x y) = true <-> (eqb y x) = true.
  Proof.
    intros x y.
    split ; intro H1.
    - rewrite eqb_eq in H1.
      rewrite <-H1.
      apply eqb_reflexive.
    - rewrite eqb_eq in H1.
      rewrite <-H1.
      apply eqb_reflexive.
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
