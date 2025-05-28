Require Import Setoid.

Module Export EqDec.

  Class EqDec A :=
  {
    eqb: A -> A -> bool;
    eqb_eq1 : forall x y, (eqb x y) = true -> x = y;
    eqb_eq2 : forall x y, x = y -> (eqb x y) = true
  }.

  Proposition eqb_reflexive {A : Type} `{EqDec A}: forall x : A, (eqb x x) = true.
  Proof.
    intro x.
    apply eqb_eq2.
    reflexivity.
  Qed.

  Proposition eqb_symmetric {A : Type} `{EqDec A}: forall x y : A, (eqb x y) = (eqb y x).
  Proof.
    intros x y.
    destruct (eqb x y) eqn:Heq.
    - apply eqb_eq1 in Heq.
      rewrite Heq.
      rewrite eqb_reflexive.
      reflexivity.
    - destruct (eqb y x) eqn:Heq1.
      + apply eqb_eq1 in Heq1.
        rewrite Heq1 in Heq.
        rewrite eqb_reflexive in Heq.
        discriminate Heq.
      + reflexivity.
  Qed.

  Proposition eqb_transitive {A : Type} `{EqDec A}: forall x y z : A, (eqb x y) = true -> (eqb y z) = true -> (eqb x z) = true.
  Proof.
    intros x y z H1 H2.
    apply eqb_eq1 in H1.
    rewrite <-H1 in H2.
    apply H2.
  Qed.

  Proposition eqb_false_neq {A : Type} `{EqDec A} : forall x y : A, (eqb x y) = false <-> x <> y.
  Proof.
    intros x y.
    split ; intro Heq.
    - intro Heq1.
      apply eqb_eq2 in Heq1.
      rewrite Heq1 in Heq.
      discriminate Heq.
    - destruct (eqb x y) eqn:Heq1.
      + apply eqb_eq1 in Heq1.
        assert (Htrue : true = true) by (reflexivity).
        apply Heq in Heq1.
        destruct Heq1.
      + reflexivity.
  Defined.
End EqDec.
Export EqDec.
