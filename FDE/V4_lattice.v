From FDE Require Import Formula.
From FDE Require Import Semantics.
From Lattices Require Import Order.
Import Lattice_LE.

Import V4Semantic.
Import FDE_V4 (V4, One, Zero, Both, None).

Module V4Lattice.
Module V4Lattice.  Inductive le_v4 : V4 -> V4 -> Prop :=
  | le_t_refl : forall x, le_v4 x x
  | le_t_zero : forall x, le_v4 Zero x
  | le_t_one : forall x, le_v4 x One.

  Instance v4Le : Le V4 := {
  le_lat := le_v4;
  }.

  Proposition le_v4_trans : forall x y z : V4, le_v4 x y -> le_v4 y z -> le_v4 x z.
  Proof.
    intros x y z H1 H2.
    inversion H1 ; subst.
    - inversion H2 ; subst.
      + apply le_t_refl.
      + apply le_t_zero.
      + apply le_t_one.
    - apply le_t_zero.
    - inversion H2 ; subst.
      + apply le_t_one.
      + apply le_t_one.
  Qed.

  Proposition le_v4_le_antisym : forall x y : V4, le_v4 x y -> le_v4 y x -> x = y.
  Proof.
    intros x y H1 H2.
    inversion H1 ; subst.
    - reflexivity.
    - inversion H2 ; subst ; reflexivity.
    - inversion H2 ; subst ; reflexivity.
  Qed.

  Instance v4PO : PartialOrder V4 := {
  le_refl := le_t_refl;
  le_trans := le_v4_trans;
  le_antisym := le_v4_le_antisym;
  }.

    Theorem le_disj_left : forall x y : V4,  le_v4 x (FDE_V4.disj x y).
  Proof.
    intros x y.
    destruct x.
    - apply le_t_zero.
    - destruct y ; simpl.
      + apply le_t_refl.
      + apply le_t_refl.
      + apply le_t_one.
      + apply le_t_one.
    - destruct y ; simpl.
      + apply le_t_refl.
      + apply le_t_one.
      + apply le_t_refl.
      + apply le_t_one.
    - apply le_t_one.
  Qed.

  Theorem le_disj_right : forall x y : V4,  le_v4 y (FDE_V4.disj x y).
  Proof.
    intros x y.
    destruct y.
    - apply le_t_zero.
    - destruct x ; simpl.
      + apply le_t_refl.
      + apply le_t_refl.
      + apply le_t_one.
      + apply le_t_one.
    - destruct x ; simpl.
      + apply le_t_refl.
      + apply le_t_one.
      + apply le_t_refl.
      + apply le_t_one.
    - destruct x ; simpl ; apply le_t_one.
  Qed.

  Theorem disj_same: forall x : V4, FDE_V4.disj x x = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem disj_comm: forall x y: V4, FDE_V4.disj x y = FDE_V4.disj y x.
  Proof.
    destruct x, y ; simpl ; reflexivity.
  Qed.

  Theorem disj_zero: forall x : V4, FDE_V4.disj x Zero = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem disj_one: forall x : V4, FDE_V4.disj x One = One.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem conj_same: forall x : V4, FDE_V4.conj x x = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem conj_comm: forall x y: V4, FDE_V4.conj x y = FDE_V4.conj y x.
  Proof.
    destruct x, y ; simpl ; reflexivity.
  Qed.

  Theorem conj_zero: forall x : V4, FDE_V4.conj x Zero = Zero.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem conj_one: forall x : V4, FDE_V4.conj x One = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem disj_supremum : forall x y z, (le_v4 x z) -> (le_v4 y z) -> le_v4 (FDE_V4.disj x y) z.
  Proof.
    intros x y z H1 H2.
    inversion H1 ; subst.
    - inversion H2 ; subst.
      + rewrite disj_same.
        apply le_t_refl.
      + rewrite disj_zero.
        apply le_t_refl.
      + rewrite disj_comm.
        rewrite disj_one.
        apply le_t_refl.
    - rewrite disj_comm.
      rewrite disj_zero.
      exact H2.
    - apply le_t_one.
  Qed.

  Theorem le_conj_left : forall x y : V4,  le_v4 (FDE_V4.conj x y) x.
  Proof.
    intros x y.
    destruct x.
    - rewrite conj_comm.
      rewrite conj_zero.
      apply le_t_refl.
    - destruct y ; simpl.
      + apply le_t_zero.
      + apply le_t_refl.
      + apply le_t_zero.
      + apply le_t_refl.
    - destruct y ; simpl.
      + apply le_t_zero.
      + apply le_t_zero.
      + apply le_t_refl.
      + apply le_t_refl.
    - apply le_t_one.
  Qed.

  Theorem le_conj_right : forall x y : V4,  le_v4 (FDE_V4.conj x y) y.
  Proof.
    intros x y.
    destruct y.
    - rewrite conj_zero.
      apply le_t_refl.
    - destruct x ; simpl.
      + apply le_t_zero.
      + apply le_t_refl.
      + apply le_t_zero.
      + apply le_t_refl.
    - destruct x ; simpl.
      + apply le_t_zero.
      + apply le_t_zero.
      + apply le_t_refl.
      + apply le_t_refl.
    - apply le_t_one.
  Qed.

  Theorem conj_infimum : forall x y z, le_v4 z x -> le_v4 z y -> le_v4 z (FDE_V4.conj x y).
  Proof.
    intros x y z H1 H2.
    inversion H1 ; subst.
    - inversion H2 ; subst.
      + rewrite conj_same.
        apply le_t_refl.
      + apply le_t_zero.
      + rewrite conj_one.
        apply le_t_refl.
    - apply le_t_zero.
    - rewrite conj_comm.
      rewrite conj_one.
      exact H2.
  Qed.

  Instance V4_Lattice : Lattice V4 :=
  {
    join := FDE_V4.disj;
    meet := FDE_V4.conj;
    le_join_left := le_disj_left;
    le_join_right := le_disj_right;
    A2 := disj_supremum;
    le_meet_left := le_conj_left;
    le_meet_right := le_conj_right;
    A4 := conj_infimum;
  }.

  Theorem neg_involutive : forall a : V4, FDE_V4.neg (FDE_V4.neg a) = a.
  Proof.
    intro a.
    destruct a ; auto.
  Qed.

End V4Lattice.
