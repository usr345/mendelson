From Basis Require Import Sets.
From Lattices Require Import Order.
From FDE Require Import Formula.
From Coq Require Import Lists.List.
Import ListNotations.
Import FormulaDef.
Import FDE_Formula.

Module RelSemantic.
  (*
    Возвращает true, если данное булево значение привязано к атому
  *)
  Record Model {atom : Type} :=
  {
    ρ : atom -> bool -> bool;
  }.

  Fixpoint eval {atom : Type} (M: @Model atom) (f : formula) (b : bool) : bool :=
    match f with
    | f_atom A => ρ M A b
    | f_not f' => eval M f' (negb b)
    | f_conj f g =>
        match b with
        | true => (eval M f true) && (eval M g true)
        | false => (eval M f false) || (eval M g false)
        end
    | f_disj f g =>
        match b with
        | true => (eval M f true) || (eval M g true)
        | false => (eval M f false) && (eval M g false)
        end
  end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : @Model atom), eval M f true = true.

  Declare Scope rel_scope.
  #[global] Notation "|= f" := (valid f) (at level 90) : rel_scope.

  Definition holds_all {atom : Type} (M : @Model atom) (Γ : list formula) : Prop := forall f : @formula atom, In f Γ -> eval M f true = true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : @Model atom), holds_all M Γ -> eval M f true = true.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : rel_scope.

  Lemma HoldsAll1 {atom : Type} (M : @Model atom) (f : @formula atom) : holds_all M [f] <-> eval M f true = true.
  Proof.
    split.
    - intro H.
      unfold holds_all in H.
      specialize (H f).
      specialize (in_eq f nil) as H1.
      specialize (H H1).
      exact H.
    - intro H.
      unfold holds_all.
      intros f1 H1.
      unfold In in H1.
      destruct H1 as [H1 | []].
      rewrite <-H1.
      exact H.
  Qed.

End RelSemantic.

Module StarSemantic.
  Record Model {atom : Type} :=
  {
    worlds : Type;
    w0 : worlds;
    star : worlds -> worlds;
    star_involutive : forall w : worlds, star (star w) = w;
    v : atom -> worlds -> bool;
  }.

  Fixpoint eval {atom : Type} (M: @Model atom) (f : formula) (w : worlds M) : bool :=
    match f with
    | f_atom A => M.(v) A w
    | f_not f' => negb (eval M f' (M.(star) w))
    | f_conj f g => andb (eval M f w) (eval M g w)
    | f_disj f g => orb (eval M f w) (eval M g w)
  end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : @Model atom) (w : M.(worlds)), eval M f w = true.

  Declare Scope star_scope.
  #[global] Notation "|= f" := (valid f) (at level 90) : star_scope.

  Definition holds_all {atom : Type} (M : @Model atom) (Γ : list formula) (w : M.(worlds)) : Prop := forall f : @formula atom, In f Γ -> eval M f w = true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : @Model atom) (w : M.(worlds)),
      holds_all M Γ w -> eval M f w = true.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : star_scope.

  Lemma HoldsAll1 {atom : Type} (M : @Model atom) (w : M.(worlds)) (f : @formula atom) : holds_all M [f] w <-> eval M f w = true.
  Proof.
    split.
    - intro H.
      unfold holds_all in H.
      specialize (H f).
      specialize (in_eq f nil) as H1.
      specialize (H H1).
      exact H.
    - intro H.
      unfold holds_all.
      intros f1 H1.
      unfold In in H1.
      destruct H1 as [H1 | []].
      rewrite <-H1.
      exact H.
  Qed.
End StarSemantic.

Import Lattice_LE.

Module FDE_V4.
  Variant V4 : Type := Zero | None | Both | One.
  Scheme Equality for V4.

  Inductive le_v4 : V4 -> V4 -> Prop :=
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

  Definition designated (v : V4) : Prop :=
    v = One \/ v = Both.

  Definition neg (a : V4) : V4 :=
    match a with
    | Zero => One
    | None => None
    | Both => Both
    | One => Zero
    end.

  Definition conj (a b : V4) : V4 :=
    match a, b with
    | Zero, _ => Zero
    | _, Zero => Zero
    | None, None => None
    | None, Both => Zero
    | None, One => None
    | Both, None => Zero
    | Both, Both => Both
    | Both, One => Both
    | One, None => None
    | One, Both => Both
    | One, One => One
    end.

  Definition disj (a b : V4) : V4 :=
    match a, b with
    | One, _ => One
    | _, One => One
    | None, Zero => None
    | None, None => None
    | None, Both => One
    | Both, Zero => Both
    | Both, None => One
    | Both, Both => Both
    | Zero, Zero => Zero
    | Zero, None => None
    | Zero, Both => Both
    end.

  Inductive neg_rel : V4 -> V4 -> Prop :=
  | neg_zero : neg_rel Zero One
  | neg_none : neg_rel None None
  | neg_both : neg_rel Both Both
  | neg_one  : neg_rel One Zero.

  Inductive conj_rel : V4 -> V4 -> V4 -> Prop :=
  | conj_zero_l : forall x, conj_rel Zero x Zero
  | conj_zero_r : forall x, conj_rel x Zero Zero
  | conj_none_none : conj_rel None None None
  | conj_none_both : conj_rel None Both Zero
  | conj_none_one  : conj_rel None One None
  | conj_both_none : conj_rel Both None Zero
  | conj_both_both : conj_rel Both Both Both
  | conj_both_one  : conj_rel Both One Both
  | conj_one_none  : conj_rel One None None
  | conj_one_both  : conj_rel One Both Both
  | conj_one_one   : conj_rel One One One.

  Inductive disj_rel : V4 -> V4 -> V4 -> Prop :=
  | disj_one_l : forall x, disj_rel One x One
  | disj_one_r : forall x, disj_rel x One One
  | disj_none_zero  : disj_rel None Zero None
  | disj_none_none : disj_rel None None None
  | disj_none_both : disj_rel None Both One
  | disj_both_zero  : disj_rel Both Zero Both
  | disj_both_none : disj_rel Both None One
  | disj_both_both : disj_rel Both Both Both
  | disj_zero_zero  : disj_rel Zero Zero Zero
  | disj_zero_none  : disj_rel Zero None None
  | disj_zero_both   : disj_rel Zero Both Both.

  Lemma neg_rel_fun_equiv :
    forall a b, neg_rel a b <-> neg a = b.
  Proof.
    intros a b.
    split ; intro H.
    - destruct a, b ; simpl ; try reflexivity ; try inversion H.
    - destruct a, b ; simpl in H ; try discriminate H.
      + apply neg_zero.
      + apply neg_none.
      + apply neg_both.
      + apply neg_one.
  Qed.

  Lemma conj_rel_fun_equiv :
    forall a b c, conj_rel a b c <-> conj a b = c.
  Proof.
    intros a b c.
    split ; intro H.
    - destruct a, b, c ; simpl ; try reflexivity ; try inversion H.
    - destruct a, b, c ; simpl in H ; try discriminate H ; try constructor.
  Qed.

  Lemma disj_rel_fun_equiv :
    forall a b c, disj_rel a b c <-> disj a b = c.
  Proof.
    intros a b c.
    split ; intro H.
    - destruct a, b, c ; simpl ; try reflexivity ; try inversion H.
    - destruct a, b, c ; simpl in H ; try discriminate H ; try constructor.
  Qed.

  Theorem le_disj_left : forall x y : V4,  le_v4 x (disj x y).
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

  Theorem le_disj_right : forall x y : V4,  le_v4 y (disj x y).
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

  Theorem disj_same: forall x : V4, disj x x = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem disj_comm: forall x y: V4, disj x y = disj y x.
  Proof.
    destruct x, y ; simpl ; reflexivity.
  Qed.

  Theorem disj_zero: forall x : V4, disj x Zero = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem disj_one: forall x : V4, disj x One = One.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem conj_same: forall x : V4, conj x x = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem conj_comm: forall x y: V4, conj x y = conj y x.
  Proof.
    destruct x, y ; simpl ; reflexivity.
  Qed.

  Theorem conj_zero: forall x : V4, conj x Zero = Zero.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem conj_one: forall x : V4, conj x One = x.
  Proof.
    destruct x ; simpl ; reflexivity.
  Qed.

  Theorem disj_supremum : forall x y z, (le_v4 x z) -> (le_v4 y z) -> le_v4 (disj x y) z.
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

  Theorem le_conj_left : forall x y : V4,  le_v4 (conj x y) x.
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

  Theorem le_conj_right : forall x y : V4,  le_v4 (conj x y) y.
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

  Theorem conj_infimum : forall x y z, le_v4 z x -> le_v4 z y -> le_v4 z (conj x y).
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
    join := disj;
    meet := conj;
    le_join_left := le_disj_left;
    le_join_right := le_disj_right;
    A2 := disj_supremum;
    le_meet_left := le_conj_left;
    le_meet_right := le_conj_right;
    A4 := conj_infimum;
  }.

  Theorem neg_involutive : forall a : V4, neg (neg a) = a.
  Proof.
    intro a.
    destruct a ; auto.
  Qed.

  Theorem conj_one_iff : forall a b : V4, conj a b = One <-> a = One /\ b = One.
  Proof.
    intros a b.
    split ; intro H.
    - destruct a, b ; simpl in H ; try discriminate H.
      split ; exact H.
    - destruct H as [H1 H2].
      rewrite H1.
      rewrite H2.
      simpl.
      reflexivity.
  Qed.

  Theorem conj_zero_iff : forall a b : V4, conj a b = Zero <-> a = Zero \/ b = Zero \/ (a = Both /\ b = None) \/ (a = None /\ b = Both).
  Proof.
    intros a b.
    split ; intro H.
    - destruct a, b ; simpl in H ; try discriminate H ; auto.
    - destruct H as [H | [H | [H | H]]].
      + rewrite H.
        destruct b ; auto.
      + rewrite H.
        destruct a ; auto.
      + destruct H as [H1 H2].
        rewrite H1, H2.
        simpl.
        reflexivity.
      + destruct H as [H1 H2].
        rewrite H1, H2.
        simpl.
        reflexivity.
  Qed.

  Theorem disj_zero_iff : forall a b : V4, disj a b = Zero <-> a = Zero /\ b = Zero.
  Proof.
    intros a b.
    split ; intro H.
    - destruct a, b ; simpl in H ; try discriminate H.
      split ; exact H.
    - destruct H as [H1 H2].
      rewrite H1.
      rewrite H2.
      simpl.
      reflexivity.
  Qed.

  Theorem disj_one_iff : forall a b : V4, disj a b = One <-> a = One \/ b = One \/ (a = Both /\ b = None) \/ (a = None /\ b = Both).
  Proof.
    intros a b.
    split ; intro H.
    - destruct a, b ; simpl in H ; try discriminate H ; auto.
    - destruct H as [H | [H | [H | H]]].
      + rewrite H.
        destruct b ; auto.
      + rewrite H.
        destruct a ; auto.
      + destruct H as [H1 H2].
        rewrite H1, H2.
        simpl.
        reflexivity.
      + destruct H as [H1 H2].
        rewrite H1, H2.
        simpl.
        reflexivity.
  Qed.
End FDE_V4.

Module V4Semantic.
  Import FDE_V4.

  Record Model {atom : Type} :=
  {
    v : atom -> V4;
  }.

  Fixpoint eval {atom : Type} (M: @Model atom) (f : formula) : V4 :=
    match f with
    | f_atom A => v M A
    | f_not f' => neg (eval M f')
    | f_conj f g => FDE_V4.conj (eval M f) (eval M g)
    | f_disj f g => FDE_V4.disj (eval M f) (eval M g)
    end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : @Model atom), designated (eval M f).

  Declare Scope V4_scope.
  #[global] Notation "|= f" := (valid f) (at level 90) : V4_scope.

  Definition holds_all {atom : Type} (M : @Model atom) (Γ : list formula) : Prop := forall f : @formula atom, In f Γ -> designated (eval M f).

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : @Model atom),
      holds_all M Γ -> designated (eval M f).

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : V4_scope.

  Lemma HoldsAll1 {atom : Type} (M : @Model atom) (f : @formula atom) : holds_all M [f] <-> designated (eval M f).
  Proof.
    split.
    - intro H.
      unfold holds_all in H.
      specialize (H f).
      specialize (in_eq f nil) as H1.
      specialize (H H1).
      exact H.
    - intro H.
      unfold holds_all.
      intros f1 H1.
      unfold In in H1.
      destruct H1 as [H1 | []].
      rewrite <-H1.
      exact H.
  Qed.

End V4Semantic.
