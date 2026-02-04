From Mendelson Require Import FSignature.
From Mendelson Require Import Sets.
From Mendelson Require Import FDE_formula.
From Coq Require Import Lists.List.
Import ListNotations.
Import FDE_FormulaDef.
Import FDE_Formula.

Module RelSemantic.
  (*
    Возвращает true, если данное булево значение привязано к атому
  *)
  Record Model (atom : Type) :=
  {
    ρ : atom -> bool -> bool;
  }.

  Fixpoint eval {atom : Type} (M: Model atom) (f : formula) (b : bool) : bool :=
    match f with
    | f_atom A => ρ atom M A b
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

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : Model atom), eval M f true = true.

  Declare Scope rel_scope.
  #[global] Notation "|= f" := (valid f) (at level 90) : rel_scope.

  Definition holds_all {atom : Type} (M : Model atom) (Γ : list formula) : Prop := forall f : @formula atom, In f Γ -> eval M f true = true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : Model atom), holds_all M Γ -> eval M f true = true.

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

  Definition convert1 {atom : Type} (M : @StarSemantic.Model atom) (w : M.(worlds)) : RelSemantic.Model atom :=
      let ρ1 :=
            fun (a : atom) (val : bool) =>
              match val with
              | true => (M.(v) a w)
              | false => negb (M.(v) a (M.(star) w))
              end
      in
        RelSemantic.Build_Model atom ρ1.

  Variant TrueWorlds : Type := TrueWorld | TrueWorld'.

  Definition true_star (w : TrueWorlds) : TrueWorlds :=
  match w with
  | TrueWorld => TrueWorld'
  | TrueWorld' => TrueWorld
  end.

  Lemma true_star_involutive : forall w : TrueWorlds, true_star (true_star w) = w.
  Proof.
    intro w.
    destruct w.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Definition convert2 {atom : Type} (M : RelSemantic.Model atom) : @StarSemantic.Model atom :=
      let v :=
            fun (a : atom) (w : TrueWorlds) =>
              match w with
              | TrueWorld => RelSemantic.ρ atom M a true
              | TrueWorld' => negb (RelSemantic.ρ atom M a false)
              end
      in
        StarSemantic.Build_Model atom TrueWorlds TrueWorld true_star true_star_involutive v.

  Variant atom3 : Set := P | Q | R.

  Definition f (a: atom3) : @formula atom3 :=
    f_atom a.

  Coercion f: atom3 >-> formula.

  Definition ρ1 (a : atom3) (val : bool) :=
    match a, val with
    | P, _ => true
    | _, _ => false
    end.

  Definition M1 := RelSemantic.Build_Model atom3 ρ1.

  Example Test1 : (v (convert2 M1) P TrueWorld) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example Test2 : (v (convert2 M1) P TrueWorld') = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example Test3 : forall A : atom3, ~(A = P) -> (v (convert2 M1) A TrueWorld) = false.
  Proof.
    intros A H.
    destruct A.
    - contradiction.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Example Test4 : forall A : atom3, ~(A = P) -> (v (convert2 M1) A TrueWorld') = true.
  Proof.
    intros A H.
    destruct A.
    - contradiction.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Example Test5 : (RelSemantic.ρ atom3 (convert1 (convert2 M1) TrueWorld) P true) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example Test6 : (RelSemantic.ρ atom3 (convert1 (convert2 M1) TrueWorld) P false) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example Test7 : forall (A : atom3) (b : bool), ~(A = P) -> (RelSemantic.ρ atom3 (convert1 (convert2 M1) TrueWorld) A b) = false.
  Proof.
    intros A b H.
    destruct A.
    - contradiction.
    - destruct b ; simpl ; reflexivity.
    - destruct b ; simpl ; reflexivity.
  Qed.

  Lemma ρ_eq {atom : Type} (M : RelSemantic.Model atom) :
    let
      StarM := (convert2 M)
    in
      forall (A : atom) (b : bool),
      RelSemantic.ρ atom M A b = RelSemantic.ρ atom (convert1 StarM TrueWorld) A b.
  Proof.
    intros StarM A b.
    simpl.
    rewrite Bool.negb_involutive.
    destruct b ; reflexivity.
  Qed.

  Lemma eval_eq {atom : Type} (M1 M2 : RelSemantic.Model atom)
    (f : formula) (b : bool) (Hρ : forall A b, RelSemantic.ρ atom M1 A b =
                                         RelSemantic.ρ atom M2 A b) :
    RelSemantic.eval M1 f b = RelSemantic.eval M2 f b.
  Proof.
    revert b.
    induction f ; intro b.
    - simpl.
      specialize (Hρ a b).
      exact Hρ.
    - simpl.
      specialize (IHf (negb b)).
      exact IHf.
    - simpl.
      destruct b.
      + rewrite IHf1.
        rewrite IHf2.
        reflexivity.
      + rewrite IHf1.
        rewrite IHf2.
        reflexivity.
    - simpl.
      destruct b.
      + rewrite IHf1.
        rewrite IHf2.
        reflexivity.
      + rewrite IHf1.
        rewrite IHf2.
        reflexivity.
  Qed.

End StarSemantic.

Module FDE_V4.
  Variant V4 : Type := Zero | None | Both | One.
  Scheme Equality for V4.

  Inductive le_t : V4 -> V4 -> Prop :=
  | le_t_refl : forall x, le_t x x
  | le_t_ZN : le_t Zero None
  | le_t_ZB : le_t Zero Both
  | le_t_NO : le_t None One
  | le_t_BO : le_t Both One.

  Instance PO_V4_truth : PartialOrder V4.

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

Module FourValuedSemantic.
  Import V4.

  Record Model (atom : Type) :=
  {
    v : atom -> V4;
  }.

  Fixpoint eval {atom : Type} (M: Model atom) (f : formula) : V4 :=
    match f with
    | f_atom A => v atom M A
    | f_not f' => neg (eval M f')
    | f_conj f g => V4.conj (eval M f) (eval M g)
    | f_disj f g => V4.disj (eval M f) (eval M g)
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

  Lemma HoldsAll1 {atom : Type} (M : @Model atom) (f : @formula atom) : holds_all M [f] <-> eval M f = One.
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

End FourValuedSemantic.
