From Mendelson Require Import FDE_formula.
From Mendelson Require Import FDE_semantics.
Import FDE_FormulaDef.
Import FDE_Formula.
Import RelSemantic.
Import StarSemantic.

Definition convert_star_rel {atom : Type} (M : @StarSemantic.Model atom) (w : M.(worlds)) : RelSemantic.Model atom :=
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

Definition convert_rel_star {atom : Type} (M : RelSemantic.Model atom) : @StarSemantic.Model atom :=
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

Example Test1 : (v (convert_rel_star M1) P TrueWorld) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example Test2 : (v (convert_rel_star M1) P TrueWorld') = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example Test3 : forall A : atom3, ~(A = P) -> (v (convert_rel_star M1) A TrueWorld) = false.
Proof.
  intros A H.
  destruct A.
  - contradiction.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Example Test4 : forall A : atom3, ~(A = P) -> (v (convert_rel_star M1) A TrueWorld') = true.
Proof.
  intros A H.
  destruct A.
  - contradiction.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Example Test5 : (RelSemantic.ρ atom3 (convert_star_rel (convert_rel_star M1) TrueWorld) P true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example Test6 : (RelSemantic.ρ atom3 (convert_star_rel (convert_rel_star M1) TrueWorld) P false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example Test7 : forall (A : atom3) (b : bool), ~(A = P) -> (RelSemantic.ρ atom3 (convert_star_rel (convert_rel_star M1) TrueWorld) A b) = false.
Proof.
  intros A b H.
  destruct A.
  - contradiction.
  - destruct b ; simpl ; reflexivity.
  - destruct b ; simpl ; reflexivity.
Qed.

Lemma ρ_eq {atom : Type} (M : RelSemantic.Model atom) :
  let
    StarM := (convert_rel_star M)
  in
    forall (A : atom) (b : bool),
    RelSemantic.ρ atom M A b = RelSemantic.ρ atom (convert_star_rel StarM TrueWorld) A b.
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

Module RelStarEquiv.
  Lemma eval_rel_star_equiv {atom : Type} (f : @formula atom) (M : RelSemantic.Model atom) :
    forall b : bool,
    RelSemantic.eval M f b = true ->
    StarSemantic.eval (convert_rel_star M) f (if b then TrueWorld else TrueWorld') = b.
  Proof.
    induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2].
    - intros b H.
      destruct b ; simpl; simpl in H.
      + exact H.
      + rewrite Bool.negb_false_iff.
        exact H.
    - intros b H.
      simpl in H.
      destruct b; simpl.
      + rewrite Bool.negb_true_iff.
        simpl in H.
        specialize (IH false).
        specialize (IH H).
        simpl in IH.
        exact IH.
      + rewrite Bool.negb_false_iff.
        simpl in H.
        specialize (IH true).
        specialize (IH H).
        simpl in IH.
        exact IH.
    - intros b H.
      simpl.
      simpl in H.
      specialize (IH1 b).
      specialize (IH2 b).
      destruct b.
      + rewrite Bool.andb_true_iff.
        rewrite Bool.andb_true_iff in H.
        specialize (IH1 (proj1 H)).
        specialize (IH2 (proj2 H)).
        exact (conj IH1 IH2).
      + rewrite Bool.andb_false_iff.
        rewrite Bool.orb_true_iff in H.
        destruct H.
        * specialize (IH1 H).
          left.
          exact IH1.
        * specialize (IH2 H).
          right.
          exact IH2.
    - intros b H.
      simpl.
      simpl in H.
      specialize (IH1 b).
      specialize (IH2 b).
      destruct b.
      + rewrite Bool.orb_true_iff.
        rewrite Bool.orb_true_iff in H.
        destruct H.
        * specialize (IH1 H).
          left.
          exact IH1.
        * specialize (IH2 H).
          right.
          exact IH2.
      + rewrite Bool.orb_false_iff.
        rewrite Bool.andb_true_iff in H.
        specialize (IH1 (proj1 H)).
        specialize (IH2 (proj2 H)).
        exact (conj IH1 IH2).
  Qed.

  Lemma eval_star_rel_equiv {atom : Type} (f : @formula atom) (M : @StarSemantic.Model atom) (w : M.(worlds)) :
    forall b : bool,
    StarSemantic.eval M f (if b then w else (M.(star) w)) = b ->
    RelSemantic.eval (convert_star_rel M w) f b = true.
  Proof.
    induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2].
    - intros b H.
      destruct b ; simpl; simpl in H.
      + exact H.
      + rewrite Bool.negb_true_iff.
        exact H.
    - intros b H.
      simpl in H.
      destruct b; simpl.
      + rewrite Bool.negb_true_iff in H.
        specialize (IH false).
        simpl in IH.
        specialize (IH H).
        exact IH.
      + rewrite Bool.negb_false_iff in H.
        specialize (IH true).
        simpl in IH.
        rewrite star_involutive in H.
        specialize (IH H).
        exact IH.
    - intros b H.
      simpl.
      simpl in H.
      specialize (IH1 b).
      specialize (IH2 b).
      destruct b.
      + rewrite Bool.andb_true_iff.
        rewrite Bool.andb_true_iff in H.
        specialize (IH1 (proj1 H)).
        specialize (IH2 (proj2 H)).
        exact (conj IH1 IH2).
      + rewrite Bool.orb_true_iff.
        rewrite Bool.andb_false_iff in H.
        destruct H.
        * specialize (IH1 H).
          left.
          exact IH1.
        * specialize (IH2 H).
          right.
          exact IH2.
    - intros b H.
      simpl.
      simpl in H.
      specialize (IH1 b).
      specialize (IH2 b).
      destruct b.
      + rewrite Bool.orb_true_iff.
        rewrite Bool.orb_true_iff in H.
        destruct H.
        * specialize (IH1 H).
          left.
          exact IH1.
        * specialize (IH2 H).
          right.
          exact IH2.
      + rewrite Bool.andb_true_iff.
        rewrite Bool.orb_false_iff in H.
        specialize (IH1 (proj1 H)).
        specialize (IH2 (proj2 H)).
        exact (conj IH1 IH2).
  Qed.

  Lemma holds_all_rel_star {atom : Type} (Γ : list (@formula atom)) (M : RelSemantic.Model atom) :
    RelSemantic.holds_all M Γ -> StarSemantic.holds_all (convert_rel_star M) Γ TrueWorld.
  Proof.
    intro H.
    unfold StarSemantic.holds_all.
    intros f H1.
    unfold RelSemantic.holds_all in H.
    specialize (H f H1).
    specialize (eval_rel_star_equiv f M true) as Heq.
    apply Heq in H.
    exact H.
  Qed.

  Lemma holds_all_star_rel {atom : Type} (Γ : list (@formula atom))
    (M : @StarSemantic.Model atom) (w : M.(worlds)) : StarSemantic.holds_all M Γ w -> RelSemantic.holds_all (convert_star_rel M w) Γ.
  Proof.
    intro H.
    unfold RelSemantic.holds_all.
    intros f H1.
    unfold StarSemantic.holds_all in H.
    specialize (H f H1).
    specialize (eval_star_rel_equiv f M w true) as Heq.
    apply Heq in H.
    exact H.
  Qed.

  Theorem star_rel_consequence {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) :
    StarSemantic.consequence Γ A -> RelSemantic.consequence Γ A.
  Proof.
    intro H.
    unfold StarSemantic.consequence in H.
    unfold RelSemantic.consequence.
    intros M H1.

    set (StarM := convert_rel_star M).
    specialize (H StarM).
    specialize (H TrueWorld).
    apply holds_all_rel_star in H1.
    specialize (H H1).
    clear H1.
    induction A.
    - simpl.
      simpl in H.
      exact H.
    - simpl.
      simpl in H.
      rewrite Bool.negb_true_iff in H.
      specialize (eval_star_rel_equiv A StarM TrueWorld false) as Heq.
      simpl in Heq.
      apply Heq in H.
      unfold StarM in H.
      specialize (eval_eq (convert_star_rel (convert_rel_star M) TrueWorld) M A false) as H1.
      assert (H2 : forall (A : atom) (b : bool),
                 RelSemantic.ρ atom (convert_star_rel (convert_rel_star M) TrueWorld) A b = RelSemantic.ρ atom M A b).
      {
        intros A1 b.
        symmetry.
        apply ρ_eq.
      }

      specialize (H1 H2).
      rewrite H1 in H.
      exact H.
    - simpl.
      simpl in H.
      rewrite Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      specialize (IHA1 H1).
      specialize (IHA2 H2).
      rewrite Bool.andb_true_iff.
      exact (conj IHA1 IHA2).
    - simpl.
      simpl in H.
      rewrite Bool.orb_true_iff.
      rewrite Bool.orb_true_iff in H.
      destruct H as [H | H].
      + specialize (IHA1 H).
        left.
        exact IHA1.
      + specialize (IHA2 H).
        right.
        exact IHA2.
  Qed.

  Lemma eval_star_roundtrip {atom : Type} (M : @StarSemantic.Model atom)
  (w : M.(worlds)) (f : formula) (u : (convert_rel_star (convert_star_rel M w)).(worlds)) :
    StarSemantic.eval (convert_rel_star (convert_star_rel M w)) f u = StarSemantic.eval M f
    (match u with
     | TrueWorld  => w
     | TrueWorld' => star M w
     end).
  Proof.
    revert u.
    revert w.
    induction f ; intros w u ; simpl.
    - destruct u.
      + reflexivity.
      + rewrite Bool.negb_involutive.
        reflexivity.
    - specialize (IHf w (true_star u)).
      destruct u.
      + simpl in IHf.
        simpl.
        rewrite IHf.
        reflexivity.
      + simpl in IHf.
        simpl.
        rewrite IHf.
        rewrite star_involutive.
        reflexivity.
    - specialize (IHf1 w u).
      specialize (IHf2 w u).
      rewrite <-IHf1.
      rewrite <-IHf2.
      reflexivity.
    - specialize (IHf1 w u).
      specialize (IHf2 w u).
      rewrite <-IHf1.
      rewrite <-IHf2.
      reflexivity.
  Qed.

  Theorem rel_star_consequence {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) :
    RelSemantic.consequence Γ A -> StarSemantic.consequence Γ A.
  Proof.
    intro H.
    unfold RelSemantic.consequence in H.
    unfold StarSemantic.consequence.
    intros M w H1.
    set (RelM := convert_star_rel M w).
    specialize (H RelM).
    apply holds_all_star_rel in H1.
    specialize (H H1).
    specialize (eval_rel_star_equiv A RelM true) as Heq.
    simpl in Heq.
    apply Heq in H.
    unfold RelM in H.
    specialize (eval_star_roundtrip M w A TrueWorld) as H2.
    simpl in H2.
    rewrite H2 in H.
    exact H.
  Qed.

  Theorem rel_star_equiv {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) : RelSemantic.consequence Γ A <-> StarSemantic.consequence Γ A.
  Proof.
    split.
    - apply rel_star_consequence.
    - apply star_rel_consequence.
  Qed.
End RelStarEquiv.

Import FDE_V4.
Import FourValuedSemantic.

Module V4StarEquiv.

  Definition convert_v4_rel {atom : Type} (M : @FourValuedSemantic.Model atom) : @RelSemantic.Model atom :=
    let ρ1 :=
          fun (a : atom) (val : bool) =>
            match val with
            | true => match (M.(v atom) a) with
                      | Zero => false
                      | None => false
                      | _ => true
                      end
            | false => match (M.(v atom) a) with
                      | Zero => true
                      | Both => true
                      | _ => false
                      end
            end
    in
      RelSemantic.Build_Model atom ρ1.

  Definition convert_rel_v4 {atom : Type} (M : @RelSemantic.Model atom) : @RelSemantic.Model atom :=
    let ρ1 :=
          fun (a : atom) (val : bool) =>
            match val with
            | true => match (M.(v atom) a) with
                      | Zero => false
                      | None => false
                      | _ => true
                      end
            | false => match (M.(v atom) a) with
                      | Zero => true
                      | Both => true
                      | _ => false
                      end
            end
    in
      RelSemantic.Build_Model atom ρ1.


  Lemma eval_v4_rel_equiv {atom : Type} (f : @formula atom) (M : @FourValuedSemantic.Model atom) :
    FourValuedSemantic.eval M f = One ->
    RelSemantic.eval (convert_v4_rel M) f true = true /\
    RelSemantic.eval (convert_v4_rel M) f false = false.
  Proof.


Lemma eval_invariant_v4_rel_One {atom : Type} (f : @formula atom) (M : @FourValuedSemantic.Model atom) :
    FourValuedSemantic.eval M f = One -> RelSemantic.eval (convert_v4_rel M) f true = true /\ RelSemantic.eval (convert_v4_rel M) f false = false
  with eval_invariant_v4_rel_None {atom : Type} (f : @formula atom) (M : @FourValuedSemantic.Model atom) :
    FourValuedSemantic.eval M f = None -> RelSemantic.eval (convert_v4_rel M) f true = false /\ RelSemantic.eval (convert_v4_rel M) f false = false
  with eval_invariant_v4_rel_Both {atom : Type} (f : @formula atom) (M : @FourValuedSemantic.Model atom) :
    FourValuedSemantic.eval M f = Both -> RelSemantic.eval (convert_v4_rel M) f true = true /\ RelSemantic.eval (convert_v4_rel M) f false = true
  with eval_invariant_v4_rel_Zero {atom : Type} (f : @formula atom) (M : @FourValuedSemantic.Model atom) :
    FourValuedSemantic.eval M f = Zero -> RelSemantic.eval (convert_v4_rel M) f true = false /\ RelSemantic.eval (convert_v4_rel M) f false = true.
  Proof.
    intro H.
    specialize (eval_invariant_v4_rel_One atom).
    specialize (eval_invariant_v4_rel_None atom).
    specialize (eval_invariant_v4_rel_Both atom).
    specialize (eval_invariant_v4_rel_Zero atom).
    - specialize (eval_invariant_v4_rel_One f M H).
      exact eval_invariant_v4_rel_One.
    - specialize (eval_invariant_v4_rel_One f M H).
      exact eval_invariant_v4_rel_One.

End V4StarEquiv.
