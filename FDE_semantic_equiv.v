From Mendelson Require Import FDE_formula.
From Mendelson Require Import FDE_semantics.
Import FDE_FormulaDef.
Import FDE_Formula.
Import RelSemantic.
Import StarSemantic.

Module RelStarEquiv.
  Lemma eval_invariant_rel_star {atom : Type} (f : @formula atom) (M : RelSemantic.Model atom) :
    (RelSemantic.eval M f true = true) -> StarSemantic.eval (convert2 M) f TrueWorld = true
  with eval_invariant_rel_star_false {atom : Type} (f : @formula atom) (M : RelSemantic.Model atom) :
    (RelSemantic.eval M f false = true) -> StarSemantic.eval (convert2 M) f TrueWorld' = false.
  Proof.
  - intro H.
    specialize (eval_invariant_rel_star atom).
    specialize (eval_invariant_rel_star_false atom).
    induction f.
    + simpl.
      simpl in H.
      exact H.
    + simpl.
      rewrite Bool.negb_true_iff.
      simpl in H.
      specialize (eval_invariant_rel_star_false f0 M).
      specialize (eval_invariant_rel_star_false H).
      exact eval_invariant_rel_star_false.
    + simpl.
      rewrite Bool.andb_true_iff.
      simpl in H.
      rewrite Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      specialize (IHf1 H1).
      specialize (IHf2 H2).
      exact (conj IHf1 IHf2).
    + simpl.
      rewrite Bool.orb_true_iff.
      simpl in H.
      rewrite Bool.orb_true_iff in H.
      destruct H as [H | H].
      * specialize (IHf1 H).
        left.
        exact IHf1.
      * specialize (IHf2 H).
        right.
        exact IHf2.
  - intro H.
    specialize (eval_invariant_rel_star atom).
    specialize (eval_invariant_rel_star_false atom).
    induction f.
    + simpl.
      rewrite Bool.negb_false_iff.
      simpl in H.
      exact H.
    + simpl.
      rewrite Bool.negb_false_iff.
      simpl in H.
      specialize (eval_invariant_rel_star f0 M).
      specialize (eval_invariant_rel_star H).
      exact eval_invariant_rel_star.
    + simpl.
      rewrite Bool.andb_false_iff.
      simpl in H.
      rewrite Bool.orb_true_iff in H.
      destruct H as [H | H].
      * specialize (IHf1 H).
        left.
        exact IHf1.
      * specialize (IHf2 H).
        right.
        exact IHf2.
    + simpl.
      rewrite Bool.orb_false_iff.
      simpl in H.
      rewrite Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      specialize (IHf1 H1).
      specialize (IHf2 H2).
      exact (conj IHf1 IHf2).
  Qed.

  Lemma eval_invariant_star_rel {atom : Type} (f : @formula atom) (M : @StarSemantic.Model atom) (w : M.(worlds)):
    StarSemantic.eval M f w = true -> RelSemantic.eval (convert1 M w) f true = true
  with eval_invariant_star_rel_false {atom : Type} (f : @formula atom) (M : @StarSemantic.Model atom) (w : M.(worlds)):
    StarSemantic.eval M f (M.(star) w) = false -> RelSemantic.eval (convert1 M w) f false = true.
  Proof.
  - intro H.
    specialize (eval_invariant_star_rel atom).
    specialize (eval_invariant_star_rel_false atom).
    induction f.
    + simpl.
      simpl in H.
      exact H.
    + simpl.
      simpl in H.
      rewrite Bool.negb_true_iff in H.
      specialize (eval_invariant_star_rel_false f0 M w).
      specialize (eval_invariant_star_rel_false H).
      exact eval_invariant_star_rel_false.
    + simpl.
      rewrite Bool.andb_true_iff.
      simpl in H.
      rewrite Bool.andb_true_iff in H.
      destruct H as [H1 H2].
      specialize (IHf1 H1).
      specialize (IHf2 H2).
      exact (conj IHf1 IHf2).
    + simpl.
      rewrite Bool.orb_true_iff.
      simpl in H.
      rewrite Bool.orb_true_iff in H.
      destruct H as [H | H].
      * specialize (IHf1 H).
        left.
        exact IHf1.
      * specialize (IHf2 H).
        right.
        exact IHf2.
  - intro H.
    specialize (eval_invariant_star_rel atom).
    specialize (eval_invariant_star_rel_false atom).
    induction f.
    + simpl.
      rewrite Bool.negb_true_iff.
      simpl in H.
      exact H.
    + simpl.
      simpl in H.
      rewrite star_involutive in H.
      rewrite Bool.negb_false_iff in H.
      specialize (eval_invariant_star_rel f0 M w).
      specialize (eval_invariant_star_rel H).
      exact eval_invariant_star_rel.
    + simpl.
      rewrite Bool.orb_true_iff.
      simpl in H.
      rewrite Bool.andb_false_iff in H.
      destruct H as [H | H].
      * specialize (IHf1 H).
        left.
        exact IHf1.
      * specialize (IHf2 H).
        right.
        exact IHf2.
    + simpl.
      rewrite Bool.andb_true_iff.
      simpl in H.
      rewrite Bool.orb_false_iff in H.
      destruct H as [H1 H2].
      specialize (IHf1 H1).
      specialize (IHf2 H2).
      exact (conj IHf1 IHf2).
  Qed.

  Lemma holds_all_rel_star {atom : Type} (Γ : list (@formula atom)) (M : RelSemantic.Model atom) :
    RelSemantic.holds_all M Γ -> StarSemantic.holds_all (convert2 M) Γ TrueWorld.
  Proof.
    intro H.
    unfold StarSemantic.holds_all.
    intros f H1.
    unfold RelSemantic.holds_all in H.
    specialize (H f H1).
    apply (eval_invariant_rel_star f M) in H.
    exact H.
  Qed.

  Lemma holds_all_star_rel {atom : Type} (Γ : list (@formula atom))
    (M : @StarSemantic.Model atom) (w : M.(worlds)) : StarSemantic.holds_all M Γ w -> RelSemantic.holds_all (convert1 M w) Γ.
  Proof.
    intro H.
    unfold RelSemantic.holds_all.
    intros f H1.
    unfold StarSemantic.holds_all in H.
    specialize (H f H1).
    apply (eval_invariant_star_rel f M w) in H.
    exact H.
  Qed.

  Theorem convert_star_rel {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) :
    StarSemantic.consequence Γ A -> RelSemantic.consequence Γ A.
  Proof.
    intro H.
    unfold StarSemantic.consequence in H.
    unfold RelSemantic.consequence.
    intros M H1.

    set (StarM := convert2 M).
    specialize (H StarM).
    specialize (H TrueWorld).
    apply holds_all_rel_star in H1.
    specialize (H H1).
    clear H1.
    induction A.
    - apply eval_invariant_star_rel in H.
      unfold StarM in H.
      simpl in H.
      simpl.
      exact H.
    - simpl.
      simpl in H.
      rewrite Bool.negb_true_iff in H.
      apply (eval_invariant_star_rel_false A StarM TrueWorld) in H.
      unfold StarM in H.
      specialize (eval_eq (convert1 (convert2 M) TrueWorld) M A false) as H1.
      assert (H2 : forall (A : atom) (b : bool),
                 RelSemantic.ρ atom (convert1 (convert2 M) TrueWorld) A b = RelSemantic.ρ atom M A b).
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
  (w : M.(worlds)) (f : formula) (u : (convert2 (convert1 M w)).(worlds)) :
    StarSemantic.eval (convert2 (convert1 M w)) f u = StarSemantic.eval M f 
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

  Theorem convert_rel_star {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) :
    RelSemantic.consequence Γ A -> StarSemantic.consequence Γ A.
  Proof.
    intro H.
    unfold RelSemantic.consequence in H.
    unfold StarSemantic.consequence.
    intros M w H1.
    set (RelM := convert1 M w).
    specialize (H RelM).
    apply holds_all_star_rel in H1.
    specialize (H H1).
    apply eval_invariant_rel_star in H.
    unfold RelM in H.
    specialize (eval_star_roundtrip M w A TrueWorld) as H2.
    simpl in H2.
    rewrite H2 in H.
    exact H.
  Qed.

  Theorem rel_star_equiv {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) : RelSemantic.consequence Γ A <-> StarSemantic.consequence Γ A.
  Proof.
    split.
    - apply convert_rel_star.
    - apply convert_star_rel.
  Qed.
End RelStarEquiv.
