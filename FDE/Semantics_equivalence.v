From FDE Require Import Formula.
From FDE Require Import Semantics.
Import FormulaDef.
Import FDE_Formula.
Import RelSemantic.
Import StarSemantic.

Definition convert_star_rel {atom : Type} (M : @StarSemantic.Model atom) (w : M.(worlds)) : @RelSemantic.Model atom :=
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

Definition convert_rel_star {atom : Type} (M : @RelSemantic.Model atom) : @StarSemantic.Model atom :=
    let v :=
          fun (a : atom) (w : TrueWorlds) =>
            match w with
            | TrueWorld => RelSemantic.ρ M a true
            | TrueWorld' => negb (RelSemantic.ρ M a false)
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

Example Test5 : (RelSemantic.ρ (convert_star_rel (convert_rel_star M1) TrueWorld) P true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example Test6 : (RelSemantic.ρ (convert_star_rel (convert_rel_star M1) TrueWorld) P false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example Test7 : forall (A : atom3) (b : bool), ~(A = P) -> (RelSemantic.ρ (convert_star_rel (convert_rel_star M1) TrueWorld) A b) = false.
Proof.
  intros A b H.
  destruct A.
  - contradiction.
  - destruct b ; simpl ; reflexivity.
  - destruct b ; simpl ; reflexivity.
Qed.

Lemma ρ_eq {atom : Type} (M : @RelSemantic.Model atom) :
  let
    StarM := (convert_rel_star M)
  in
    forall (A : atom) (b : bool),
    RelSemantic.ρ M A b = RelSemantic.ρ (convert_star_rel StarM TrueWorld) A b.
Proof.
  intros StarM A b.
  simpl.
  rewrite Bool.negb_involutive.
  destruct b ; reflexivity.
Qed.

Lemma eval_eq {atom : Type} (M1 M2 : @RelSemantic.Model atom)
  (f : formula) (b : bool) (Hρ : forall A b, RelSemantic.ρ M1 A b =
                                       RelSemantic.ρ M2 A b) :
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
  Lemma eval_rel_star_equiv {atom : Type} (f : @formula atom) (M : @RelSemantic.Model atom) :
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

  Lemma holds_all_rel_star {atom : Type} (Γ : list (@formula atom)) (M : @RelSemantic.Model atom) :
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
                 RelSemantic.ρ (convert_star_rel (convert_rel_star M) TrueWorld) A b = RelSemantic.ρ M A b).
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

Import V4Semantic.
Module V4 := FDE_V4.
Import V4 (One, Zero, Both, None, neg_rel, neg_zero, neg_none, neg_both, neg_one, conj_rel, disj_rel, conj_zero_l, conj_zero_r, conj_none_both, conj_both_none, disj_one_l, disj_one_r, neg_rel_fun_equiv, conj_rel_fun_equiv, disj_rel_fun_equiv).

Module V4RelEquiv.

Definition convert_v4_rel {atom : Type} (M : @V4Semantic.Model atom) : @RelSemantic.Model atom :=
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

Definition convert_rel_v4 {atom : Type} (M : @RelSemantic.Model atom) : @V4Semantic.Model atom :=
  let ρ1 :=
    fun (a : atom) =>
      let v1 := (M.(ρ) a true) in
      let v2 := (M.(ρ) a false) in
      match v1, v2 with
      | true, true => Both
      | true, false => One
      | false, true => Zero
      | false, false => None
      end
  in
    V4Semantic.Build_Model atom ρ1.

Lemma eval_rel_v4_equiv {atom : Type} (f : @formula atom) (M : @RelSemantic.Model atom) :
  forall b1 b2 : bool,
  RelSemantic.eval M f true = b1 /\ RelSemantic.eval M f false = b2 ->
  V4Semantic.eval (convert_rel_v4 M) f =
    match b1, b2 with
    | true, true => Both
    | true, false => One
    | false, true => Zero
    | false, false => None
    end.
Proof.
  induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2] ; intros b1 b2 [H1 H2].
  - destruct b1, b2 ; simpl in H1 ; simpl in H2 ; simpl.
    + rewrite H1.
      rewrite H2.
      reflexivity.
    + rewrite H1.
      rewrite H2.
      reflexivity.
    + rewrite H1.
      rewrite H2.
      reflexivity.
    + rewrite H1.
      rewrite H2.
      reflexivity.
  - destruct b1, b2 ; simpl in H1 ; simpl in H2 ; simpl ; rewrite <-neg_rel_fun_equiv.
    + specialize (IH true true).
      specialize (IH (conj H2 H1)).
      simpl in IH.
      rewrite IH.
      apply neg_both.
    + specialize (IH false true).
      specialize (IH (conj H2 H1)).
      simpl in IH.
      rewrite IH.
      apply neg_zero.
    + specialize (IH true false).
      specialize (IH (conj H2 H1)).
      simpl in IH.
      rewrite IH.
      apply neg_one.
    + specialize (IH false false).
      specialize (IH (conj H2 H1)).
      simpl in IH.
      rewrite IH.
      apply neg_none.
  - destruct b1, b2 ; simpl in H1 ; simpl in H2 ; simpl ; rewrite <-conj_rel_fun_equiv.
    + rewrite Bool.andb_true_iff in H1.
      rewrite Bool.orb_true_iff in H2.
      destruct H1 as [H3 H4].
      destruct H2 as [H2 | H2].
      * specialize (IH1 true true).
        specialize (IH1 (conj H3 H2)).
        simpl in IH1.
        rewrite IH1.
        (* Now eval f2 is unknown, but f2 true = true, so eval f2 ∈ {One, Both} *)
        destruct (RelSemantic.eval M f2 false) eqn:Heq.
        ** (* f2 false = true → eval f2 = Both *)
          specialize (IH2 true true).
          specialize (IH2 (conj H4 eq_refl)).
          simpl in IH2.
          rewrite IH2.
          constructor.
        ** (* f2 false = false → eval f2 = One *)
          specialize (IH2 true false).
          specialize (IH2 (conj H4 eq_refl)).
          simpl in IH2.
          rewrite IH2.
          constructor.
      * specialize (IH2 true true).
        specialize (IH2 (conj H4 H2)).
        simpl in IH2.
        rewrite IH2.
        destruct (RelSemantic.eval M f1 false) eqn:Heq.
        ** specialize (IH1 true true).
           specialize (IH1 (conj H3 eq_refl)).
           simpl in IH1.
           rewrite IH1.
           constructor.
        ** specialize (IH1 true false).
           specialize (IH1 (conj H3 eq_refl)).
           simpl in IH1.
           rewrite IH1.
           constructor.
    + rewrite Bool.andb_true_iff in H1.
      rewrite Bool.orb_false_iff in H2.
      destruct H1 as [H3 H4].
      destruct H2 as [H1 H2].
      specialize (IH1 true false).
      specialize (IH1 (conj H3 H1)).
      specialize (IH2 true false).
      specialize (IH2 (conj H4 H2)).
      simpl in IH1, IH2.
      rewrite IH1, IH2.
      constructor.
    + rewrite Bool.andb_false_iff in H1.
      rewrite Bool.orb_true_iff in H2.
      destruct H1 as [H1 | H1], H2 as [H2 | H2].
      * specialize (IH1 false true).
        specialize (IH1 (conj H1 H2)).
        simpl in IH1.
        rewrite IH1.
        apply conj_zero_l.
      * specialize (IH1 false).
        destruct (RelSemantic.eval M f1 false) eqn:Heq1.
        ** specialize (IH1 true).
           specialize (IH1 (conj H1 eq_refl)).
           simpl in IH1.
           rewrite IH1.
           apply conj_zero_l.
        ** specialize (IH1 false).
           specialize (IH1 (conj H1 eq_refl)).
           simpl in IH1.
           rewrite IH1.
           destruct (RelSemantic.eval M f2 true) eqn:Heq2.
           *** specialize (IH2 true true).
               specialize (IH2 (conj eq_refl H2)).
               simpl in IH2.
               rewrite IH2.
               apply conj_none_both.
           *** specialize (IH2 false true).
               specialize (IH2 (conj eq_refl H2)).
               simpl in IH2.
               rewrite IH2.
               apply conj_zero_r.
      * specialize (IH2 false).
        destruct (RelSemantic.eval M f1 true) eqn:Heq1.
        ** specialize (IH1 true true).
           specialize (IH1 (conj eq_refl H2)).
           simpl in IH1.
           rewrite IH1.
           destruct (RelSemantic.eval M f2 false) eqn:Heq2.
           *** specialize (IH2 true).
               specialize (IH2 (conj H1 eq_refl)).
               simpl in IH2.
               rewrite IH2.
               apply conj_zero_r.
           *** specialize (IH2 false).
               specialize (IH2 (conj H1 eq_refl)).
               simpl in IH2.
               rewrite IH2.
               apply conj_both_none.
        ** specialize (IH1 false true).
           specialize (IH1 (conj eq_refl H2)).
           simpl in IH1.
           rewrite IH1.
           apply conj_zero_l.
      * specialize (IH2 false true).
        specialize (IH2 (conj H1 H2)).
        simpl in IH2.
        rewrite IH2.
        apply conj_zero_r.
  + rewrite Bool.andb_false_iff in H1.
    rewrite Bool.orb_false_iff in H2.
    destruct H1 as [H1 | H1], H2 as [H2 H3].
    * specialize (IH1 false false).
      specialize (IH1 (conj H1 H2)).
      simpl in IH1.
      rewrite IH1.
      destruct (RelSemantic.eval M f2 true) eqn:Heq.
      ** specialize (IH2 true false).
         specialize (IH2 (conj eq_refl H3)).
         simpl in IH2.
         rewrite IH2.
         constructor.
      ** specialize (IH2 false false).
         specialize (IH2 (conj eq_refl H3)).
         simpl in IH2.
         rewrite IH2.
         constructor.
    * specialize (IH2 false false).
      specialize (IH2 (conj H1 H3)).
      simpl in IH2.
      rewrite IH2.
      destruct (RelSemantic.eval M f1 true) eqn:Heq.
      ** specialize (IH1 true false).
         specialize (IH1 (conj eq_refl H2)).
         simpl in IH1.
         rewrite IH1.
         constructor.
      ** specialize (IH1 false false).
         specialize (IH1 (conj eq_refl H2)).
         simpl in IH1.
         rewrite IH1.
         constructor.
- destruct b1, b2 ; simpl in H1 ; simpl in H2 ; simpl; rewrite <-disj_rel_fun_equiv.
    + rewrite Bool.orb_true_iff in H1.
      rewrite Bool.andb_true_iff in H2.
      destruct H2 as [H2 H3].
      destruct H1 as [H1 | H1].
      * specialize (IH1 true true).
        specialize (IH1 (conj H1 H2)).
        simpl in IH1.
        rewrite IH1.
        destruct (RelSemantic.eval M f2 true) eqn:Heq.
        ** specialize (IH2 true true).
           specialize (IH2 (conj eq_refl H3)).
           simpl in IH2.
           rewrite IH2.
           constructor.
        ** specialize (IH2 false true).
           specialize (IH2 (conj eq_refl H3)).
           simpl in IH2.
           rewrite IH2.
           constructor.
      * specialize (IH2 true true).
        specialize (IH2 (conj H1 H3)).
        simpl in IH2.
        rewrite IH2.
        destruct (RelSemantic.eval M f1 true) eqn:Heq.
        ** specialize (IH1 true true).
           specialize (IH1 (conj eq_refl H2)).
           simpl in IH1.
           rewrite IH1.
           constructor.
        ** specialize (IH1 false true).
           specialize (IH1 (conj eq_refl H2)).
           simpl in IH1.
           rewrite IH1.
           constructor.
  + rewrite Bool.orb_true_iff in H1.
    rewrite Bool.andb_false_iff in H2.
    destruct H1 as [H1 | H1], H2 as [H2 | H2].
    * specialize (IH1 true false).
      specialize (IH1 (conj H1 H2)).
      simpl in IH1.
      rewrite IH1.
      apply disj_one_l.
    * specialize (IH1 true).
      destruct (RelSemantic.eval M f1 false) eqn:Heq1.
      ** specialize (IH1 true).
         specialize (IH1 (conj H1 eq_refl)).
         simpl in IH1.
         rewrite IH1.
         destruct (RelSemantic.eval M f2 true) eqn:Heq2.
         *** specialize (IH2 true false).
             specialize (IH2 (conj eq_refl H2)).
             simpl in IH2.
             rewrite IH2.
             constructor.
         *** specialize (IH2 false false).
             specialize (IH2 (conj eq_refl H2)).
             simpl in IH2.
             rewrite IH2.
             constructor.
      ** specialize (IH1 false).
         specialize (IH1 (conj H1 eq_refl)).
         simpl in IH1.
         rewrite IH1.
         apply disj_one_l.
    * specialize (IH2 true).
      destruct (RelSemantic.eval M f1 true) eqn:Heq1.
      ** specialize (IH1 true false).
         specialize (IH1 (conj eq_refl H2)).
         simpl in IH1.
         rewrite IH1.
         destruct (RelSemantic.eval M f2 false) eqn:Heq2.
         *** specialize (IH2 true).
             specialize (IH2 (conj H1 eq_refl)).
             simpl in IH2.
             rewrite IH2.
             constructor.
         *** specialize (IH2 false).
             specialize (IH2 (conj H1 eq_refl)).
             simpl in IH2.
             rewrite IH2.
             constructor.
      ** specialize (IH1 false false).
         specialize (IH1 (conj eq_refl H2)).
         simpl in IH1.
         rewrite IH1.
         destruct (RelSemantic.eval M f2 false) eqn:Heq2.
         *** specialize (IH2 true).
             specialize (IH2 (conj H1 eq_refl)).
             simpl in IH2.
             rewrite IH2.
             constructor.
         *** specialize (IH2 false).
             specialize (IH2 (conj H1 eq_refl)).
             simpl in IH2.
             rewrite IH2.
             constructor.
    * specialize (IH2 true false).
      specialize (IH2 (conj H1 H2)).
      simpl in IH2.
      rewrite IH2.
      apply disj_one_r.
  + rewrite Bool.orb_false_iff in H1.
    rewrite Bool.andb_true_iff in H2.
    destruct H2 as [H3 H4], H1 as [H1 H2].
    specialize (IH1 false true).
    specialize (IH1 (conj H1 H3)).
    simpl in IH1.
    rewrite IH1.
    specialize (IH2 false true).
    specialize (IH2 (conj H2 H4)).
    simpl in IH2.
    rewrite IH2.
    constructor.
  + rewrite Bool.orb_false_iff in H1.
    rewrite Bool.andb_false_iff in H2.
    destruct H1 as [H1 H3], H2 as [H2 | H2].
    * specialize (IH1 false false).
      specialize (IH1 (conj H1 H2)).
      simpl in IH1.
      rewrite IH1.
      destruct (RelSemantic.eval M f2 false) eqn:Heq.
      ** specialize (IH2 false true).
         specialize (IH2 (conj H3 eq_refl)).
         simpl in IH2.
         rewrite IH2.
         constructor.
      ** specialize (IH2 false false).
         specialize (IH2 (conj H3 eq_refl)).
         simpl in IH2.
         rewrite IH2.
         constructor.
    * specialize (IH2 false false).
      specialize (IH2 (conj H3 H2)).
      simpl in IH2.
      rewrite IH2.
      destruct (RelSemantic.eval M f1 false) eqn:Heq.
      ** specialize (IH1 false true).
         specialize (IH1 (conj H1 eq_refl)).
         simpl in IH1.
         rewrite IH1.
         constructor.
      ** specialize (IH1 false false).
         specialize (IH1 (conj H1 eq_refl)).
         simpl in IH1.
         rewrite IH1.
         constructor.
Qed.

Lemma eval_v4_rel_equiv {atom : Type} (f : @formula atom) (M : @V4Semantic.Model atom) :
  forall b1 b2 : bool,
  V4Semantic.eval M f =
    match b1, b2 with
    | true, true => Both
    | true, false => One
    | false, true => Zero
    | false, false => None
    end
  -> RelSemantic.eval (convert_v4_rel M) f true = b1 /\ RelSemantic.eval (convert_v4_rel M) f false = b2.
Proof.
  induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2] ; intros b1 b2 H.
  - destruct b1, b2 ; simpl in H ; simpl.
    + rewrite H.
      auto.
    + rewrite H.
      auto.
    + rewrite H.
      auto.
    + rewrite H.
      auto.
  - simpl in H.
    rewrite <-neg_rel_fun_equiv in H.
    simpl.
    destruct b1, b2.
    + inversion H ; subst.
      specialize (IH true true).
      simpl in IH.
      symmetry in H1.
      specialize (IH H1).
      rewrite and_comm.
      exact IH.
    + inversion H ; subst.
      specialize (IH false true).
      simpl in IH.
      symmetry in H1.
      specialize (IH H1).
      rewrite and_comm.
      exact IH.
    + inversion H ; subst.
      specialize (IH true false).
      simpl in IH.
      symmetry in H1.
      specialize (IH H1).
      rewrite and_comm.
      exact IH.
    + inversion H ; subst.
      specialize (IH false false).
      simpl in IH.
      symmetry in H1.
      specialize (IH H1).
      rewrite and_comm.
      exact IH.
  - simpl in H.
    rewrite <-conj_rel_fun_equiv in H.
    simpl.
    destruct b1, b2.
    + rewrite Bool.andb_true_iff.
      rewrite Bool.orb_true_iff.
      inversion H ; subst.
      * specialize (IH1 true true).
        simpl in IH1.
        symmetry in H1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 true true).
        simpl in IH2.
        symmetry in H2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** exact (conj H3 H5).
        ** apply (or_introl H4).
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 true true).
        specialize (IH2 true false).
        simpl in IH1.
        simpl in IH2.
        specialize (IH1 H1).
        specialize (IH2 H2).
        destruct IH1 as [H3 H4].
        destruct IH2 as [H5 H6].
        split.
        ** exact (conj H3 H5).
        ** apply (or_introl H4).
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 true false).
        specialize (IH2 true true).
        simpl in IH1.
        simpl in IH2.
        specialize (IH1 H1).
        specialize (IH2 H2).
        destruct IH1 as [H3 H4].
        destruct IH2 as [H5 H6].
        split.
        ** exact (conj H3 H5).
        ** apply (or_intror H6).
    + rewrite Bool.andb_true_iff.
      rewrite Bool.orb_false_iff.
      inversion H ; subst.
      symmetry in H1.
      symmetry in H2.
      specialize (IH1 true false).
      simpl in IH1.
      specialize (IH1 H1).
      destruct IH1 as [H3 H4].
      specialize (IH2 true false).
      simpl in IH2.
      specialize (IH2 H2).
      destruct IH2 as [H5 H6].
      split.
      * exact (conj H3 H5).
      * exact (conj H4 H6).
    + rewrite Bool.andb_false_iff.
      rewrite Bool.orb_true_iff.
      inversion H ; subst.
      * symmetry in H1.
        specialize (IH1 false true).
        specialize (IH1 H1).
        destruct IH1 as [H2 H3].
        split.
        ** left.
           exact H2.
        ** left.
           exact H3.
      * symmetry in H2.
        specialize (IH2 false true).
        specialize (IH2 H2).
        destruct IH2 as [H1 H3].
        split.
        ** right.
           exact H1.
        ** right.
           exact H3.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 true true).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** left.
           exact H3.
        ** right.
           exact H6.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 true true).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** right.
           exact H5.
        ** left.
           exact H4.
    + rewrite Bool.andb_false_iff.
      rewrite Bool.orb_false_iff.
      inversion H ; subst.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** left.
           exact H3.
        ** exact (conj H4 H6).
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 true false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** left.
           exact H3.
        ** exact (conj H4 H6).
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 true false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** right.
           exact H5.
        ** exact (conj H4 H6).
  - simpl in H.
    rewrite <-disj_rel_fun_equiv in H.
    simpl.
    destruct b1, b2.
    + rewrite Bool.orb_true_iff.
      rewrite Bool.andb_true_iff.
      inversion H ; subst.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 true true).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false true).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** left.
           exact H3.
        ** exact (conj H4 H6).
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 true true).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 true true).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** left.
           exact H3.
        ** exact (conj H4 H6).
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false true).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 true true).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** right.
           exact H5.
        ** exact (conj H4 H6).
    + rewrite Bool.orb_true_iff.
      rewrite Bool.andb_false_iff.
      inversion H ; subst.
      * symmetry in H1.
        specialize (IH1 true false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        split.
        ** left.
           exact H3.
        ** left.
           exact H4.
      * symmetry in H2.
        specialize (IH2 true false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H3 H4].
        split.
        ** right.
           exact H3.
        ** right.
           exact H4.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 true true).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** right.
           exact H5.
        ** left.
           exact H4.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 true true).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** left.
           exact H3.
        ** right.
           exact H6.
    + rewrite Bool.orb_false_iff.
      rewrite Bool.andb_true_iff.
      inversion H ; subst.
      symmetry in H1.
      symmetry in H2.
      specialize (IH1 false true).
      simpl in IH1.
      specialize (IH1 H1).
      destruct IH1 as [H3 H4].
      specialize (IH2 false true).
      simpl in IH2.
      specialize (IH2 H2).
      destruct IH2 as [H5 H6].
      split.
      * exact (conj H3 H5).
      * exact (conj H4 H6).
    + rewrite Bool.orb_false_iff.
      rewrite Bool.andb_false_iff.
      inversion H ; subst.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false true).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** exact (conj H3 H5).
        ** left.
           exact H4.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false false).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** exact (conj H3 H5).
        ** left.
           exact H4.
      * symmetry in H1.
        symmetry in H2.
        specialize (IH1 false true).
        simpl in IH1.
        specialize (IH1 H1).
        destruct IH1 as [H3 H4].
        specialize (IH2 false false).
        simpl in IH2.
        specialize (IH2 H2).
        destruct IH2 as [H5 H6].
        split.
        ** exact (conj H3 H5).
        ** right.
           exact H6.
Qed.

Lemma holds_all_rel_v4 {atom : Type} (Γ : list (@formula atom)) (M : @RelSemantic.Model atom) :
  RelSemantic.holds_all M Γ -> V4Semantic.holds_all (convert_rel_v4 M) Γ.
Proof.
  intro H.
  unfold V4Semantic.holds_all.
  intros f H1.
  unfold RelSemantic.holds_all in H.
  specialize (H f H1).
  unfold FDE_V4.designated.
  destruct (RelSemantic.eval M f false) eqn:Heq.
  - specialize (eval_rel_v4_equiv f M true true) as H2.
    simpl in H2.
    specialize (H2 (conj H Heq)).
    right.
    exact H2.
  - specialize (eval_rel_v4_equiv f M true false) as H2.
    simpl in H2.
    specialize (H2 (conj H Heq)).
    left.
    exact H2.
Qed.

Lemma holds_all_v4_rel {atom : Type} (Γ : list (@formula atom)) (M : @V4Semantic.Model atom) :
  V4Semantic.holds_all M Γ -> RelSemantic.holds_all (convert_v4_rel M) Γ.
Proof.
  intro H.
  unfold RelSemantic.holds_all.
  intros f H1.
  unfold V4Semantic.holds_all in H.
  specialize (H f H1).
  unfold FDE_V4.designated in H.
  destruct H as [H | H].
  - specialize (eval_v4_rel_equiv f M true false) as H2.
    simpl in H2.
    specialize (H2 H).
    destruct H2 as [H2 _].
    exact H2.
  - specialize (eval_v4_rel_equiv f M true true) as H2.
    simpl in H2.
    specialize (H2 H).
    destruct H2 as [H2 _].
    exact H2.
Qed.

Theorem v4_eval_convert_roundtrip {atom : Type} (M : @V4Semantic.Model atom):
  forall f : @formula atom, V4Semantic.eval (convert_rel_v4 (convert_v4_rel M)) f = V4Semantic.eval M f.
Proof.
  intro f.
  induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2].
  - simpl.
    destruct (v M a) eqn:Heq ; reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
  - simpl.
    rewrite IH1.
    rewrite IH2.
    reflexivity.
  - simpl.
    rewrite IH1.
    rewrite IH2.
    reflexivity.
Qed.

Theorem rel_eval_convert_roundtrip {atom : Type} (M : @RelSemantic.Model atom) (f : @formula atom):
  forall b : bool, RelSemantic.eval (convert_v4_rel (convert_rel_v4 M)) f b = RelSemantic.eval M f b.
Proof.
  induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2] ; intro b.
  - cbn [RelSemantic.eval].
    destruct b ; simpl.
    + destruct (ρ M a true) eqn:Heq1, (ρ M a false) eqn:Heq2 ; reflexivity.
    + destruct (ρ M a true) eqn:Heq1, (ρ M a false) eqn:Heq2 ; reflexivity.
  - simpl.
    specialize (IH (negb b)).
    exact IH.
  - cbn [RelSemantic.eval].
    specialize (IH1 b).
    specialize (IH2 b).
    destruct b.
    + rewrite IH1.
      rewrite IH2.
      reflexivity.
    + rewrite IH1.
      rewrite IH2.
      reflexivity.
  - cbn [RelSemantic.eval].
    specialize (IH1 b).
    specialize (IH2 b).
    destruct b.
    + rewrite IH1.
      rewrite IH2.
      reflexivity.
    + rewrite IH1.
      rewrite IH2.
      reflexivity.
Qed.

Theorem rel_v4_consequence {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) :
  RelSemantic.consequence Γ A -> V4Semantic.consequence Γ A.
Proof.
  intro H.
  unfold RelSemantic.consequence in H.
  unfold V4Semantic.consequence.
  intros M H1.
  apply holds_all_v4_rel in H1.
  specialize (H (convert_v4_rel M)).
  specialize (H H1).
  clear H1.
  unfold FDE_V4.designated.
  destruct (RelSemantic.eval (convert_v4_rel M) A false) eqn:Heq.
  - specialize (eval_rel_v4_equiv A (convert_v4_rel M) true true) as H1.
    simpl in H1.
    specialize (H1 (conj H Heq)).
    right.
    rewrite v4_eval_convert_roundtrip in H1.
    exact H1.
  - specialize (eval_rel_v4_equiv A (convert_v4_rel M) true false) as H1.
    simpl in H1.
    specialize (H1 (conj H Heq)).
    left.
    rewrite v4_eval_convert_roundtrip in H1.
    exact H1.
Qed.

Theorem v4_rel_consequence {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) :
  V4Semantic.consequence Γ A -> RelSemantic.consequence Γ A.
Proof.
  intro H.
  unfold V4Semantic.consequence in H.
  unfold RelSemantic.consequence.
  intros M H1.
  apply holds_all_rel_v4 in H1.
  specialize (H (convert_rel_v4 M)).
  specialize (H H1).
  clear H1.
  unfold FDE_V4.designated in H.
  destruct H.
  - specialize (eval_v4_rel_equiv A (convert_rel_v4 M) true false) as H1.
    simpl in H1.
    specialize (H1 H).
    destruct H1 as [H1 _].
    rewrite rel_eval_convert_roundtrip in H1.
    exact H1.
  - specialize (eval_v4_rel_equiv A (convert_rel_v4 M) true true) as H1.
    simpl in H1.
    specialize (H1 H).
    destruct H1 as [H1 _].
    rewrite rel_eval_convert_roundtrip in H1.
    exact H1.
Qed.

Theorem rel_v4_equiv {atom : Type} (A: @formula atom) (Γ : list (@formula atom)) : RelSemantic.consequence Γ A <-> V4Semantic.consequence Γ A.
Proof.
  split.
  - apply rel_v4_consequence.
  - apply v4_rel_consequence.
Qed.
End V4RelEquiv.
