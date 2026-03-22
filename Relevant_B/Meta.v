From Basis Require Export MSets.
From Relevant_B Require Import Formula.
From Relevant_B Require Import Syntactic.
From Relevant_B Require Import Semantic.
From Coq Require Import Classical_Prop.
From Coq Require Import Lists.List.
Import ListNotations.

Import FormulaDef.
Import Relevant_B_Formula.
Import Semantic.
Import Syntactic.
Import Functions.

Local Open Scope formula_scope.
Module Meta.
  Lemma identity_valid {atom : Type} (A : @formula atom) : valid (@Model atom) (f_identity A).
  Proof.
    unfold f_identity.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR HA.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    rewrite HR in HA.
    exact HA.
  Qed.

  Lemma disj_intro_left_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (f_disj_intro_left A B).
  Proof.
    unfold f_disj_intro_left.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR HA.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    rewrite HR in HA.
    left.
    exact HA.
  Qed.

  Lemma disj_intro_right_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (f_disj_intro_right A B).
  Proof.
    unfold f_disj_intro_right.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR HB.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    rewrite HR in HB.
    right.
    exact HB.
  Qed.

  Lemma conj_elim_left_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (f_conj_elim_left A B).
  Proof.
    unfold f_conj_elim_left.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR HAB.
    destruct HAB as [HA _].
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    clear Heq.
    rewrite HR in HA.
    exact HA.
  Qed.

  Lemma conj_elim_right_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (f_conj_elim_right A B).
  Proof.
    unfold f_conj_elim_right.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR HAB.
    destruct HAB as [_ HB].
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    clear Heq.
    rewrite HR in HB.
    exact HB.
  Qed.

  Lemma conj_distrib_valid {atom : Type} (A B C : @formula atom) : valid (@Model atom) (f_conj_distrib A B C).
  Proof.
    unfold f_conj_distrib.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR Hconj.
    destruct Hconj as [HA HB_or_C].
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    clear Heq.
    rewrite HR in HA, HB_or_C.
    destruct HB_or_C as [HB | HC].
    - left.
      exact (conj HA HB).
    - right.
      exact (conj HA HC).
  Qed.

  Lemma impl_conj_right_valid {atom : Type} (A B C : @formula atom) : valid (@Model atom) (f_impl_conj_right A B C).
  Proof.
    unfold f_impl_conj_right.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y Rxy Hconj.
    intros u v Ruv Au.
    destruct Hconj as [HAB HAC].
    specialize (HAB u v).
    specialize (HAC u v).
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in Rxy.
    clear Heq.
    rewrite Rxy in HAB, HAC.
    specialize (HAB Ruv Au).
    specialize (HAC Ruv Au).
    exact (conj HAB HAC).
  Qed.

  Lemma case_analysis_valid {atom : Type} (A B C : @formula atom) : valid (@Model atom) (f_case_analysis A B C).
  Proof.
    unfold f_case_analysis.
    unfold valid.
    intros M w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y HRxy H.
    intros u v HRuv HA_or_B.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HRxy.
    clear Heq.
    rename HRxy into Heq.
    destruct H as [HAC HBC].
    specialize (HAC u v).
    rewrite Heq in HAC.
    specialize (HAC HRuv).
    specialize (HBC u v).
    rewrite Heq in HBC.
    clear Heq.
    specialize (HBC HRuv).
    destruct HA_or_B as [HA | HB].
    - specialize (HAC HA).
      exact HAC.
    - specialize (HBC HB).
      exact HBC.
  Qed.

  Lemma neg_elim_valid {atom : Type} (A : @formula atom) : valid (@Model atom) (f_neg_elim A).
  Proof.
    unfold f_neg_elim.
    unfold valid.
    intros M w Hnormal.
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR Hneg.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    clear Heq.
    rename HR into Heq.
    rewrite star_involutive in Hneg.
    apply NNPP in Hneg.
    rewrite Heq in Hneg.
    exact Hneg.
  Qed.

  Lemma mp_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B : @formula atom, consequence (@Model atom) Γ $A -> B$ -> consequence (@Model atom) Γ A -> consequence (@Model atom) Γ B.
  Proof.
    intros A B HAB HA.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HA.
    specialize (HA M w Hnormal Hall).
    unfold consequence in HAB.
    specialize (HAB M w Hnormal Hall).
    simpl in HAB.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    specialize (Rnormal M w w w Hnormal) as Heq.
    specialize (eq_refl w) as Hw.
    rewrite <-Heq in Hw.
    clear Heq.
    rename Hw into HR.
    specialize (HAB w w).
    specialize (HAB HR HA).
    simpl.
    exact HAB.
  Qed.

  Lemma conj_intro_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B : @formula atom, consequence (@Model atom) Γ A -> consequence (@Model atom) Γ B -> consequence (@Model atom) Γ $A /\ B$.
  Proof.
    intros A B HA HB.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HA.
    specialize (HA M w Hnormal Hall).
    unfold consequence in HB.
    specialize (HB M w Hnormal Hall).
    simpl.
    exact (conj HA HB).
  Qed.

  Lemma trans_prefix_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B C, consequence (@Model atom) Γ $A -> B$ -> consequence (@Model atom) Γ $(C -> A) -> (C -> B)$.
  Proof.
    intros A B C HAB.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HAB.
    specialize (HAB M w Hnormal Hall).
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HRxy HCA.
    intros u v HRuv HC.
    simpl in HAB.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HRxy.
    clear Heq.
    rename HRxy into Heq.
    specialize (HCA u v).
    rewrite Heq in HCA.
    specialize (HCA HRuv).
    specialize (HCA HC).
    clear HC Heq.

    specialize (Rnormal M w v v Hnormal) as Heq.
    specialize (eq_refl v) as Hv.
    rewrite <-Heq in Hv.
    clear Heq.
    specialize (HAB v v).
    specialize (HAB Hv HCA).
    exact HAB.
  Qed.

  Lemma trans_suffix_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B C, consequence (@Model atom) Γ $A -> B$ -> consequence (@Model atom) Γ $(B -> C) -> (A -> C)$.
  Proof.
    intros A B C HAB.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HAB.
    specialize (HAB M w Hnormal Hall).
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HRxy HBC.
    intros u v HRuv HA.
    simpl in HAB.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HRxy.
    clear Heq.
    rename HRxy into Heq.
    specialize (HBC u v).
    rewrite Heq in HBC.
    specialize (HBC HRuv).
    apply HBC.
    specialize (HAB u u).
    clear Heq.
    specialize (Rnormal M w u u Hnormal) as Heq.
    specialize (eq_refl u) as Hu.
    rewrite <-Heq in Hu.
    clear Heq.
    specialize (HAB Hu HA).
    exact HAB.
  Qed.

  Lemma contrapos_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B, consequence (@Model atom) Γ $A -> ~B$ -> consequence (@Model atom) Γ $B -> ~A$.
  Proof.
    intros A B HAnB.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HAnB.
    specialize (HAnB M w Hnormal Hall).
    simpl.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    intros x y HR HB.
    unfold not.
    intro HA.
    specialize (Rnormal M w x y Hnormal) as Heq.
    rewrite Heq in HR.
    clear Heq.
    rename HR into Heq.
    simpl in HAnB.
    rewrite <-Heq in HA.
    clear Heq.
    specialize (HAnB (star M x) (star M x)).
    specialize (Rnormal M w (star M x) (star M x) Hnormal) as Heq.
    specialize (eq_refl (star M x)) as Hstar.
    rewrite <-Heq in Hstar.
    clear Heq.
    specialize (HAnB Hstar HA).
    unfold not in HAnB.
    apply HAnB.
    rewrite star_involutive.
    exact HB.
  Qed.

  Theorem soundness {atom : Type} : forall (A B : @formula atom), Syntactic.entails (fun x => x = A) B  -> Semantic.consequence (@Model atom) [A] B.
  Proof.
    intros A B.
    intro H.
    induction H.
    - rewrite γ.
      unfold consequence.
      intros M w Hnormal Hall.
      apply holds_all_single in Hall.
      exact Hall.
    - specialize (identity_valid A0) as Hvalid.
      specialize (valid_forall_consequence (f_identity A0) Hvalid [A]) as H.
      exact H.
    - specialize (disj_intro_left_valid A0 B) as Hvalid.
      specialize (valid_forall_consequence (f_disj_intro_left A0 B) Hvalid [A]) as H.
      exact H.
    - specialize (disj_intro_right_valid A0 B) as Hvalid.
      specialize (valid_forall_consequence (f_disj_intro_right A0 B) Hvalid [A]) as H.
      exact H.
    - specialize (conj_elim_left_valid A0 B) as Hvalid.
      specialize (valid_forall_consequence (f_conj_elim_left A0 B) Hvalid [A]) as H.
      exact H.
    - specialize (conj_elim_right_valid A0 B) as Hvalid.
      specialize (valid_forall_consequence (f_conj_elim_right A0 B) Hvalid [A]) as H.
      exact H.
    - specialize (conj_distrib_valid A0 B C) as Hvalid.
      specialize (valid_forall_consequence (f_conj_distrib A0 B C) Hvalid [A]) as H.
      exact H.
    - specialize (case_analysis_valid A0 B C) as Hvalid.
      specialize (valid_forall_consequence (f_case_analysis A0 B C) Hvalid [A]) as H.
      exact H.
    - specialize (impl_conj_right_valid A0 B C) as Hvalid.
      specialize (valid_forall_consequence (f_impl_conj_right A0 B C) Hvalid [A]) as H.
      exact H.
    - specialize (neg_elim_valid A0) as Hvalid.
      specialize (valid_forall_consequence (f_neg_elim A0) Hvalid [A]) as H.
      exact H.
    - specialize (mp_valid [A] A0 B IHentails1 IHentails2) as Hvalid.
      exact Hvalid.
    - specialize (conj_intro_valid [A] A0 B IHentails1 IHentails2) as Hvalid.
      exact Hvalid.
    - specialize (trans_prefix_valid [A] A0 B C IHentails) as Hvalid.
      exact Hvalid.
    - specialize (trans_suffix_valid [A] A0 B C IHentails) as Hvalid.
      exact Hvalid.
    - specialize (contrapos_valid [A] A0 B IHentails) as Hvalid.
      exact Hvalid.
  Qed.

  Lemma A8_valid (atom : Type) (A B : @formula atom): valid (@Model_T8 atom) $(A -> ~B) -> B -> ~A$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y HRxy HAB.
    intros u v HRuv HB.
    unfold not.
    intro HAstar.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in HRxy.
    clear Heq.
    rename HRxy into Heq.
    rewrite <-Heq in HRuv.
    specialize (HAB (star m v) (star m u)).
    rewrite (star_involutive m) in HAB.
    specialize (T8 m x u v) as HT8.
    specialize (HT8 HRuv).
    specialize (HAB HT8).
    specialize (HAB HAstar).
    unfold not in HAB.
    apply HAB.
    exact HB.
  Qed.

  Lemma A9_valid (atom : Type) (A B C : @formula atom): valid (@Model_T9 atom) $(A -> B) -> ((B -> C) -> (A -> C))$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y HRxy.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in HRxy.
    clear Heq.
    rename HRxy into Heq.
    intro HAB.
    intros u v HRuv HBC.
    intros j k HRjk HA.
    specialize (T9 m y u v j k) as HT9.
    specialize (HT9 HRuv HRjk).
    destruct HT9 as [i [HRji HRik]].
    specialize (HBC i k).
    specialize (HBC HRik).
    apply HBC.
    specialize (HAB j i).
    rewrite Heq in HAB.
    specialize (HAB HRji).
    apply HAB.
    exact HA.
  Qed.

  Lemma A10_valid (atom : Type) (A B C : @formula atom): valid (@Model_T10 atom) $(A -> B) -> ((C ->A) -> (C -> B))$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y HRxy.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in HRxy.
    clear Heq.
    rename HRxy into Heq.
    intro HAB.
    intros u v HRuv HCA.
    intros j k HRjk HC.
    specialize (T10 m y u v j k) as HT10.
    specialize (HT10 HRuv HRjk).
    destruct HT10 as [i [HRji HRik]].
    specialize (HCA j i).
    specialize (HCA HRji).
    specialize (HCA HC).
    rename HCA into HA.
    specialize (HAB i k).
    rewrite Heq in HAB.
    specialize (HAB HRik).
    specialize (HAB HA).
    exact HAB.
  Qed.

  Lemma A11_valid (atom : Type) (A B C : @formula atom): valid (@Model_T11 atom) $(A -> (A -> B)) -> (A -> B)$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y HRxy.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in HRxy.
    clear Heq.
    rename HRxy into Heq.
    intro HAAB.
    intros u v HRuv HA.
    specialize (T11 m y u v) as HT11.
    specialize (HT11 HRuv).
    destruct HT11 as [j [HRuj HRjuv]].
    specialize (HAAB u j).
    rewrite Heq in HAAB.
    specialize (HAAB HRuj).
    specialize (HAAB HA).
    specialize (HAAB u v).
    specialize (HAAB HRjuv).
    specialize (HAAB HA).
    exact HAAB.
  Qed.

  Lemma A12_valid {atom : Type} (A B : @formula atom): valid (@Model_T12 atom) $A -> ((A -> B) -> B)$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y Rxy.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in Rxy.
    clear Heq.
    rename Rxy into Heq.
    intro HA.
    intros u v Ruv HAB.
    rewrite Heq in HA.
    specialize (T12 m y u v) as HT12.
    specialize (HT12 Ruv).
    destruct HT12 as [j [Hincl Rjv]].
    specialize (HAB j v).
    specialize (HAB Rjv).
    apply HAB.
    clear HAB.
    specialize (inclusion_eval m A y j Hincl HA) as HAj.
    exact HAj.
  Qed.

  Lemma A13_valid {atom : Type} (A : @formula atom): valid (@Model_T13 atom) $A \/ ~A$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    specialize (T13 m w Hnormal) as HT13.
    specialize (inclusion_eval m A (star m w) w HT13) as Heval.
    specialize (classic (eval m A (star m w))) as Hstar.
    destruct Hstar as [True | False].
    - apply Heval in True.
      left.
      exact True.
    - right.
      exact False.
  Qed.

  Lemma A14_valid {atom : Type} (A : @formula atom): valid (@Model_T14 atom) $(A -> ~A) -> ~A$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y Rxy.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in Rxy.
    clear Heq.
    rename Rxy into Heq.
    intro HA_starA.
    unfold not.
    intro HA_star.
    unfold not in HA_starA.
    specialize (T14 m y) as HT14.
    destruct (is_normal m y) eqn:Hy.
    - specialize (Rnormal m y y y Hy) as HRy.
      specialize (eq_refl y) as Heq1.
      apply HRy in Heq1.
      clear HRy.
      rename Heq1 into Ry.
      specialize (HA_starA y y).
      rewrite Heq in HA_starA.
      specialize (HA_starA Ry).
      specialize (inclusion_eval m A (star m y) y HT14 HA_star) as HAy.
      specialize (HA_starA HAy).
      specialize (HA_starA HA_star).
      exact HA_starA.
    - specialize (HA_starA (star m y) y).
      rewrite Heq in HA_starA.
      specialize (HA_starA HT14 HA_star HA_star).
      exact HA_starA.
  Qed.

  Lemma A15_valid {atom : Type} (A B : @formula atom): valid (@Model_T15 atom) $A -> (B -> A)$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y Rxy.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in Rxy.
    clear Heq.
    rename Rxy into Heq.
    intro HA.
    intros u v Ruv Hbu.
    specialize (T15 m y u v) as HT15.
    specialize (HT15 Ruv).
    rewrite Heq in HA.
    specialize (inclusion_eval m A y v HT15 HA) as HAv.
    exact HAv.
  Qed.

  Lemma A16_valid {atom : Type} (A : @formula atom): valid (@Model_T16 atom) $A -> (A -> A)$.
  Proof.
    unfold valid.
    intros m w Hnormal.
    unfold to_model in Hnormal.
    simpl in Hnormal.
    simpl.
    intros x y Rxy HAx.
    specialize (Rnormal m w x y Hnormal) as Heq.
    rewrite Heq in Rxy.
    clear Heq.
    rename Rxy into Heq.
    intros u v Ruv HAu.
    rewrite Heq in HAx.
    clear Heq.
    rename HAx into HAy.
    specialize (T16 m y u v) as HT16.
    specialize (HT16 Ruv).
    destruct HT16 as [Hyv | Huv].
    - specialize (inclusion_eval m A y v Hyv HAy) as HAv.
      exact HAv.
    - specialize (inclusion_eval m A u v Huv HAu) as HAv.
      exact HAv.
  Qed.

End Meta.