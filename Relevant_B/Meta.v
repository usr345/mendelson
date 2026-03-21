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

End Meta.