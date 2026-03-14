From Basis Require Import FSignature.
From Relevant_B Require Import Formula.
From Relevant_B Require Import Syntactic.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Classical_Prop.
Import Syntactic.
Import ListNotations.
Import FormulaDef.
Import Relevant_B_Formula.
Local Open Scope formula_scope.

Module Semantic.
  Record Model {atom : Type} :=
  {
    worlds : Type;
    w0 : worlds;
    is_normal : worlds -> bool;
    R : worlds -> worlds -> worlds -> Prop;
    Rnormal : forall w x y : worlds, is_normal w = true -> (R w x y <-> x = y);
    star : worlds -> worlds;
    star_involutive : forall w : worlds, star (star w) = w;
    v : atom -> worlds -> Prop;
  }.

  Fixpoint eval {atom : Type} (M: @Model atom) (f : formula) (w : worlds M) : Prop :=
    match f with
    | f_atom A => M.(v) A w
    | f_not f' => ~ (eval M f' (M.(star) w))
    | f_conj f g => (eval M f w) /\ (eval M g w)
    | f_disj f g => (eval M f w) \/ (eval M g w)
    | f_imp f g =>  forall x y : M.(worlds), (M.(R) w x y) -> (eval M f x) -> (eval M g y)
    end.

  Class IsModel (atom : Type) (M : Type) := {
    to_model : M -> @Model atom
  }.

  Instance Model_IsModel (atom : Type) : IsModel atom (@Model atom) :=
  {
    to_model := fun m => m
  }.

  Definition valid {atom : Type} (MType : Type) `{IsModel atom MType} (f : @formula atom) : Prop :=
    forall (m : MType) (w : worlds (to_model m)),
      is_normal (to_model m) w = true -> eval (to_model m) f w.

  Declare Scope relevant_B_scope.

  #[global] Notation "M |= φ" := (valid M φ) (at level 90) : relevant_B_scope.

  Definition holds_all {atom : Type} (M : @Model atom) (Γ : list formula) (w : M.(worlds)) : Prop := forall f : @formula atom, In f Γ -> eval M f w.

  Lemma holds_all_single {atom : Type} (M : @Model atom) (w : M.(worlds)) : forall A : @formula atom, holds_all M [A] w -> eval M A w.
  Proof.
    intros A Hall.
    unfold holds_all in Hall.
    specialize (Hall A).
    specialize (in_eq A nil) as HA.
    specialize (Hall HA).
    exact Hall.
  Qed.

  Definition consequence {atom : Type} (MType : Type) `{IsModel atom MType} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (m : MType) (w : worlds (to_model m)),
      (is_normal (to_model m) w) = true -> holds_all (to_model m) Γ w -> eval (to_model m) f w.

(*  #[global] Notation "M , Γ |= f" := (consequence M Γ f) (at level 90) : relevant_B_scope.
  Open Scope relevant_B_scope.
*)

  Lemma valid_forall_consequence {atom : Type} (A : @formula atom) :
    valid (@Model atom) A -> forall Γ : list (@formula atom), consequence (@Model atom) Γ A.
  Proof.
    intro Hvalid.
    intro Γ.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold valid in Hvalid.
    specialize (Hvalid M w Hnormal).
    exact Hvalid.
  Qed.

  Lemma identity_valid {atom : Type} (A : @formula atom) : valid (@Model atom) (Syntactic.f_identity A).
  Proof.
    unfold Syntactic.f_identity.
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

  Lemma disj_intro_left_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (Syntactic.f_disj_intro_left A B).
  Proof.
    unfold Syntactic.f_disj_intro_left.
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

  Lemma disj_intro_right_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (Syntactic.f_disj_intro_right A B).
  Proof.
    unfold Syntactic.f_disj_intro_right.
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

  Lemma conj_elim_left_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (Syntactic.f_conj_elim_left A B).
  Proof.
    unfold Syntactic.f_conj_elim_left.
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

  Lemma conj_elim_right_valid {atom : Type} (A B : @formula atom) : valid (@Model atom) (Syntactic.f_conj_elim_right A B).
  Proof.
    unfold Syntactic.f_conj_elim_right.
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

  Lemma conj_distrib_valid {atom : Type} (A B C : @formula atom) : valid (@Model atom) (Syntactic.f_conj_distrib A B C).
  Proof.
    unfold Syntactic.f_conj_distrib.
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

  Lemma case_analysis_valid {atom : Type} (A B C : @formula atom) : valid (@Model atom) (Syntactic.f_case_analysis A B C).
  Proof.
    unfold Syntactic.f_case_analysis.
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

  Lemma neg_elim_valid {atom : Type} (A : @formula atom) : valid (@Model atom) (Syntactic.f_neg_elim A).
  Proof.
    unfold Syntactic.f_neg_elim.
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

  Theorem soundness {atom : Type} : forall (A B : @formula atom), (fun x => x = A) |- B -> consequence (@Model atom) [A] B.
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

  Variant atom3 : Type := P | Q | S.
  Definition f (a: atom3) : @formula atom3 :=
    f_atom a.
  Coercion f: atom3 >-> formula.

  Definition id {T : Type} (w: T) : T := w.
  Lemma IdInvolutive {T : Type} : forall w : T, id (id w) = w.
  Proof.
    intro w.
    unfold id.
    reflexivity.
  Qed.

  Module Worlds4.

    Variant worlds4 : Type := Γ | Δ | Ε | Ω.

    Definition is_normal1 (w: worlds4) : bool :=
    match w with  
    | Γ => true
    | _ => false
    end.

    Definition R1 (w1 w2 w3: worlds4) : Prop :=
      (w1 = Γ /\ w2 = w3) \/ (w1 = Δ /\ w2 = Ε /\ w3 = Ω).

    Lemma Rnormal1 : forall w x y : worlds4, is_normal1 w = true -> (R1 w x y <-> x = y).
    Proof.
      intros w x y Hnormal.
      split.
      - intro HR.
        unfold R1 in HR.
        destruct HR as [HΓ | HΔ].
        + destruct HΓ as [_ H].
          exact H.
        + destruct HΔ as [Hw _].
          rewrite Hw in Hnormal.
          simpl in Hnormal.
          discriminate Hnormal.
     - intro Heq.
       rewrite Heq.
       destruct w ; simpl in Hnormal ; try discriminate Hnormal.
       unfold R1.
       left.
       exact (conj eq_refl eq_refl).
    Qed.

    Lemma A1_neg : ~ forall (atom : Type) (A B : @formula atom), valid (@Model atom) $A -> (B -> A)$.
    Proof.
      unfold not.
      intro H.
      specialize (H atom3 P Q).

      pose (
        v1 :=
          fun (a : atom3) (w: worlds4) =>
            match a, w with
            | P, Δ => True
            | Q, Ε => True
            | _, _ => False
            end
      ).

      pose (M1 := {|
        worlds := worlds4;
        w0 := Γ;
        is_normal := is_normal1;
        R := R1;
        Rnormal := Rnormal1;
        star := id;
        star_involutive := IdInvolutive;
        v := v1;
      |}).

      unfold valid in H.
      specialize (H M1 M1.(w0)).
      unfold M1 in H.
      cbn [is_normal] in H.
      cbn [w0] in H.
      cbn [is_normal1] in H.
      specialize (H eq_refl).
      simpl in H.
      specialize (H Δ Δ).
      simpl in H.
      assert (HΓ : R1 Γ Δ Δ).
      {
        unfold R1.
        left.
        exact (conj eq_refl eq_refl).
      }
      specialize (H HΓ I).
      specialize (H Ε Ω).
      simpl in H.
      apply H.
      - unfold R1.
        right.
        exact (conj eq_refl (conj eq_refl eq_refl)).
      - exact I.
    Qed.

   Lemma T2_1_neg : ~ forall (atom : Type) (A B C : @formula atom), consequence (@Model atom) [$(A /\ B) -> C$] $A -> (B -> C)$.
   Proof.
    unfold not.
    intro H.
    specialize (H atom3 P Q S).

    pose (
      v1 :=
        fun (a : atom3) (w: worlds4) =>
          match a, w with
          | P, Δ => True
          | Q, Ε => True
          | S, Ε => True
          | _, _ => False
          end
    ).

    pose (M1 := {|
      worlds := worlds4;
      w0 := Γ;
      is_normal := is_normal1;
      R := R1;
      Rnormal := Rnormal1;
      star := id;
      star_involutive := IdInvolutive;
      v := v1;
    |}).

    unfold consequence in H.
    specialize (H M1 M1.(w0)).
    unfold M1 in H.
    cbn [is_normal] in H.
    cbn [w0] in H.
    cbn [is_normal1] in H.
    specialize (H eq_refl).
    assert (Hall : holds_all
        {|
          worlds := worlds4;
          w0 := Γ;
          is_normal := is_normal1;
          R := R1;
          Rnormal := Rnormal1;
          star := id;
          star_involutive := IdInvolutive;
          v := v1
        |} [$P /\ Q -> S$] Γ).
    {
      unfold holds_all.
      intros f Hin.
      unfold In in Hin.
      destruct Hin as [Hin | []].
      rewrite <-Hin.
      simpl.
      intros x y HRxy.
      unfold R1 in HRxy.
      destruct HRxy as [Heq | Heq].
      - destruct Heq as [_ Heq].
        rewrite <-Heq.
        destruct x.
        + intro H1.
          destruct H1 as [H1 _].
          exact H1.
        + intro H1.
          destruct H1 as [_ H1].
          exact H1.
        + intro H1.
          destruct H1 as [_ H1].
          exact H1.
        + intro H1.
          destruct H1 as [H1 _].
          exact H1.
      - destruct Heq as [Heq _].
        discriminate Heq.
    }

    specialize (H Hall).
    simpl in H.
    specialize (H Δ Δ).
    simpl in H.
    assert (HΓ : R1 Γ Δ Δ).
    {
      unfold R1.
      left.
      exact (conj eq_refl eq_refl).
    }

    specialize (H HΓ I).
    specialize (H Ε Ω).
    simpl in H.
    apply H.
    - unfold R1.
      right.
      exact (conj eq_refl (conj eq_refl eq_refl)).
    - exact I.
  Qed.

  Lemma T2_3_neg : ~ forall (atom : Type) (A B C : @formula atom), valid (@Model atom) $((A -> B) /\ (B -> C)) -> (A -> C)$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 P Q S).

    pose (
      v1 :=
        fun (a : atom3) (w: worlds4) =>
          match a, w with
          | P, Ε => True
          | Q, Ω => True
          | _, _ => False
          end
    ).

    pose (M1 := {|
      worlds := worlds4;
      w0 := Γ;
      is_normal := is_normal1;
      R := R1;
      Rnormal := Rnormal1;
      star := id;
      star_involutive := IdInvolutive;
      v := v1;
    |}).

    unfold valid in H.
    specialize (H M1 M1.(w0)).
    unfold M1 in H.
    cbn [is_normal] in H.
    cbn [w0] in H.
    cbn [is_normal1] in H.
    specialize (H eq_refl).
    simpl in H.
    specialize (H Δ Δ).
    assert (HΓ : R1 Γ Δ Δ).
    {
      unfold R1.
      left.
      exact (conj eq_refl eq_refl).
    }

    specialize (H HΓ).
    clear HΓ.

    assert (Hante : (forall x y : worlds4,
       R1 Δ x y ->
       match x with
       | Ε => True
       | _ => False
       end ->
       match y with
       | Ω => True
       | _ => False
       end) /\
      (forall x y : worlds4,
       R1 Δ x y ->
       match x with
       | Ω => True
       | _ => False
       end -> False)).
    {
      split.
      - intros x y HR.
        destruct x, y ; unfold R1 in HR ; intro H1 ; try destruct H1 ; try apply I.
        + destruct HR as [HR | HR].
          * destruct HR as [HR _].
            discriminate HR.
          * destruct HR as [_ [_ HR]].
            discriminate HR.
        + destruct HR as [HR | HR].
          * destruct HR as [HR _].
            discriminate HR.
          * destruct HR as [_ [_ HR]].
            discriminate HR.
        + destruct HR as [HR | HR].
          * destruct HR as [HR _].
            discriminate HR.
          * destruct HR as [_ [_ HR]].
            discriminate HR.
      - intros x y HR.
        destruct x, y ; unfold R1 in HR ; intro H1 ; try destruct H1 ; try apply I.
        + destruct HR as [HR | HR].
          * destruct HR as [HR _].
            discriminate HR.
          * destruct HR as [_ [_ HR]].
            discriminate HR.
        + destruct HR as [HR | HR].
          * destruct HR as [HR _].
            discriminate HR.
          * destruct HR as [_ [_ HR]].
            discriminate HR.
        + destruct HR as [HR | HR].
          * destruct HR as [HR _].
            discriminate HR.
          * destruct HR as [_ [_ HR]].
            discriminate HR.
        + destruct HR as [HR | HR].
          * destruct HR as [HR _].
            discriminate HR.
          * destruct HR as [_ [HR _]].
            discriminate HR.
    }

    specialize (H Hante).
    clear Hante.
    specialize (H Ε Ω).
    simpl in H.
    apply H.
    - unfold R1.
      right.
      exact (conj eq_refl (conj eq_refl eq_refl)).
    - exact I.
  Qed.

  Lemma T2_4_neg : ~ forall (atom : Type) (A B C : @formula atom), valid (@Model atom) $(A -> B) -> ((A /\ C)-> (B /\ C))$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 P Q S).

    pose (
      v1 :=
        fun (a : atom3) (w: worlds4) =>
          match a, w with
          | P, Ε => True
          | S, Ε => True
          | Q, Ω => True
          | _, _ => False
          end
    ).

    pose (M1 := {|
      worlds := worlds4;
      w0 := Γ;
      is_normal := is_normal1;
      R := R1;
      Rnormal := Rnormal1;
      star := id;
      star_involutive := IdInvolutive;
      v := v1;
    |}).

    unfold valid in H.
    specialize (H M1 M1.(w0)).
    unfold M1 in H.
    cbn [is_normal] in H.
    cbn [w0] in H.
    cbn [is_normal1] in H.
    specialize (H eq_refl).
    simpl in H.
    specialize (H Δ Δ).
    assert (HΓ : R1 Γ Δ Δ).
    {
      unfold R1.
      left.
      exact (conj eq_refl eq_refl).
    }

    specialize (H HΓ).
    clear HΓ.

    assert (Hante : (forall x y : worlds4,
       R1 Δ x y ->
       match x with
       | Ε => True
       | _ => False
       end ->
       match y with
       | Ω => True
       | _ => False
       end)).
    {
      intros x y HR.
      destruct x, y ; unfold R1 in HR ; intro H1 ; try destruct H1 ; try apply I.
      + destruct HR as [HR | HR].
        * destruct HR as [HR _].
          discriminate HR.
        * destruct HR as [_ [_ HR]].
          discriminate HR.
      + destruct HR as [HR | HR].
        * destruct HR as [HR _].
          discriminate HR.
        * destruct HR as [_ [_ HR]].
          discriminate HR.
      + destruct HR as [HR | HR].
        * destruct HR as [HR _].
          discriminate HR.
        * destruct HR as [_ [_ HR]].
          discriminate HR.
    }

    specialize (H Hante).
    clear Hante.
    specialize (H Ε Ω).
    simpl in H.
    assert (HR1 : R1 Δ Ε Ω).
    {
      unfold R1.
      right.
      exact (conj eq_refl (conj eq_refl eq_refl)).
    }

    specialize (H HR1).
    specialize (H (conj I I)).
    destruct H as [_ H].
    exact H.
  Qed.

  Lemma T2_5_neg : ~ forall (atom : Type) (A B C : @formula atom), consequence (@Model atom) [$(A /\ B) -> C$] $(A /\ ~C) -> ~B$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 P Q S).

    pose (
        R1 :=
          fun (w1 w2 w3: worlds4) => (w1 = Γ /\ w2 = w3)
      ).

    assert(Rnormal1 : forall w x y : worlds4, is_normal1 w = true -> (R1 w x y <-> x = y)).
    {
      intros w x y Hnormal.
      split.
      - intro HR.
        unfold R1 in HR.
        destruct HR as [_ Heq].
        exact Heq.
     - intro Heq.
       rewrite Heq.
       destruct w ; simpl in Hnormal ; try discriminate Hnormal.
       unfold R1.
       exact (conj eq_refl eq_refl).
    }

    pose (
        star1 :=
          fun (w: worlds4) => 
          match w with
          | Γ => Γ
          | Δ => Ε
          | Ε => Δ
          | Ω => Ω
          end
      ).

    assert (Hinvolutive : forall w : worlds4, star1 (star1 w) = w).
    {
      intro w.
      destruct w ; unfold star1 ; reflexivity.
    }

    pose (
      v1 :=
        fun (a : atom3) (w: worlds4) =>
          match a, w with
          | P, Δ => True
          | Q, Ε => True
          | _, _ => False
          end
    ).

    pose (M1 := {|
      worlds := worlds4;
      w0 := Γ;
      is_normal := is_normal1;
      R := R1;
      Rnormal := Rnormal1;
      star := star1;
      star_involutive := Hinvolutive;
      v := v1;
    |}).

    unfold consequence in H.
    specialize (H M1 M1.(w0)).
    unfold M1 in H.
    cbn [is_normal] in H.
    cbn [w0] in H.
    cbn [is_normal1] in H.
    specialize (H eq_refl).

    assert (Hall : holds_all
        {|
          worlds := worlds4;
          w0 := Γ;
          is_normal := is_normal1;
          R := R1;
          Rnormal := Rnormal1;
          star := star1;
          star_involutive := Hinvolutive;
          v := v1
        |} [$P /\ Q -> S$] Γ).
    {
      unfold holds_all.
      intros f Hin.
      unfold In in Hin.
      destruct Hin as [Hin | []].
      rewrite <-Hin.
      simpl.
      intros x y HR.
      destruct x ; intro H1.
      - destruct H1 as [H1 _].
        exact H1.
      - destruct H1 as [_ H1].
        exact H1.
      - destruct H1 as [H1 _].
        exact H1.
      - destruct H1 as [H1 _].
        exact H1.
    }

    specialize (H Hall).
    clear Hall.
    simpl in H.
    specialize (H Δ Δ).
    assert (HΓ : R1 Γ Δ Δ).
    {
      unfold R1.
      exact (conj eq_refl eq_refl).
    }

    specialize (H HΓ).
    clear HΓ.
    simpl in H.
    unfold not in H.
    apply H.
    split.
    - exact I.
    - intro H1.
      exact H1.
    - exact I.
  Qed.

   Lemma A11_neg : ~ forall (atom : Type) (A B : @formula atom), valid (@Model atom) $(A -> (A -> B)) -> (A -> B)$.
   Proof.
    unfold not.
    intro H.
    specialize (H atom3 P Q).

    pose (
      v1 :=
        fun (a : atom3) (w: worlds4) =>
          match a, w with
          | P, Ε => True
          | _, _ => False
          end
    ).

    pose (M1 := {|
      worlds := worlds4;
      w0 := Γ;
      is_normal := is_normal1;
      R := R1;
      Rnormal := Rnormal1;
      star := id;
      star_involutive := IdInvolutive;
      v := v1;
    |}).

    unfold valid in H.
    specialize (H M1 M1.(w0)).
    unfold M1 in H.
    cbn [is_normal] in H.
    cbn [w0] in H.
    cbn [is_normal1] in H.
    specialize (H eq_refl).
    simpl in H.
    specialize (H Δ Δ).
    assert (HΓ : R1 Γ Δ Δ).
    {
      unfold R1.
      left.
      exact (conj eq_refl eq_refl).
    }

    specialize (H HΓ).
    clear HΓ.

    assert (Hante : (forall x y : worlds4,
     R1 Δ x y ->
     match x with
     | Ε => True
     | _ => False
     end ->
     forall x0 y0 : worlds4,
     R1 y x0 y0 ->
     match x0 with
     | Ε => True
     | _ => False
     end -> False)).
    {
      intros x y HR Hx.
      destruct x ; try destruct Hx.
      unfold R1 in HR.
      destruct HR as [HR | HR].
      - destruct HR as [HR _].
        discriminate HR.
      - destruct HR as [_ [_ Hy]].
        intros u v HRuv.
        rewrite Hy in HRuv.
        unfold R1 in HRuv.
        destruct HRuv as [HRuv | HRuv].
        + destruct HRuv as [HRuv _].
          discriminate HRuv.
        + destruct HRuv as [HRuv _].
          discriminate HRuv.
      }

      specialize (H Hante).
      clear Hante.
      specialize (H Ε Ω).
      simpl in H. 
      assert (HΔ : R1 Δ Ε Ω).
      {
        unfold R1.
        right.
        exact (conj eq_refl (conj  eq_refl eq_refl)).
      }

      apply H.
      - exact HΔ.
      - exact I.
  Qed.
  End Worlds4.

  Module Worlds2.
    Variant worlds2 : Type := Γ | Δ.
    Definition is_normal1 (w: worlds2) : bool :=
    match w with  
    | Γ => true
    | _ => false
    end.

    Definition R1 (w1 w2 w3: worlds2) : Prop :=
      (w1 = Γ /\ w2 = w3).

    Lemma Rnormal1 : forall w x y : worlds2, is_normal1 w = true -> (R1 w x y <-> x = y).
    Proof.
      intros w x y Hnormal.
      destruct w ; simpl in Hnormal ; try discriminate Hnormal.
      split.
      - intro HR.
        unfold R1 in HR.
        destruct HR as [_ Heq].
        exact Heq.
      - intro Heq.
        rewrite Heq.
        unfold R1.
        exact (conj eq_refl eq_refl).
    Qed.

    Lemma T3_neg : ~ forall (atom : Type) (A B : @formula atom), valid (@Model atom) $(A /\ (A -> B)) -> B$.
     Proof.
      unfold not.
      intro H.
      specialize (H atom3 P Q).
      pose (
        v1 :=
          fun (a : atom3) (w: worlds2) =>
            match a, w with
            | P, Δ => True
            | _, _ => False
            end
      ).

      pose (M1 := {|
        worlds := worlds2;
        w0 := Γ;
        is_normal := is_normal1;
        R := R1;
        Rnormal := Rnormal1;
        star := id;
        star_involutive := IdInvolutive;
        v := v1;
      |}).

      unfold valid in H.
      specialize (H M1 M1.(w0)).
      unfold M1 in H.
      cbn [is_normal] in H.
      cbn [w0] in H.
      cbn [is_normal1] in H.
      specialize (H eq_refl).
      simpl in H.
      specialize (H Δ Δ).
      assert (HΓ : R1 Γ Δ Δ).
      {
        unfold R1.
        exact (conj eq_refl eq_refl).
      }

      specialize (H HΓ).
      clear HΓ.

      apply H.
      split.
      - exact I.
      - intros x y HR.
        destruct x, y ; unfold R1 in HR ; intro H1 ; try destruct H1 ; try apply I.
        + destruct HR as [HR _].
          discriminate HR.
        + destruct HR as [HR _].
          discriminate HR.
    Qed.

    Record Model_R3w {atom : Type} :=
    {
      base_model :> @Model atom;
      R3w : forall w : base_model.(worlds), (base_model.(R) w w w);
    }.

    Instance Model_R3w_IsModel (atom : Type) : IsModel atom (@Model_R3w atom) :=
    {
      to_model := base_model
    }.

    Lemma T3_pos (atom : Type) (A B : @formula atom): valid (@Model_R3w atom) $(A /\ (A -> B)) -> B$.
    Proof.
      unfold valid.
      intros M w Hnormal.
      simpl.
      unfold to_model in Hnormal.
      simpl in Hnormal.
      intros x y HRxy Hconj.
      destruct Hconj as [HA HAB].
      specialize (Rnormal M w x y Hnormal) as Heq.
      rewrite Heq in HRxy.
      clear Heq.
      rename HRxy into Heq.
      specialize (HAB y y).
      rewrite Heq in HAB.
      specialize (R3w M y) as Hy.
      rewrite Heq in HA.
      specialize (HAB Hy HA). 
      exact HAB.
    Qed.
  End Worlds2.

  Record Model_T8 {atom : Type} :=
  {
    base_model_T8 :> @Model atom;
    T8 : forall x y z : base_model_T8.(worlds), base_model_T8.(R) x y z -> base_model_T8.(R) x (base_model_T8.(star) z) (base_model_T8.(star) y);
  }.

  Record Model_T9 {atom : Type} :=
  {
    base_model_T9 :> @Model atom;
    T9 : forall x y z u v : base_model_T9.(worlds), base_model_T9.(R) x y z -> base_model_T9.(R) z u v -> 
      exists j : base_model_T9.(worlds), base_model_T9.(R) x u j /\ base_model_T9.(R) y j v;
  }.

  Record Model_T10 {atom : Type} :=
  {
    base_model_T10 :> @Model atom;
    T10 : forall x y z u v : base_model_T10.(worlds), base_model_T10.(R) x y z -> base_model_T10.(R) z u v -> 
      exists j : base_model_T10.(worlds), base_model_T10.(R) y u j /\ base_model_T10.(R) x j v;
  }.

  Record Model_T11 {atom : Type} :=
  {
    base_model_T11 :> @Model atom;
    T11 : forall x y z : base_model_T11.(worlds), base_model_T11.(R) x y z -> 
      exists j : base_model_T11.(worlds), base_model_T11.(R) x y j /\ base_model_T11.(R) j y z;
  }.

  Instance Model_T8_IsModel (atom : Type) : IsModel atom (@Model_T8 atom) :=
  {
    to_model := base_model_T8
  }.

  Instance Model_T9_IsModel (atom : Type) : IsModel atom (@Model_T9 atom) :=
  {
    to_model := base_model_T9
  }.

  Instance Model_T10_IsModel (atom : Type) : IsModel atom (@Model_T10 atom) :=
  {
    to_model := base_model_T10
  }.

  Instance Model_T11_IsModel (atom : Type) : IsModel atom (@Model_T11 atom) :=
  {
    to_model := base_model_T11
  }.

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
End Semantic.
