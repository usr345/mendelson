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
    | f_imp f g =>  match (M.(is_normal) w) with
                    | true => forall w' : M.(worlds), (eval M f w') -> (eval M g w')
                    | false => forall x y : M.(worlds), (M.(R) w x y) -> (eval M f x) -> (eval M g y)
                    end
    end.

  Definition valid {atom : Type} (f : @formula atom) : Prop :=
    forall (M : Model) (w : M.(worlds)), (M.(is_normal) w) = true -> (eval M f w).

  Declare Scope relevant_B_scope.

  #[global] Notation "|= f" := (valid f) (at level 90) : relevant_B_scope.

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

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : @Model atom) (w : M.(worlds)),
      (M.(is_normal) w) = true -> holds_all M Γ w -> eval M f w.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : relevant_B_scope.
  Open Scope relevant_B_scope.

  Lemma valid_forall_consequence {atom : Type} (A : @formula atom) :
    |= A -> forall Γ : list (@formula atom), Γ |= A.
  Proof.
    intro Hvalid.
    intro Γ.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold valid in Hvalid.
    specialize (Hvalid M w Hnormal).
    exact Hvalid.
  Qed.

  Lemma identity_valid {atom : Type} (A : @formula atom) : |= (Syntactic.f_identity A).
  Proof.
    unfold Syntactic.f_identity.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w' H1.
    exact H1.
  Qed.

  Lemma disj_intro_left_valid {atom : Type} (A B : @formula atom) : |= (Syntactic.f_disj_intro_left A B).
  Proof.
    unfold Syntactic.f_disj_intro_left.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w' H1.
    left.
    exact H1.
  Qed.

  Lemma disj_intro_right_valid {atom : Type} (A B : @formula atom) : |= (Syntactic.f_disj_intro_right A B).
  Proof.
    unfold Syntactic.f_disj_intro_right.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w' H1.
    right.
    exact H1.
  Qed.

  Lemma conj_elim_left_valid {atom : Type} (A B : @formula atom) : |= (Syntactic.f_conj_elim_left A B).
  Proof.
    unfold Syntactic.f_conj_elim_left.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w' H1.
    destruct H1 as [H1 _].
    exact H1.
  Qed.

  Lemma conj_elim_right_valid {atom : Type} (A B : @formula atom) : |= (Syntactic.f_conj_elim_right A B).
  Proof.
    unfold Syntactic.f_conj_elim_right.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w' H1.
    destruct H1 as [_ H1].
    exact H1.
  Qed.

  Lemma conj_distrib_valid {atom : Type} (A B C : @formula atom) : |= (Syntactic.f_conj_distrib A B C).
  Proof.
    unfold Syntactic.f_conj_distrib.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w' H1.
    destruct H1 as [H1 H2].
    destruct H2 as [H2 | H2].
    - left.
      exact (conj H1 H2).
    - right.
      exact (conj H1 H2).
  Qed.

  Lemma case_analysis_valid {atom : Type} (A B C : @formula atom) : |= (Syntactic.f_case_analysis A B C).
  Proof.
    unfold Syntactic.f_case_analysis.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w1 H1.
    destruct H1 as [HAC HBC].
    destruct (is_normal M w1) eqn:Heq.
    - intros w2 H2.
      destruct H2 as [HA | HB].
      + specialize (HAC w2 HA).
        exact HAC.
      + specialize (HBC w2 HB).
        exact HBC.
    - intros x y HR H2.
      destruct H2 as [HA | HB].
      + specialize (HAC x y HR HA).
        exact HAC.
      + specialize (HBC x y HR HB).
        exact HBC.
  Qed.

  Lemma neg_elim_valid {atom : Type} (A : @formula atom) : |= (Syntactic.f_neg_elim A).
  Proof.
    unfold Syntactic.f_neg_elim.
    unfold valid.
    intros M w H.
    simpl.
    rewrite H.
    intros w1 H1.
    rewrite star_involutive in H1.
    apply NNPP in H1.
    exact H1.
  Qed.

  Lemma mp_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B : @formula atom, Γ |= $A -> B$ -> Γ |= A -> Γ |= B.
  Proof.
    intros A B HAB HA.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HA.
    specialize (HA M w Hnormal Hall).
    unfold consequence in HAB.
    specialize (HAB M w Hnormal Hall).
    simpl in HAB.
    rewrite Hnormal in HAB.
    specialize (HAB w HA).
    exact HAB.
  Qed.

  Lemma conj_intro_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B : @formula atom, Γ |= A -> Γ |= B -> Γ |= $A /\ B$.
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
    forall A B C, Γ |= $A -> B$ -> Γ |= $(C -> A) -> (C -> B)$.
  Proof.
    intros A B C HAB.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HAB.
    specialize (HAB M w Hnormal Hall).
    simpl.
    rewrite Hnormal.
    simpl in HAB.
    rewrite Hnormal in HAB.
    intros w1 HCA.
    destruct (is_normal M w1) eqn:Heq.
    - intros w2 HC.
      specialize (HCA w2 HC).
      rename HCA into HA.
      specialize (HAB w2 HA).
      exact HAB.
    - intros x y HR HC.
      specialize (HCA x y HR HC).
      rename HCA into HA.
      specialize (HAB y HA).
      exact HAB.
  Qed.

  Lemma trans_suffix_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B C, Γ |= $A -> B$ -> Γ |= $(B -> C) -> (A -> C)$.
  Proof.
    intros A B C HAB.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HAB.
    specialize (HAB M w Hnormal Hall).
    simpl.
    rewrite Hnormal.
    simpl in HAB.
    rewrite Hnormal in HAB.
    intros w1 HBC.
    destruct (is_normal M w1) eqn:Heq.
    - intros w2 HA.
      specialize (HBC w2).
      specialize (HAB w2 HA).
      rename HAB into HB.
      specialize (HBC HB).
      exact HBC.
    - intros x y HR HA.
      specialize (HBC x y HR).
      specialize (HAB x HA).
      rename HAB into HB.
      specialize (HBC HB).
      exact HBC.
  Qed.

  Lemma contrapos_valid {atom : Type} (Γ : list (@formula atom)) :
    forall A B, Γ |= $A -> ~B$ -> Γ |= $B -> ~A$.
  Proof.
    intros A B HAnB.
    unfold consequence.
    intros M w Hnormal Hall.
    unfold consequence in HAnB.
    specialize (HAnB M w Hnormal Hall).
    simpl.
    rewrite Hnormal.
    intros w' HB.
    unfold not.
    intro HA.
    simpl in HAnB.
    rewrite Hnormal in HAnB.
    specialize (HAnB (star M w')).
    specialize (HAnB HA).
    apply HAnB.
    rewrite star_involutive.
    exact HB.
  Qed.

  Theorem soundness {atom : Type} : forall (A B : @formula atom), (fun x => x = A) |- B -> [A] |= B.
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
  Variant worlds4 : Type := Γ | Δ | Ε | Ω.

  Definition is_normal1 (w: worlds4) : bool :=
  match w with  
  | Γ => true
  | _ => false
  end.

  Definition R1 (w1 w2 w3: worlds4) : Prop :=
    (w1 = Γ /\ w2 = w3) \/ (w1 = Δ /\ w2 = Ε /\ w3 = Ω).

  Definition star1 (w: worlds4) : worlds4 := w.
  Lemma Star1Involutive : forall w : worlds4, star1 (star1 w) = w.
  Proof.
    intro w.
    destruct w ; unfold star1 ; reflexivity.
  Qed.

  Lemma A1_neg : ~ forall (atom : Type) (A B : @formula atom), |= $A -> (B -> A)$.
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
      star := star1;
      star_involutive := Star1Involutive;
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
    specialize (H Δ).
    simpl in H.
    specialize (H I).
    specialize (H Ε Ω).
    simpl in H.
    apply H.
    - unfold R1.
      right.
      exact (conj eq_refl (conj eq_refl eq_refl)).
    - exact I.
  Qed.

 Lemma T2_1_neg : ~ forall (atom : Type) (A B C : @formula atom), [$(A /\ B) -> C$] |= $A -> (B -> C)$.
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
    star := star1;
    star_involutive := Star1Involutive;
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
        star := star1;
        star_involutive := Star1Involutive;
        v := v1
      |} [$P /\ Q -> S$] Γ).
  {
    unfold holds_all.
    intros f Hin.
    unfold In in Hin.
    destruct Hin as [Hin | []].
    rewrite <-Hin.
    simpl.
    intro w.
    destruct w ; intro H1.
    - destruct H1 as [H1 _].
      exact H1.
    - destruct H1 as [_ H1].
      exact H1.
    - destruct H1 as [_ H1].
      exact H1.
    - destruct H1 as [H1 _].
      exact H1.
  }

  specialize (H Hall).
  simpl in H.
  specialize (H Δ).
  simpl in H.
  specialize (H I).
  specialize (H Ε Ω).
  simpl in H.
  apply H.
  - unfold R1.
    right.
    exact (conj eq_refl (conj eq_refl eq_refl)).
  - exact I.
Qed.

Lemma T2_3_neg : ~ forall (atom : Type) (A B C : @formula atom), |= $((A -> B) /\ (B -> C)) -> (A -> C)$.
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
    star := star1;
    star_involutive := Star1Involutive;
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
  specialize (H Δ).
  cbn [is_normal1] in H.

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

 Lemma T2_4_neg : ~ forall (atom : Type) (A B C : @formula atom), |= $(A -> B) -> ((A /\ C)-> (B /\ C))$.
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
    star := star1;
    star_involutive := Star1Involutive;
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
  specialize (H Δ).
  cbn [is_normal1] in H.

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

Lemma T2_5_neg : ~ forall (atom : Type) (A B C : @formula atom), [$(A /\ B) -> C$] |= $(A /\ ~C) -> ~B$.
 Proof.
  unfold not.
  intro H.
  specialize (H atom3 P Q S).

  pose (
      R1 :=
        fun (w1 w2 w3: worlds4) => (w1 = Γ /\ w2 = w3)
    ).

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
    intro w.
    destruct w ; intro H1.
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
  specialize (H Δ).
  simpl in H.
  unfold not in H.
  apply H.
  split.
  - exact I.
  - intro H1.
    exact H1.
  - exact I.
Qed.
End Semantic.