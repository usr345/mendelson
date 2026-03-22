From Relevant_B Require Import Formula.
From Relevant_B Require Import Syntactic.
From Relevant_B Require Import Semantic.
From Coq Require Import Lists.List.
From Coq Require Import Classical_Prop.
Import ListNotations.

Import FormulaDef.
Import Relevant_B_Formula.
Import Semantic.
Import Syntactic_R.
Import Functions.

Module Semantic_B_exercises.
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

End Semantic_B_exercises.

Module Syntactic_R_exercises.
Lemma mirabilis {atom : Type} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $(A -> ~A) -> ~A$.
Proof.
  specialize_axiom (identity (Γ:=Γ) $A -> ~A$) H1.
  specialize_axiom (permutation (Γ:=Γ) H1) H2.
  specialize_axiom (contrapos (Γ:=Γ) $A -> ~A$ A) H3.
  specialize (trans_prefix_rule H3 H2) as H4.
  specialize_axiom (mp_surreal (Γ:=Γ) A $~(A -> ~A)$) H5.
  specialize (mp H5 H4) as H6.
  specialize (contrapos_rule H6) as H7.
  exact H7.
Qed.

Lemma excluded_middle {atom : Type} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A \/ ~A$.
Proof.
  specialize_axiom (disj_intro_left (Γ:=Γ) A $~A$) H1.
  specialize (A_nnA Γ $A \/ ~A$) as H2.
  specialize (trans_suffix_rule H1 H2) as H3.
  specialize (contrapos_rule H3) as H4.
  specialize_axiom (disj_intro_right (Γ:=Γ) A $~A$) H5.
  specialize (trans_suffix_rule H4 H5) as H6.
  specialize (trans_suffix_rule H6 H2) as H7.
  specialize (mirabilis Γ $~(A \/ ~A)$) as H8.
  specialize (mp H8 H7) as H9.
  specialize (neg_elim_rule H9) as H10.
  exact H10.
Qed.
End Syntactic_R_exercises.