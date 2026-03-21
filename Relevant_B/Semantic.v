From Basis Require Export MSets.
From Relevant_B Require Import Formula.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Classical_Prop.
Import ListNotations.
Import FormulaDef.
Import Relevant_B_Formula.
Import Relation.
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

  Record Model_inclusion {atom : Type} :=
  {
    base_model_incl :> @Model atom;
    inclusion : relation base_model_incl.(worlds);
    incl_refl : reflexive inclusion;
    incl_trans : transitive inclusion;
    incl_C1 : forall (w w' : base_model_incl.(worlds)) (a : atom), 
      inclusion w w' -> base_model_incl.(v) a w -> base_model_incl.(v) a w';
    incl_C2 : forall w w' : base_model_incl.(worlds), inclusion w w' ->
      inclusion (base_model_incl.(star) w') (base_model_incl.(star) w);
    incl_C3 : forall w w' w1 w2 : base_model_incl.(worlds), inclusion w w' ->
      base_model_incl.(R) w' w1 w2 -> 
        (base_model_incl.(is_normal) w = true /\ inclusion w1 w2) \/ (base_model_incl.(is_normal) w = false /\ base_model_incl.(R) w w1 w2);
  }.

  Lemma inclusion_eval {atom : Type} (m : @Model_inclusion atom) (f : @formula atom) :
    forall w1 w2 : m.(worlds), m.(inclusion) w1 w2 -> eval m f w1 -> eval m f w2.
  Proof.
    induction f as [a | f' IH | f1 IH1 f2 IH2 | f1 IH1 f2 IH2 | f1 IH1 f2 IH2] ; intros w1 w2.
    - intros Hincl Hw1.
      cbn [eval] in *.
      specialize (incl_C1 m w1 w2 a) as HC1.
      specialize (HC1 Hincl). 
      specialize (HC1 Hw1).
      exact HC1.
    - intros Hincl Hw1.
      cbn [eval] in *.
      unfold not.
      intro Hstar_w2.
      unfold not in Hw1.
      specialize (incl_C2 m w1 w2) as HC2.
      specialize (HC2 Hincl).
      specialize (IH (star m w2) (star m w1)).
      specialize (IH HC2).
      specialize (IH Hstar_w2).
      specialize (Hw1 IH).
      exact Hw1.
    - intros Hincl Hconj.
      cbn [eval] in *.
      destruct Hconj as [Hw1 Hw2].
      specialize (IH1 w1 w2 Hincl Hw1).
      specialize (IH2 w1 w2 Hincl Hw2).
      exact (conj IH1 IH2).
    - intros Hincl Hdisj.
      cbn [eval] in *.
      specialize (IH1 w1 w2 Hincl).
      specialize (IH2 w1 w2 Hincl).
      destruct Hdisj as [H | H].
      + specialize (IH1 H).
        left.
        exact IH1.
      + specialize (IH2 H).
        right.
        exact IH2.
    - intros Hincl Himpl.
      cbn [eval] in *.
      intros x y HR Hx.
      specialize (incl_C3 m w1 w2 x y) as HC3.
      specialize (HC3 Hincl HR).
      destruct HC3 as [HC3 | HC3].
      + destruct HC3 as [Hnormal Incl_xy].
        specialize (Rnormal m w1 y y Hnormal) as HRyy.
        specialize (eq_refl y) as Hy1.
        rewrite <-HRyy in Hy1.
        clear HRyy.
        rename Hy1 into HRy.
        specialize (IH1 x y).
        specialize (IH1 Incl_xy).
        specialize (IH1 Hx).
        specialize (Himpl y y).
        specialize (Himpl HRy IH1).
        exact Himpl.
      + destruct HC3 as [Hnormal Rxy].
        specialize (Himpl x y).
        specialize (Himpl Rxy Hx).
        exact Himpl.
  Qed.

  Record Model_T12 {atom : Type} :=
  {
    base_model_T12 :> @Model_inclusion atom;
    T12 : forall x y z : base_model_T12.(worlds), base_model_T12.(R) x y z -> 
      exists j : base_model_T12.(worlds), base_model_T12.(inclusion) x j /\ base_model_T12.(R) y j z;
  }.

  Instance Model_T12_IsModel (atom : Type) : IsModel atom (@Model_T12 atom) :=
  {
    to_model :=  fun (m : @Model_T12 atom) => m;
  }.

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

  Record Model_T13 {atom : Type} :=
  {
    base_model_T13 :> @Model_inclusion atom;
    T13 : forall w : base_model_T13.(worlds), base_model_T13.(is_normal) w = true -> 
      base_model_T13.(inclusion) (star base_model_T13 w) w;
  }.

  Instance Model_T13_IsModel (atom : Type) : IsModel atom (@Model_T13 atom) :=
  {
    to_model :=  fun (m : @Model_T13 atom) => m;
  }.

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

  Record Model_T14 {atom : Type} :=
  {
    base_model_T14 :> @Model_inclusion atom;
    T14 : forall w : base_model_T14.(worlds), 
      match base_model_T14.(is_normal) w with
      | true => base_model_T14.(inclusion) (star base_model_T14 w) w
      | false => base_model_T14.(R) w (star base_model_T14 w) w
      end;
  }.

  Instance Model_T14_IsModel (atom : Type) : IsModel atom (@Model_T14 atom) :=
  {
    to_model :=  fun (m : @Model_T14 atom) => m;
  }.

  Lemma T14_to_T13 {atom : Type} (m : @Model_T14 atom) : @Model_T13 atom.
  Proof.
     assert (HT13 : forall w : worlds m, is_normal m w = true -> 
      inclusion m (star m w) w).
     {
        intros w Hnormal.
        specialize (T14 m w) as HT14.
        rewrite Hnormal in HT14.
        exact HT14.
     }

     pose (M1 := {|
      base_model_T13 := base_model_T14 m;
      T13 := HT13;
    |}).

    exact M1.
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

  Record Model_T15 {atom : Type} :=
  {
    base_model_T15 :> @Model_inclusion atom;
    T15 : forall x y z : base_model_T15.(worlds),
      base_model_T15.(R) x y z -> base_model_T15.(inclusion) x z;
  }.

  Instance Model_T15_IsModel (atom : Type) : IsModel atom (@Model_T15 atom) :=
  {
    to_model :=  fun (m : @Model_T15 atom) => m;
  }.

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

  Record Model_T16 {atom : Type} :=
  {
    base_model_T16 :> @Model_inclusion atom;
    T16 : forall x y z : base_model_T16.(worlds),
      base_model_T16.(R) x y z -> base_model_T16.(inclusion) x z \/ base_model_T16.(inclusion) y z;
  }.

  Instance Model_T16_IsModel (atom : Type) : IsModel atom (@Model_T16 atom) :=
  {
    to_model :=  fun (m : @Model_T16 atom) => m;
  }.

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

  Record Model_R {atom : Type} :=
  {
    base_model_R :> @Model_inclusion atom;
    A8 : forall x y z : base_model_R.(worlds), base_model_R.(R) x y z -> base_model_R.(R) x (base_model_R.(star) z) (base_model_R.(star) y);
    A9 : forall x y z u v : base_model_R.(worlds), base_model_R.(R) x y z -> base_model_R.(R) z u v -> 
          exists j : base_model_R.(worlds), base_model_R.(R) x u j /\ base_model_R.(R) y j v;
    A10 : forall x y z u v : base_model_R.(worlds), base_model_R.(R) x y z -> base_model_R.(R) z u v -> 
          exists j : base_model_R.(worlds), base_model_R.(R) y u j /\ base_model_R.(R) x j v;
    A11 : forall x y z : base_model_R.(worlds), base_model_R.(R) x y z -> 
          exists j : base_model_R.(worlds), base_model_R.(R) x y j /\ base_model_R.(R) j y z;
    A12 : forall x y z : base_model_R.(worlds), base_model_R.(R) x y z -> 
      exists j : base_model_R.(worlds), base_model_R.(inclusion) x j /\ base_model_R.(R) y j z;
  }.

  Instance Model_R_IsModel (atom : Type) : IsModel atom (@Model_R atom) :=
  {
    to_model :=  fun (m : @Model_R atom) => m;
  }.

  Lemma flip_valid {atom : Type} (A B C : @formula atom): consequence (@Model_R atom) [$A -> (B -> C)$] $B -> (A -> C)$.
  Proof.
    unfold consequence.
    intros m w Hnormal Hall.
    apply holds_all_single in Hall.
    simpl in Hall.
    simpl.
    intros x y HRxy HB.
    intros u v.
    intros HRuv HA.
    specialize (Hall u).
    specialize (Rnormal m w x y Hnormal) as Heq.
    apply Heq in HRxy as Heq1.
    clear Heq.
    rename Heq1 into Heq.
    rewrite Heq in HRxy.
    rewrite Heq in HB.
    specialize (A12 m y u v) as H12.
    specialize (H12 HRuv).
    destruct H12 as [j [Hincl HRjv]].
    specialize (inclusion_eval m B) as HBj.
    specialize (HBj y j Hincl HB) as HBj.
    specialize (Rnormal m w u u Hnormal) as HRuu.
    specialize (eq_refl u) as HRu.
    apply HRuu in HRu.
    clear HRuu.
    specialize (Hall u HRu HA).
    specialize (Hall j v).
    specialize (Hall HRjv HBj).
    exact Hall.
  Qed.

End Semantic.
