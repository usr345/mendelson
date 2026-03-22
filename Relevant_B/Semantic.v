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
