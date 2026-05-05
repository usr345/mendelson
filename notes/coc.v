Module CoC.
  Definition False_CoC : Prop :=
    forall P : Prop, P.

  Definition not_CoC (P : Prop) : Prop :=
    P -> False_CoC.

  Definition And_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> B -> C) -> C.

  Definition Or_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> C) -> (B -> C) -> C.

  Definition Eq_CoC (A : Type) (x y : A) : Prop :=
    forall (P : A -> Prop), P x -> P y.

  (* Ex - это свойство предиката B на универсуме A, что B не пусто *)
  Definition Ex (A : Type) (B : A -> Prop) : Prop :=
    forall C : Prop, (forall x : A, B x -> C) -> C.

  Definition ex_intro (A : Type) (B : A -> Prop) (t : A) (p : B t) : Ex A B :=
    fun (C : Prop) => fun (H : forall x : A, B x -> C) => H t p.

(*
  Γ ⊢ t : ∃x : A, B Γ, x : A, p : B ⊢ u : C x !∈ Γ, C
  Γ ⊢ t C (fun (x : A)(p : B) ⇒ u) : C
*)
  Definition ex_elim (A : Type) (P : A -> Prop) (C : Prop)
    (H_exists : Ex A P)                    (* Γ ⊢ ∃x:A, P x *)
    (H_goal : forall x : A, P x -> C)      (* Γ ⊢ ∀x:A, P x → C *)
    : C := H_exists C H_goal.
End CoC.

Section CoC_example.
  Import CoC.
  Variable U : Type. (* Универсум *)
  Variable B : U -> Prop. (* Предикат на универсуме *)
  Variable t : U. (* Объект универсума *)

  (* If Γ ⊢ p : B t *)
  (* В контексте Γ p - это доказательство того, что
    объект универсума t удовлетворяет предикату B
   *)
  Variable p : B t.

  Variable Person : Type.
  Variable is_happy : Person -> Prop.
  Variable bob : Person.
  Variable bob_is_happy : is_happy bob.

  (* Proving that someone is happy using our manual Ex *)
  Lemma someone_is_happy : Ex Person is_happy.
  Proof.
    (* This is exactly applying the term: fun C H => H bob bob_is_happy *)
    apply (ex_intro Person is_happy bob bob_is_happy).
  Qed.
End CoC_example.

Section CoC_theorems.
  Import CoC.

  Lemma ex_not_forall (A : Type) (P : A -> Prop) (C : Prop) :
    Ex A P -> not_CoC (forall x : A, not_CoC (P x)).
  Proof.
    intro Hex.
    unfold not_CoC.
    intro Hwit.
    unfold False_CoC.
    intro P0.
    unfold Ex in Hex.
    specialize (Hex P0).
    apply Hex.
    intros x Px.
    specialize (Hwit x Px).
    unfold False_CoC in Hwit.
    specialize (Hwit P0).
    exact Hwit.
  Qed.

  Lemma and_proj1 (A B : Prop) : And_CoC A B -> A.
  Proof.
    intro Hand.
    unfold And_CoC in Hand.
    specialize (Hand A).
    apply Hand.
    intros HA _.
    exact HA.
  Qed.

  Definition and_elim1 : forall {A B : Prop}, And_CoC A B -> A :=
    fun (A B : Prop) =>
      fun (Hand : And_CoC A B) => Hand A (fun (a : A) (b : B) => a).

  Lemma and_proj2 (A B : Prop) : And_CoC A B -> B.
  Proof.
    intro Hand.
    unfold And_CoC in Hand.
    specialize (Hand B).
    apply Hand.
    intros _ HB.
    exact HB.
  Qed.

  Definition and_elim2 : forall {A B : Prop}, And_CoC A B -> B :=
    fun (A B : Prop) =>
     fun (Hand : And_CoC A B) => Hand B (fun (a : A) (b : B) => b).

  Definition and_intro : forall {A B : Prop}, A -> B -> And_CoC A B :=
    fun (A B : Prop) =>
      fun (a : A) (b : B) =>
        fun (C : Prop) (HAB_C : A -> B -> C) => HAB_C a b.

  Lemma and_comm (A B : Prop) : And_CoC A B -> And_CoC B A.
  Proof.
    intro Hand.
    unfold And_CoC in Hand.
    unfold And_CoC.
    intros C H.
    apply Hand.
    intros HA HB.
    specialize (H HB HA).
    exact H.
  Qed.

  Definition and_comm_dir (A B : Prop) : And_CoC A B -> And_CoC B A :=
    fun (Hand : And_CoC A B) =>
      fun (C : Prop) (f : B -> A -> C) =>
        Hand C (fun (a : A) (b : B) => f b a).

  Theorem and_comm_refine (A B : Prop) : And_CoC A B -> And_CoC B A.
  Proof.
    refine (fun Hand : And_CoC A B =>
      fun (C : Prop) (f : B -> A -> C) => Hand C
        (fun (a : A) (b : B) => _)).
    exact (f b a).
  Qed.

  Definition or_intro_left : forall (A B : Prop), A -> Or_CoC A B :=
    fun (A B : Prop) (Ha : A) =>
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hac Ha.

  Definition or_intro_right : forall (A B : Prop), B -> Or_CoC A B :=
    fun (A B : Prop) (Hb : B) =>
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hbc Hb.

  Lemma or_comm (A B : Prop) : Or_CoC A B -> Or_CoC B A.
  Proof.
    intro Hor.
    unfold Or_CoC in Hor.
    unfold Or_CoC.
    intros C HBC HAC.
    specialize (Hor C HAC HBC).
    exact Hor.
  Qed.

  Definition or_comm_dir (A B : Prop) : Or_CoC A B -> Or_CoC B A :=
    fun (Hor : Or_CoC A B) =>
      fun (C : Prop) (fB : B -> C) (fA : A -> C) =>
        Hor C fA fB.

  Definition uncurry : forall {A B C : Prop}, (A -> B -> C) -> (And_CoC A B) -> C :=
    fun (A B C : Prop) =>
      fun (f_abc : A -> B -> C) (Hconj : And_CoC A B) =>
        f_abc (and_elim1 Hconj) (and_elim2 Hconj).

  Definition id : forall A : Type, A -> A :=
    fun (A : Type) (a : A) => a.

  Definition or_idempotent : forall {A : Prop}, Or_CoC A A -> A :=
    fun (A : Prop) (Hor : Or_CoC A A) =>
      Hor A (id A) (id A).

  Definition and_idempotent : forall {A : Prop}, And_CoC A A -> A :=
    fun (A : Prop) (Hand : And_CoC A A) =>
      Hand A (fun (a _ : A) => a).

  Lemma eq_sym (U : Type) (x y : U) : Eq_CoC U x y -> Eq_CoC U y x.
  Proof.
    unfold Eq_CoC.
    intros Hxy P Py.
    apply (Hxy (fun z => P z -> P x)).
    - intro H.
      exact H.
    - exact Py.
  Qed.

  Definition eq_trans_dir (U : Type) (x y z : U) :
    Eq_CoC U x y -> Eq_CoC U y z -> Eq_CoC U x z :=
    fun (Heq1 : Eq_CoC U x y) (Heq2 : Eq_CoC U y z) =>
      fun (P : U -> Prop) (Px : P x) => Heq2 P (Heq1 P Px).

  Definition contrapos (A B : Prop) : (A -> B) -> not_CoC B -> not_CoC A :=
    fun (Impl : A -> B) (notB : not_CoC B) =>
      fun (Ha : A) => notB (Impl Ha).

  Theorem deMorgan_disj : forall A B : Prop, not_CoC (Or_CoC A B) -> And_CoC (not_CoC A) (not_CoC B).
  Proof.
    intros A B H.
    unfold And_CoC.
    intros C H1.
    unfold not_CoC in H.
    unfold Or_CoC in H.
    apply H1.
    - unfold not_CoC.
      intro a.
      apply H.
      intros C0 A_C0 B_C0.
      specialize (A_C0 a).
      exact A_C0.
    - unfold not_CoC.
      intro b.
      apply H.
      intros C0 A_C0 B_C0.
      specialize (B_C0 b).
      exact B_C0.
  Qed.

  Definition deMorgan_disj_dir (A B : Prop) :
    not_CoC (Or_CoC A B) -> And_CoC (not_CoC A) (not_CoC B) :=
    fun (NotOr : not_CoC (Or_CoC A B)) =>
      fun (C : Prop) (H : (not_CoC A) -> (not_CoC B) -> C) =>
        H
          (fun (a : A) => NotOr (or_intro_left A B a))
          (fun (b : B) => NotOr (or_intro_right A B b))
        .

  Definition deMorgan_disj_back : forall (A B : Prop),
    And_CoC (not_CoC A) (not_CoC B) -> not_CoC (Or_CoC A B) :=
    fun (A B : Prop) =>
      fun (Hand : And_CoC (not_CoC A) (not_CoC B)) =>
        fun (Hor : Or_CoC A B) =>
          Hor False_CoC (and_elim1 Hand) (and_elim2 Hand).
End CoC_theorems.
