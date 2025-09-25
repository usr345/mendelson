Require Import Lists.List.
(* From Stdlib Require Import Lists.List. *)
Import ListNotations.

Module MSet.

Record TSet (T : Type) : Type := mkTSet {
  struct_t : Type;
  elem : T -> struct_t -> Prop;
  empty : struct_t;
  sgt : T -> struct_t;
  union : struct_t -> struct_t  -> struct_t;
  subtract : struct_t -> struct_t -> struct_t;
  empty_correct : forall a : T, ~ elem a empty;
  sgt_correct (a b : T) : elem b (sgt a) <-> a = b;
  union_correct (G H : struct_t) (a: T) : elem a (union G H) <-> elem a G \/ elem a H;
  subtract_correct Γ Δ A : elem A (subtract Γ Δ) <-> elem A Γ /\ ~ elem A Δ;
}.

Coercion TSet_Type {T : Type} (s : TSet T): Type := s.(struct_t T).

Definition extend {T : Type} {Set_obj : TSet T} (Γ : Set_obj) (A : T) := union _ _ Γ (sgt _ _ A).
Definition subtract_elem {T : Type} {Set_obj : TSet T} (Γ : Set_obj) (A : T) := subtract _ _ Γ (sgt _ _ A).

Section Constructs.

  Context {T : Type} {Set_obj1 Set_obj2 : TSet T} (Γ : Set_obj1) (Δ : Set_obj2).

  Definition subset := forall A : T, elem _ _ A Γ -> elem _ _ A Δ.
  Definition set_eq := forall A : T, elem _ _ A Γ <-> elem _ _ A Δ.
  Definition proper_extension := subset /\ ~ set_eq.

End Constructs.

Declare Scope sets_scope.
Open Scope sets_scope.
Infix "∈" := (elem _ _) (at level 71, left associativity) : sets_scope.
Notation "∅" := (empty _ _) : sets_scope.
Infix "∪" := (union _ _) (at level 71, left associativity) : sets_scope.
Infix "∖∖" := (subtract _ _) (at level 69, left associativity) : sets_scope.
Infix "∖" := subtract_elem  (at level 69, left associativity) : sets_scope.
Notation "Γ ,, A" := (extend Γ A) (at level 32, left associativity) : sets_scope.
Infix "≡" := set_eq (at level 73) : sets_scope.
Infix "⊆" := subset (at level 73) : sets_scope.
Infix "⊊" := proper_extension (at level 73) : sets_scope.

Lemma no_elem_in_empty {T : Type} {Set_obj : TSet T} (A : T) : A ∈ (∅ : Set_obj) <-> False.
Proof.
  split.
  - intro H.
    apply empty_correct in H.
    exact H.
  - intros [].
Qed.

Lemma empty_subtract {T : Type} {Set_obj : TSet T} {Γ : Set_obj} : (∅ : Set_obj) ≡ Γ ∖∖ Γ.
Proof.
  unfold set_eq.
  intro a.
  split.
  - rewrite no_elem_in_empty.
    intros [].
  - rewrite subtract_correct.
    intros [H1 H2].
    apply H2 in H1.
    rewrite no_elem_in_empty.
    exact H1.
Qed.

Lemma empty_subset {T : Type} {Set_obj1 : TSet T} (Set_obj2 : TSet T) (Γ : Set_obj1) : (∅ : Set_obj2) ⊆ Γ.
Proof.
  unfold subset.
  intros a H.
  apply empty_correct in H.
  destruct H.
Qed.

Lemma extend_correct {T : Type} {Set_obj : TSet T} (Γ : Set_obj) (A B: T) : B ∈ Γ,, A <-> A = B \/ B ∈ Γ.
Proof.
  unfold extend.
  split.
  - intro H.
    rewrite union_correct in H.
    destruct H.
    + right.
      exact H.
    + rewrite sgt_correct in H.
      left.
      exact H.
  - intro H.
    rewrite union_correct.
    destruct H.
    + right.
      apply sgt_correct.
      exact H.
    + left.
      exact H.
Qed.

Lemma subtract_elem_correct {T : Type} {Set_obj : TSet T} {Γ : Set_obj} (A B : T) : B ∈ (Γ ∖ A) <-> A <> B /\ B ∈ Γ.
Proof.
  unfold subtract_elem.
  rewrite subtract_correct.
  rewrite sgt_correct.
  split.
  - intros [H1 H2].
    apply (conj H2 H1).
  - intros [H1 H2].
    apply (conj H2 H1).
Qed.

Lemma subset_refl {T : Type} {Set_obj : TSet T} {Γ : Set_obj} : subset Γ Γ.
Proof.
  exact (fun _ Proof_a_Γ => Proof_a_Γ).
Qed.

Lemma subset_trans {T : Type} {Set_obj Set_obj2 Set_obj3 : TSet T} {Γ : Set_obj} {Δ : Set_obj2} {Σ : Set_obj3} :
  Γ ⊆ Δ -> Δ ⊆ Σ -> Γ ⊆ Σ.
Proof.
  exact (fun H1 H2 A H3 => H2 A (H1 A H3)).
Qed.

Lemma subset_extend {T : Type} {Set_obj : TSet T} (Γ : Set_obj) (A : T) : Γ ⊆ Γ,, A.
Proof.
  intros B HB.
  apply extend_correct.
  right.
  assumption.
Qed.

Lemma subset_extend_not {T : Type} {Set_obj Set_obj2 : TSet T} (Γ : Set_obj) (Δ : Set_obj2) (A: T) :
  Δ ⊆ Γ,, A -> ~ A ∈ Δ -> Δ ⊆ Γ.
Proof.
  intros H1 H2 B HB.
  unfold subset in H1.
  specialize (H1 B HB).
  apply extend_correct in H1.
  destruct H1.
  - rewrite H in H2.
    contradiction.
  - exact H.
Qed.

Lemma extend_subtract {T : Type} {Set_obj Set_obj2 : TSet T} {Γ : Set_obj} {Δ : Set_obj2} (X: T) :
  Γ ⊆ (Δ ,, X) -> (Γ ∖ X) ⊆ Δ.
Proof.
  intros H1.
  unfold subset in H1.
  unfold subset.
  intros a H2.
  specialize (H1 a).
  unfold subtract_elem in H2.
  rewrite subtract_correct in H2.
  destruct H2 as [Γ_a H2].
  rewrite sgt_correct in H2.
  specialize (H1 Γ_a).
  rewrite extend_correct in H1.
  destruct H1 as [H1 | H1].
  - apply H2 in H1.
    destruct H1.
  - exact H1.
Qed.

Lemma not_conj1 (A B : Prop) : ~(A /\ B) -> A -> ~B.
Proof.
  unfold not.
  intros HnA_B HA HB.
  specialize (conj HA HB) as HA_B.
  specialize (HnA_B HA_B) as HContra.
  exact HContra.
Qed.

Lemma DeMogran_conj2 (A B : Prop) : ~A \/ ~B -> ~(A /\ B).
Proof.
  intro H.
  unfold not in H.
  unfold not.
  intros [H1 H2].
  destruct H.
  - exact (H H1).
  - exact (H H2).
Qed.

(* Lemma subset_equal {T : Type} {Set_obj Set_obj2 : TSet T} {Γ : Set_obj} {Δ : Set_obj2} : *)
(*   Γ ⊆ Δ -> ~(Γ ⊊ Δ) -> Γ ≡ Δ. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   unfold set_eq. *)
(*   intro a. *)
(*   split ; intro H3. *)
(*   - unfold subset in H1. *)
(*     specialize (H1 a H3). *)
(*     exact H1. *)
(*   - unfold proper_extension in H2. *)
(*     specialize (not_conj1 _ _ H2 H1) as H4. *)

Lemma union_subset {T : Type} {Set_obj Set_obj2 : TSet T} {Γ : Set_obj} {Δ Σ : Set_obj2} :
  Δ ⊆ Γ -> Σ ⊆ Γ -> (Δ ∪ Σ) ⊆ Γ.
Proof.
  intros H1 H2.
  unfold subset.
  intros a H3.
  rewrite union_correct in H3.
  unfold subset in H1, H2.
  specialize (H1 a).
  specialize (H2 a).
  destruct H3 as [H3 | H3].
  - specialize (H1 H3).
    exact H1.
  - specialize (H2 H3).
    exact H2.
Qed.

(* Общие теоремы для объединения *)
Lemma union_zero {T : Type} {Set_obj : TSet T} {Γ : Set_obj} : Γ ∪ ∅ ≡ Γ.
Proof.
  unfold set_eq.
  intro A.
  split.
  - intro H.
    rewrite union_correct in H.
    destruct H.
    + exact H.
    + apply empty_correct in H.
      destruct H.
  - intro H.
    apply union_correct.
    left.
    exact H.
Qed.

Lemma union_comm {T : Type} {Set_obj : TSet T} {Γ Δ: Set_obj} : Γ ∪ Δ ≡ Δ ∪ Γ.
Proof.
  intro a.
  split ; intros H.
  - apply union_correct in H.
    apply union_correct.
    apply or_comm.
    exact H.
  - apply union_correct in H.
    apply union_correct.
    apply or_comm.
    exact H.
Qed.

Lemma union_assoc {T : Type} {Set_obj : TSet T} {Γ Δ Σ: Set_obj} : ((Γ ∪ Δ) ∪ Σ) ≡ (Γ ∪ (Δ ∪ Σ)).
Proof.
  intro a.
  split ; intros H.
  - apply union_correct in H.
    apply union_correct.
    destruct H.
    + apply union_correct in H.
      destruct H.
      * left.
        exact H.
      * right.
        apply union_correct.
        left.
        exact H.
    + right.
      apply union_correct.
      right.
      exact H.
  - apply union_correct in H.
    apply union_correct.
    destruct H.
    + left.
      apply union_correct.
      left.
      exact H.
    + apply union_correct in H.
      destruct H.
      * left.
        apply union_correct.
        right.
        exact H.
      * right.
        exact H.
Qed.

Lemma union_idempotent {T : Type} {Set_obj : TSet T} {Γ: Set_obj} : Γ ∪ Γ ≡ Γ.
Proof.
  intro a.
  split ; intros H.
  - apply union_correct in H.
    destruct H ; exact H.
  - apply union_correct.
    left.
    exact H.
Qed.

Lemma union_subset1 {T : Type} {Set_obj : TSet T} {Γ Δ: Set_obj} : Γ ⊆ Γ ∪ Δ.
Proof.
  intros a H.
  apply union_correct.
  left.
  assumption.
Qed.

Lemma union_subset2 {T : Type} {Set_obj : TSet T} {Γ Δ: Set_obj} : Δ ⊆ Γ ∪ Δ.
Proof.
  intros a H.
  apply union_correct.
  right.
  assumption.
Qed.

(* Instances *)
Definition Prop_Set (T : Type) : TSet T := {|
  struct_t := T -> Prop;
  empty _ := False;
  elem A Γ := Γ A;
  union Γ Δ A := Γ A \/ Δ A;
  subtract Γ Δ A := Γ A /\ ~ Δ A;
  sgt := @eq T;
  sgt_correct _ _ := iff_refl _;
  union_correct _ _ _ := iff_refl _;
  subtract_correct _ _ _ := iff_refl _;
  empty_correct := fun _ X => match X with end;
|}.

Section EqDec.

  Context (T : Type) (eq_dec : forall x y : T, {x = y} + {x <> y}).

  Definition List_subtract l1 l2 := fold_right (remove eq_dec) l1 l2.

  Lemma List_subtract_correct l1 l2 A : In A (List_subtract l1 l2) <-> In A l1 /\ ~ In A l2.
  Proof.
    induction l2; [ tauto | split ].
    - cbn. intros [Hin Hneq]%in_remove. split.
      + apply IHl2, Hin.
      + intros [-> | Hin2].
    * contradiction Hneq. reflexivity.
    * revert Hin2. apply IHl2, Hin.
    - intros [Hin1 Hnin2].
      cbn. apply in_in_remove.
      + intros [= ->]. apply Hnin2, in_eq.
      + apply IHl2. split; [ assumption | ].
        intro Hin. apply Hnin2, in_cons, Hin.
  Qed.

  Definition List_Set : TSet T := {|
    struct_t := list T;
    empty := nil;
    elem := @In T;
    union := @app T;
    subtract := List_subtract;
    sgt A := [A];
    sgt_correct := ltac:(cbn; tauto);
    union_correct := (@in_app_iff _);
    subtract_correct := List_subtract_correct;
    empty_correct := fun _ X => match X with end;
  |}.

End EqDec.

Lemma List_elem_excl_middle (T : Type) (Heq_dec : forall x y : T, {x = y} + {x <> y}) (l : list T) : forall x : T, {In x l} + {~ In x l}.
Proof.
  intro x.
  exact (in_dec Heq_dec x l).
Qed.

Lemma subset_app_eq_conj {T : Type} {SetType : TSet T} (eq_dec : forall x y : T, {x = y} + {x <> y}) (lst1 lst2 : List_Set T eq_dec) (all : SetType) : (@subset T (List_Set T eq_dec) SetType (lst1 ++ lst2) all) <-> ((@subset T (List_Set T eq_dec) SetType lst1 all) /\ (@subset T (List_Set T eq_dec) SetType lst2 all)).
Proof.
  split.
  - intro H.
    unfold subset in H.
    unfold subset.
    split.
    + intros A H1.
      unfold elem in H1.
      simpl in H1.
      specialize (H A).
      assert (Hor : In A lst1 \/ In A lst2).
      {
        left.
        apply H1.
      }

      apply in_or_app in Hor.
      simpl in H.
      specialize (H Hor).
      exact H.
    + intros A H1.
      unfold elem in H1.
      simpl in H1.
      specialize (H A).
      simpl in H.
      assert (Hor : In A lst1 \/ In A lst2).
      {
        right.
        apply H1.
      }

      apply in_or_app in Hor.
      specialize (H Hor).
      exact H.
  - intro H.
    unfold subset in H.
    unfold subset.
    intros A H1.
    unfold elem in H1.
    simpl in H1.
    destruct H as [H2 H3].
    specialize (H2 A).
    specialize (H3 A).
    simpl in H2, H3.
    rewrite in_app_iff in H1.
    destruct H1.
    + specialize (H2 H).
      exact H2.
    + specialize (H3 H).
      exact H3.
Qed.

End MSet.
Export MSet.

(* Definition odd (n : nat) : Prop := *)
(*   Nat.modulo n 2 <> 0. *)

(* Definition odd_list : list nat := [1; 3; 5; 7]. *)

(* Check subset. *)
(* Example Test1 : subset odd_list odd. *)

Module Relation.
Definition relation (U: Type) := U -> U -> Prop.

Definition reflexive {U: Type} (R: relation U) :=
  forall x : U, R x x.

Definition symmetric {U : Type} (R: relation U) :=
  forall x y : U, R x y -> R y x.

Definition transitive {U : Type} (R: relation U) :=
  forall x y z : U, R x y -> R y z -> R x z.

Definition serial {U: Type} (R: relation U) :=
  forall x : U, exists y : U, R x y.

(* Two things equal to the third are equal to each other *)
Definition euclidian {U : Type} (R: relation U) :=
  forall x y z : U, R x y -> R x z -> R y z.

Definition linear {U : Type} (R: relation U) :=
  forall x y z : U, R x y -> R x z -> ((R y z) \/ (R z y)).

Definition partially_functional {U : Type} (R: relation U) :=
  forall x y z : U, R x y -> R x z -> y = z.

Definition functional {U : Type} (R: relation U) :=
  forall x : U, exists! y : U, R x y.

Definition weakly_dense {U : Type} (R: relation U) :=
  forall x y : U, R x y -> exists z : U, R x z /\ R z y.

Definition weakly_connected {U : Type} (R: relation U) :=
  forall x y z: U, R x y -> R x z -> (R y z \/ y = z \/ R z y).

Definition weakly_directed {U : Type} (R: relation U) :=
  forall x y z: U, R x y -> R x z -> exists v : U, (R y v /\ R z v).


Lemma relf_eucl_symmetric {U : Type} (R: relation U) :
reflexive R -> euclidian R -> symmetric R.
Proof.
  unfold reflexive, euclidian, symmetric.
  intros Hrefl Heu.
  intros x y H1.
  specialize (Hrefl x) as Hxx.
  specialize (Heu x y x) as H2.
  specialize (H2 H1 Hxx).
  exact H2.
Qed.

(* Excersize 5.4.6 стр. 87*)
Lemma sym_trans_eq_euclidian {U : Type} (R: relation U) (Hrefl: reflexive R) : (symmetric R /\ transitive R) <-> (euclidian R).
Proof.
  split.
  - intro H2.
    destruct H2 as [Hsym Htrans].
    unfold euclidian.
    intros x y z H4 H5.
    unfold symmetric in Hsym.
    unfold transitive in Htrans.
    specialize (Hsym x y H4) as H6.
    specialize (Htrans y x z) as H7.
    specialize (H7 H6 H5) as H7.
    exact H7.
  - intro Heu.
    unfold symmetric, transitive.
    specialize (relf_eucl_symmetric R Hrefl Heu) as Hsym.
    split.
    + apply Hsym.
    + intros x y z H1 H2.
      unfold euclidian in Heu.
      unfold symmetric in Hsym.
      specialize (Hsym x y H1) as H3.
      specialize (Heu y x z) as H4.
      specialize (H4 H3 H2).
      exact H4.
Qed.

End Relation.
Export Relation.
