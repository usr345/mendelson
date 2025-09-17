Require Import Lists.List.
(* From Stdlib Require Import Lists.List. *)
Import ListNotations.

Module MSet.

Definition eq_by {T : Type} {TElem : Type} (P : TElem -> T -> Prop) (x y : T) : Prop := forall e : TElem, P e x <-> P e y.

Record TSet (T : Type) : Type := mkTSet {
  struct_t : Type;
  empty : struct_t;
  elem : T -> struct_t -> Prop;
  union : struct_t -> struct_t  -> struct_t;
  extend : struct_t -> T -> struct_t;
  extend_correct (G : struct_t) (A: T) : elem A (extend G A);
  extend_elem (G : struct_t) (A B: T) : elem B (extend G A) -> elem B G \/ A = B;
  union_correct (G H : struct_t) (A: T) : elem A (union G H) <-> elem A G \/ elem A H;
  union_zero (A: struct_t) : eq_by elem (union A empty) A;
}.

Lemma eq_by1 {T : Type} {TElem : Type} (x y : T) : x = y -> forall P : TElem -> T -> Prop, eq_by P x y.
Proof.
  intros Heq P.
  unfold eq_by.
  intro a.
  rewrite Heq.
  reflexivity.
Qed.

Declare Scope sets_scope.
Open Scope sets_scope.
Infix "∈" := (elem _ _) (at level 77) : sets_scope.
Infix "∪" := (union _ _) (at level 78, left associativity) : sets_scope.
Notation "Γ ,, A" := (extend _ _ Γ A) (at level 32, left associativity) : sets_scope.

Coercion TSet_Type {T : Type} (s : TSet T): Type := s.(struct_t T).

(* Parameter elem_dec {T : Type} `{Set_obj: TSet T} (obj : Set_obj) : forall x : T, { elem Set_obj t } + { ~elem Set_obj t }. *)

Definition Prop_extend {T : Type} (Γ : T -> Prop) (A : T) := fun x : T => Γ x \/ A = x.

Lemma Prop_extend_correct {T : Type} (G : T -> Prop) (A : T) : (Prop_extend G A) A.
Proof.
  unfold Prop_extend.
  right.
  reflexivity.
Qed.

Lemma Prop_extend_elem {T : Type} (G : T -> Prop) (A B: T) : (Prop_extend G A) B -> G B \/ A = B.
Proof.
  intro H.
  unfold Prop_extend in H.
  exact H.
Qed.

Definition Prop_elem {T : Type} (A : T) (Γ : T -> Prop) := Γ A.
Definition Prop_union {T : Type} (Γ Δ : T -> Prop) (A : T) := Γ A \/ Δ A.

Lemma Prop_zero {T : Type} (Γ: T -> Prop) : eq_by Prop_elem (Prop_union Γ (fun _ => False)) Γ.
Proof.
  unfold eq_by.
  unfold Prop_elem.
  unfold Prop_union.
  intro a.
  split ; intro H.
  - destruct H.
    + exact H.
    + destruct H.
  - left.
    exact H.
Qed.

Lemma Prop_union_correct {T : Type} (Γ Δ: T -> Prop) (A: T) :
  (Prop_elem A (Prop_union Γ Δ)) <-> ((Prop_elem A Γ) \/ (Prop_elem A Δ)).
Proof.
  unfold Prop_elem.
  unfold Prop_union.
  reflexivity.
Qed.

Definition Prop_Set (T : Type) : TSet T := {|
  struct_t := T -> Prop;
  empty _ := False;
  elem := Prop_elem;
  union := Prop_union;
  extend := Prop_extend;
  extend_correct := Prop_extend_correct;
  extend_elem := Prop_extend_elem;
  union_correct := Prop_union_correct;
  union_zero := Prop_zero;
|}.

Definition List_extend {T : Type} (lst : list T) (A : T) := cons A lst.

Lemma List_extend_correct {T : Type} (lst : list T) (A : T) : In A (List_extend lst A).
Proof.
  unfold List_extend.
  simpl.
  left.
  reflexivity.
Qed.

Lemma List_extend_elem {T : Type} (lst : list T) (A B : T) : In B (List_extend lst A) -> In B lst \/ A = B.
Proof.
  intro H.
  unfold List_extend in H.
  simpl in H.
  rewrite or_comm in H.
  exact H.
Qed.

Lemma List_append_comm {T : Type} (Γ Δ: list T) : forall a : T,
    In a (Γ ++ Δ) -> In a (Δ ++ Γ).
Admitted.

Lemma List_union_correct {T : Type} (Γ Δ: list T) (A: T) :
  In A (Γ ++ Δ) <-> (In A Γ) \/ (In A Δ).
Proof.
  split.
  - apply in_app_or.
  - apply in_or_app.
Qed.

Lemma List_union_zero {T : Type} (Γ: list T) : eq_by (@In T) (Γ ++ nil) Γ.
Proof.
  unfold eq_by.
  intro a.
  rewrite app_nil_r.
  reflexivity.
Qed.

Definition List_Set (T : Type) : TSet T := {|
  struct_t := list T;
  empty := nil;
  elem := @In T;
  union := @app T;
  extend := List_extend;
  extend_correct := List_extend_correct;
  extend_elem := List_extend_elem;
  union_correct := List_union_correct;
  union_zero := List_union_zero;
|}.

(* Общие теоремы для объединения *)
Lemma union_comm {T : Type} {SetType : TSet T} (Γ Δ: SetType) : eq_by (elem T SetType) (Γ ∪ Δ) (Δ ∪ Γ).
Proof.
  unfold eq_by.
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

Lemma union_assoc {T : Type} {SetType : TSet T} (Γ Δ Ε : SetType) : eq_by (elem T SetType) ((Γ ∪ Δ) ∪ Ε) (Γ ∪ (Δ ∪ Ε)).
Proof.
  unfold eq_by.
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

Lemma union_idempotent {T : Type} {SetType : TSet T} (Γ : SetType) : eq_by (elem T SetType) (Γ ∪ Γ) Γ.
Proof.
  unfold eq_by.
  intro a.
  split ; intros H.
  - apply union_correct in H.
    destruct H ; exact H.
  - apply union_correct.
    left.
    exact H.
Qed.

Definition subset {T : Type} {Set_obj1 Set_obj2 : TSet T} (Γ : Set_obj1) (Δ : Set_obj2 ) : Prop :=
  forall A : T, A ∈ Γ -> A ∈ Δ.

Infix "⊆" := subset (at level 79) : sets_scope.

Definition set_eq {T : Type} {Set_obj1 Set_obj2 : TSet T} (Γ : Set_obj1) (Δ : Set_obj2) : Prop :=
  forall A : T, A ∈ Γ <-> A ∈ Δ.

(* Δ is a proper extension of Γ *)
Definition proper_extension {T : Type} {Set_obj1 Set_obj2: TSet T} (Γ : Set_obj1) (Δ : Set_obj2) :=
  Γ ⊆ Δ /\ ~ set_eq Γ Δ.

Lemma subset_refl {T : Type} `{Set_obj : TSet T} {Γ : Set_obj} : subset Γ Γ.
Proof.
  unfold subset.
  intros A H.
  exact H.
Qed.

Lemma subset_trans {T : Type} {Set_obj1 Set_obj2 Set_obj3 : TSet T} {Γ : Set_obj1} {Δ : Set_obj2} {Ε : Set_obj3} : subset Γ Δ -> subset Δ Ε -> subset Γ Ε.
Proof.
  unfold subset.
  intros H1 H2.
  intros A H3.
  specialize (H1 A).
  specialize (H2 A).
  specialize (H1 H3).
  specialize (H2 H1).
  exact H2.
Qed.

Lemma Prop_subset_union1 {T : Type} (Γ Δ : Prop_Set T) : Γ ⊆ (Γ ∪ Δ).
Proof.
  unfold subset.
  intros A H.
  unfold union.
  simpl.
  unfold Prop_elem.
  unfold Prop_union.
  unfold elem in H.
  simpl in H.
  unfold Prop_elem in H.
  left.
  exact H.
Qed.

(*
TODO
A <-> B -> C <-> D -> (subset A C) <-> subset (B D) *)
Lemma Prop_subset_union2 {T : Type} (Γ Δ : Prop_Set T) : Δ ⊆ (Γ ∪ Δ).
Proof.
  specialize (union_comm T (Prop_Set T) Γ Δ) as H.
  unfold eq_by in H.
  specialize (Prop_subset_union1 Δ Γ) as H1.
  unfold subset in H1.
  rewrite H in H1.
  unfold subset.
  intros A Δ_A.
Qed.

Record TSet2 (T : Type) := {
  TSet_car : TSet T;
  subset_extend {Γ : TSet_car} X : subset Γ (extend _ _ Γ X);
  union_subset1 (A B: struct_t) : A ⊆ (union A B;
  union_subset2 (A B: struct_t) : B ⊆ (union A A);
}.

Coercion TSet2_Type {T : Type} (s : TSet2 T): Type := s.(TSet_car T).(struct_t T).

(* Множество Gamma является подмножеством (Gamma ,, A) *)
Lemma Prop_subset_extend {T : Type} (Γ : Prop_Set) (A : T) : Γ ⊆ (Γ ,, A).
Proof.
  unfold subset, extend.
  intros A0 H.
  simpl.
  unfold elem in H.
  simpl in H.
  unfold Prop_extend.
  left.
  exact H.
Qed.

Lemma List_Prop_subset_extend_not {T : Type} {Set_obj : TSet T} (Γ: Set_obj) (Δ: @List_Set T) (A: T) : Δ ⊆ (Γ ,, A) -> ~(A ∈ Δ) -> Δ ⊆ Γ.
Proof.
  intros H1 H2.
  unfold subset.
  intros B Δ_B.
  unfold subset in H1.
  specialize (H1 B).
  specialize (H1 Δ_B).
  apply extend_elem in H1.
  destruct H1.
  - exact H.
  - rewrite <-H in Δ_B.
    specialize (H2 Δ_B).
    destruct H2.
Qed.

Definition Prop_Set2 {T : Type} : @TSet2 T :=
{|
  TSet_car := Prop_Set;
  subset_extend := Prop_subset_extend;
|}.

(* Список Gamma является подмножеством (Gamma ,, A) *)
Lemma List_subset_extend {T : Type} (lst : List_Set) (A : T) : lst ⊆ (lst ,, A).
Proof.
  unfold subset, extend.
  intros A0 H.
  unfold elem.
  simpl.
  right.
  unfold elem in H.
  simpl in H.
  exact H.
Qed.

Definition List_Set2 {T : Type} : @TSet2 T :=
{|
  TSet_car := List_Set;
  subset_extend := List_subset_extend;
|}.

Lemma List_elem_excl_middle (T : Type) (Heq_dec : forall x y : T, {x = y} + {x <> y}) (l : list T) : forall x : T, {In x l} + {~ In x l}.
Proof.
  intro x.
  induction l as [|a l' IH].
  - right.
    unfold In.
    intro H.
    exact H.
  - destruct (Heq_dec x a) eqn:Heq.
    + left.
      cbn.
      left.
      symmetry.
      exact e.
    + destruct IH as [In_x_l | nIn_x_l].
      * left.
        cbn.
        right.
        exact In_x_l.
      * right.
        cbn.
        unfold not.
        intro H.
        destruct H.
        ** symmetry in H.
           specialize (n H) as Hcontra.
           destruct Hcontra.
        ** specialize (nIn_x_l H) as Hcontra.
           destruct Hcontra.
Qed.

Lemma nil_subset_Prop {T : Type} {Γ : Prop_Set} : @subset T List_Set Prop_Set nil Γ.
Proof.
  unfold subset.
  intros A1 H.
  unfold elem in H.
  simpl in H.
  destruct H.
Qed.

Lemma nil_subset_list {T : Type} {lst: List_Set} : @subset T List_Set List_Set nil lst.
Proof.
  unfold subset.
  intros A1 H.
  unfold elem in H.
  simpl in H.
  destruct H.
Qed.

Lemma subset_extend_no_A {T : Type} `{Set_obj1 : TSet T} `{Set_obj2 : TSet T} {Γ : Set_obj1} {Δ : Set_obj2} (A : T) : Δ ⊆ (Γ ,, A) -> ~(A ∈ Δ) -> Δ ⊆ Γ.
Proof.
  intros H1 H2.
  unfold subset.
  intros B Δ_B.
  unfold subset in H1.
  specialize (H1 B Δ_B).
  apply extend_elem in H1.
  destruct H1 as [H1 | H1].
  - exact H1.
  - rewrite <-H1 in Δ_B.
    specialize (H2 Δ_B).
    destruct H2.
Qed.

Lemma subset_app_eq_conj {T : Type} {SetType : TSet T} (lst1 lst2 : List_Set) (all : SetType) : (@subset T List_Set SetType (lst1 ++ lst2) all) <-> ((@subset T List_Set SetType lst1 all) /\ (@subset T List_Set SetType lst2 all)).
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
