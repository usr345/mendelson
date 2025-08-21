Module MSet.

(* Instead of working with lists of assumptions we shall work with
   sets of assumptions. A set of formulas can be represented by its
   characteristic map formula -> Prop.
*)

(* Отношение принадлежности между элементом типа T и множеством с элементами типа T *)
Definition elem {T : Type} (A : T) (Γ : T  -> Prop) := Γ A.

Declare Scope sets_scope.
Open Scope sets_scope.
Declare Custom Entry sets_view.

(* Пустое множество объектов типа T. *)
Definition empty {T : Type} : T -> Prop := fun _ => False.
Infix "∈" := elem (at level 77) : sets_scope.

(* The union of two sets of formulas. *)
Definition union {T : Type} (Γ Δ : T -> Prop) (A : T) := (elem A Γ) \/ A ∈ Δ.
Infix "∪" := union (at level 78, left associativity) : sets_scope.

(* Γ --- подмножество Δ. *)
Definition subset {T : Type} (Γ Δ : T -> Prop) :=
  forall A, A ∈ Γ -> A ∈ Δ.
Infix "⊆" := subset (at level 79) : sets_scope.

(* "extend Γ A" is the set Γ ∪ {A}. *)
Definition extend {T : Type} (Γ : T -> Prop) (A : T) : T -> Prop := fun B : T => or (B ∈ Γ) (A = B).

Notation "Γ ,, A" := (extend Γ A) (at level 32, left associativity).

(* Множество Gamma является подмножеством (Gamma,, A) *)
Lemma subset_extend {T : Type} {Γ : T -> Prop} {A : T} : subset Γ (extend Γ A).
Proof.
  unfold subset, extend.
  intros A0 H.
  unfold elem.
  left.
  exact H.
Qed.

End MSet.
Export MSet.

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
