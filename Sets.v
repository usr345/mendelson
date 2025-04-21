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
