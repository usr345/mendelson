From Stdlib Require Import Lists.List.

Module MSet.
Class TSet (A : Type) :=
{
  struct_t: Type -> Type;
  empty {T : Type}: struct_t T;
  elem {T : Type}: T -> struct_t T -> Prop;
  union {T : Type}: struct_t T -> struct_t T  -> struct_t T;
  extend {T : Type}: struct_t T -> T -> struct_t T;
}.

Instance Prop_Set {T : Type} : TSet (T -> Prop) :=
{
  struct_t := fun X => X -> Prop;
  empty {T : Type} := fun _ => False;
  elem {T : Type} (A : T) (Γ : T -> Prop) := Γ A;
  union {T : Type} (Γ Δ : T -> Prop) := fun x : T => (Γ x) \/ (Δ x);
  extend {T : Type} (Γ : T -> Prop) (A : T) := fun B : T => or (Γ B) (A = B);
}.

Instance List_Set {T : Type} : TSet (list T) :=
{
  struct_t := list;
  empty {T : Type} := nil;
  elem {T : Type} (A : T) (lst : list T) := In A lst;
  union {T : Type} (l1 l2 : list T) := l1 ++ l2;
  extend {T : Type} (lst : list T) (A : T) := A :: lst;
}.

Definition subset {T : Type} `{Set_obj : TSet} (Γ Δ : Set_obj.(struct_t) T) :=
  forall A : T, (elem A Γ) -> (elem A Δ).

Definition set_eq {T : Type} `{Set_obj : TSet} (Γ Δ : Set_obj.(struct_t) T) :=
  forall x : T, (elem x Γ) <-> (elem x Δ).

(*   (* Δ is a proper extension of Γ *) *)
Definition proper_extension {T : Type} `{Set_obj : TSet} (Γ Δ : Set_obj.(struct_t) T) :=
  subset Γ Δ /\ ~ set_eq Γ Δ.

Declare Scope sets_scope.
Infix "∈" := elem (at level 77) : sets_scope.
Infix "∪" := union (at level 78, left associativity) : sets_scope.
Infix "⊆" := subset (at level 79) : sets_scope.
Notation "Γ ,, A" := (extend Γ A) (A ident, at level 32, left associativity).

Class TSet2 (T : Type) `{Set_obj : TSet T} :=
{
  subset_extend {Γ : Set_obj.(struct_t) T} {X : T}: subset Γ (extend Γ X);
}.

(* Множество Gamma является подмножеством (Gamma ,, A) *)
Lemma Prop_subset_extend {T : Type} (Γ : T -> Prop) (A : T) : @subset _ (T -> Prop) Prop_Set Γ (@extend (T -> Prop) _ _ Γ A).
Proof.
  unfold subset, extend.
  intros A0 H.
  simpl.
  unfold elem in H.
  simpl in H.
  left.
  exact H.
Qed.

Instance Prop_Set2 {T : Type} : TSet2 (T -> Prop) :=
{
  subset_extend := Prop_subset_extend;
}.

(* Список Gamma является подмножеством (Gamma ,, A) *)
Lemma List_subset_extend {T : Type} (lst : list T) (A : T) : @subset _ (list T) List_Set lst (@extend (list T) _ _ lst A).
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

Instance List_Set2 {T : Type} : TSet2 (list T) :=
{
  subset_extend := List_subset_extend;
}.
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
