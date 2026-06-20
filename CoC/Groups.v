From CoC Require Import CoC.
Import CoC.

Definition Is_Setoid (A : Type) (Eq : A -> A -> Prop) : Prop :=
  forall P : Prop,
  ( (* Конструктор ожидает получить три доказательства: *)
    (forall x : A, Eq x x) ->                             (* Refl *)
    (forall x y : A, Eq x y -> Eq y x) ->                 (* Sym *)
    (forall x y z : A, Eq x y -> Eq y z -> Eq x z) ->     (* Trans *)
    P
  ) -> P.

(* 2. Функция сборки (Конструктор) *)
Definition Build_Setoid : forall (A : Type) (Eq : A -> A -> Prop) (Refl : forall x : A, Eq x x) (Sym : forall x y : A, Eq x y -> Eq y x) (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z), Is_Setoid A Eq :=
  fun (A : Type)
    (Eq : A -> A -> Prop)
    (Refl : forall x : A, Eq x x)
    (Sym : forall x y : A, Eq x y -> Eq y x)
    (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z)
    (P : Prop)
    (Constructor : (forall x : A, Eq x x) -> (forall x y : A, Eq x y -> Eq y x) -> (forall x y z : A, Eq x y -> Eq y z -> Eq x z) -> P) =>
    Constructor Refl Sym Trans.

Definition setoid_refl
  (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : forall x : A, Eq x x :=
  S (forall x : A, Eq x x)
    (fun (Refl : forall x : A, Eq x x) Sym Trans => Refl).

Definition setoid_sym
  (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : forall x y : A, Eq x y -> Eq y x :=
  S (forall x y : A, Eq x y -> Eq y x)
    (fun Refl (Sym : forall x y : A, Eq x y -> Eq y x) Trans => Sym).

Definition setoid_trans
  (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : forall x y z : A, Eq x y -> Eq y z -> Eq x z :=
  S (forall x y z : A, Eq x y -> Eq y z -> Eq x z)
    (fun Refl Sym (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z) => Trans).

(* Отношение эквивалентности разбивает исходное множество на непересекающиеся подмножества - классы эквивалентности. Множество классов эквивалентности для данного множества - это фактормножество *)
Definition equivalence_class (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : A -> A -> Prop := fun a b : A => Eq a b.

Definition FactorSet (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : (C : equivalence_class A Eq S) -> Prop := fun (C : equivalence_class A Eq S)

Definition setoid_eq_congr (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) :
  forall (f : A -> A) {x y : A}, Eq x y -> Eq (f x) (f y) :=
  fun (f : A -> A) (x y : A) (Heq : Eq x y) =>
    _.

  
  fun (P : B -> Prop) (Pfx : P (f x)) =>
    Heq (fun z : A => P (f z)) Pfx.

