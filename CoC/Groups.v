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

Definition Build_Setoid : forall (A : Type) (Eq : A -> A -> Prop) (Refl : forall x : A, Eq x x) (Sym : forall x y : A, Eq x y -> Eq y x) (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z), Is_Setoid A Eq :=
  fun (A : Type)
    (Eq : A -> A -> Prop)
    (Refl : forall x : A, Eq x x)
    (Sym : forall x y : A, Eq x y -> Eq y x)
    (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z)
    (P : Prop)
    (Constructor : (forall x : A, Eq x x) -> (forall x y : A, Eq x y -> Eq y x) -> (forall x y z : A, Eq x y -> Eq y z -> Eq x z) -> P) =>
    Constructor Refl Sym Trans.

Definition setoid_refl {A : Type} {Eq : A -> A -> Prop} (S : Is_Setoid A Eq) : forall x : A, Eq x x :=
  S (forall x : A, Eq x x)
    (fun (Refl : forall x : A, Eq x x) Sym Trans => Refl).

Definition setoid_sym
  {A : Type} {Eq : A -> A -> Prop} (S : Is_Setoid A Eq) : forall x y : A, Eq x y -> Eq y x :=
  S (forall x y : A, Eq x y -> Eq y x)
    (fun Refl (Sym : forall x y : A, Eq x y -> Eq y x) Trans => Sym).

Definition setoid_trans
  {A : Type} {Eq : A -> A -> Prop} (S : Is_Setoid A Eq) : forall x y z : A, Eq x y -> Eq y z -> Eq x z :=
  S (forall x y z : A, Eq x y -> Eq y z -> Eq x z)
    (fun Refl Sym (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z) => Trans).

(* Отношение эквивалентности разбивает исходное множество на непересекающиеся подмножества - классы эквивалентности. Множество классов эквивалентности для данного множества - это фактормножество *)
Definition equivalence_class (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : A -> A -> Prop := fun a b : A => Eq a b.

(* Definition is_equivalence_class {A : Type} (Eq : A -> A -> Prop) (C : A -> Prop) : Prop := *)
(*   exists a : A, forall b : A, C b <-> Eq a b. *)

(* Definition FactorSet (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : Type := *)
(*   { C : A -> Prop | is_equivalence_class Eq C }. *)

(* Definition FactorSet (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : (C : equivalence_class A Eq S) -> Prop := fun (C : equivalence_class A Eq S) *)

(* Definition setoid_eq_congr (A : Type) (Eq : A -> A -> Prop) (S : Is_Setoid A Eq) : *)
(*   forall (f : A -> A) {x y : A}, Eq x y -> Eq (f x) (f y) := *)
(*   fun (f : A -> A) (x y : A) (Heq : Eq x y) => *)
(*     _. *)

(* Предикат 1: Операция сохраняет отношение эквивалентности *)
Definition Is_Congruence_2
  (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) : Prop :=
  forall x1 x2 y1 y2 : A, Eq x1 x2 -> Eq y1 y2 -> Eq (op x1 y1) (op x2 y2).

Definition Is_Associative
  (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) : Prop :=
  forall x y z : A, Eq (op (op x y) z) (op x (op y z)).

Definition Is_Semigroup (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) : Prop :=
  forall P : Prop,
  (
    Is_Setoid A Eq ->
    Is_Congruence_2 A Eq op ->
    Is_Associative A Eq op ->
    P
  ) -> P.

Definition Build_Semigroup (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (Hsetoid : Is_Setoid A Eq) (Hcongr : Is_Congruence_2 A Eq op) (Hassoc : Is_Associative A Eq op) : Is_Semigroup A Eq op :=
  fun (P : Prop) (Constructor : Is_Setoid A Eq -> Is_Congruence_2 A Eq op -> Is_Associative A Eq op -> P) => Constructor Hsetoid Hcongr Hassoc.

Definition semigroup_setoid {A : Type} {Eq : A -> A -> Prop} {op : A -> A -> A} (Hs : Is_Semigroup A Eq op) : Is_Setoid A Eq :=
  Hs (Is_Setoid A Eq) (fun (S : Is_Setoid A Eq) _ _ => S).

Definition semigroup_congruence_2 {A : Type} {Eq : A -> A -> Prop} {op : A -> A -> A} (Hs : Is_Semigroup A Eq op) : Is_Congruence_2 A Eq op :=
  Hs (Is_Congruence_2 A Eq op) (fun _ (congr : Is_Congruence_2 A Eq op) _ => congr).

Definition semigroup_assoc {A : Type} {Eq : A -> A -> Prop} {op : A -> A -> A} (Hs : Is_Semigroup A Eq op) : Is_Associative A Eq op :=
  Hs (Is_Associative A Eq op) (fun _ _ (assoc : Is_Associative A Eq op) => assoc).

Definition Is_Unit (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) : Prop :=
  (forall a : A, Eq (op e a) a) /\
  (forall a : A, Eq (op a e) a).

Definition Is_Monoid
  (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) : Prop :=
  forall P : Prop,
  ( Is_Semigroup A Eq op ->
    Is_Unit A Eq op e ->
    P
  ) -> P.

Definition Build_Monoid (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (Hsemi : Is_Semigroup A Eq op) (Hunit : Is_Unit A Eq op e) : Is_Monoid A Eq op e :=
  fun (P : Prop) (Constructor : Is_Semigroup A Eq op -> Is_Unit A Eq op e -> P) => Constructor Hsemi Hunit.

Definition monoid_semigroup {A : Type} {Eq : A -> A -> Prop} {op : A -> A -> A} (e : A) (Hm : Is_Monoid A Eq op e) : Is_Semigroup A Eq op :=
  Hm (Is_Semigroup A Eq op) (fun (semi : Is_Semigroup A Eq op) _ => semi).


Definition monoid_unit_proof (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (Hm : Is_Monoid A Eq op e) : Is_Unit A Eq op e :=
  Hm (Is_Unit A Eq op e)
    (fun _ (H_unit : Is_Unit A Eq op e) => H_unit).

Definition monoid_id_left
  (A : Type)
  (Eq : A -> A -> Prop)
  (op : A -> A -> A)
  (e : A)
  (M : Is_Monoid A Eq op e) : forall a : A, Eq (op e a) a :=
  let H_unit : Is_Unit A Eq op e := monoid_unit_proof A Eq op e M in
  and_elim1 H_unit.

Definition monoid_id_right
  (A : Type)
  (Eq : A -> A -> Prop)
  (op : A -> A -> A)
  (e : A)
  (M : Is_Monoid A Eq op e) : forall a : A, Eq (op a e) a :=
  let H_unit : Is_Unit A Eq op e := monoid_unit_proof A Eq op e M in
  and_elim2 H_unit.

Definition e_unique : forall {A : Type} {Eq : A -> A -> Prop} {op : A -> A -> A} {e : A} (Hm : Is_Monoid A Eq op e),
  forall e1 : A, Is_Unit A Eq op e1 -> Eq e e1 :=
  fun (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (Hm : Is_Monoid A Eq op e) (e1 : A) (e1_unit : Is_Unit A Eq op e1) =>
    let e1_id_left : forall a : A, Eq (op e1 a) a := and_elim1 e1_unit in
    let e_id_right : forall a : A, Eq (op a e) a := monoid_id_right A Eq op e Hm in
    let e1_e : Eq (op e1 e) e := e1_id_left e in
    let e_e1 : Eq (op e1 e) e1 := e_id_right e1 in
    let Hsemi : Is_Semigroup A Eq op := @monoid_semigroup A Eq op e Hm in
    let Hsetoid : Is_Setoid A Eq := semigroup_setoid Hsemi in
    (* Wrapper assignments to force implicit variable resolution *)
    let eq_symm {x y : A} (H : Eq x y) : Eq y x := setoid_sym Hsetoid x y H in
    let eq_trans {x y z : A} (H1 : Eq x y) (H2 : Eq y z) : Eq x z := setoid_trans Hsetoid x y z H1 H2 in

    let H1 : Eq e (op e1 e) := eq_symm e1_e in
    let H2 : Eq e e1 := eq_trans H1 e_e1 in
    H2.
