From CoC Require Import CoC.
Import CoC_core.
Import CoC_theorems.

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
  {A : Type}
  {Eq : A -> A -> Prop}
  {op : A -> A -> A}
  {e : A}
  (M : Is_Monoid A Eq op e) : forall a : A, Eq (op e a) a :=
  let H_unit : Is_Unit A Eq op e := monoid_unit_proof A Eq op e M in
  conj_elim1 H_unit.

Definition monoid_id_right
  {A : Type}
  {Eq : A -> A -> Prop}
  {op : A -> A -> A}
  {e : A}
  (M : Is_Monoid A Eq op e) : forall a : A, Eq (op a e) a :=
  let H_unit : Is_Unit A Eq op e := monoid_unit_proof A Eq op e M in
  conj_elim2 H_unit.

Definition e_unique : forall {A : Type} {Eq : A -> A -> Prop} {op : A -> A -> A} {e : A} (Hm : Is_Monoid A Eq op e),
  forall e1 : A, Is_Unit A Eq op e1 -> Eq e e1 :=
  fun (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (Hm : Is_Monoid A Eq op e) (e1 : A) (e1_unit : Is_Unit A Eq op e1) =>
    let e1_id_left : forall a : A, Eq (op e1 a) a := conj_elim1 e1_unit in
    let e_id_right : forall a : A, Eq (op a e) a := monoid_id_right Hm in
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

(* Отображение $f : A \to B$ является гомоморфизмом моноидов, если выполняются **три** условия:

 1. **Сохранение эквивалентности (Морфизм сетоидов):
    ** Если элементы равны в $A$, их образы должны быть равны в $B$.
    $forall x y : A, Eq_A x y \to Eq_B (f x) (f y)$
 2. **Сохранение операции:** $forall x y : A, Eq_B (f (op_A x y)) (op_B (f x) (f y))$
 3. **Сохранение нейтрального элемента:** $Eq_B (f e_A) e_B$ *)

Definition Is_Monoid_Homomorphismus (A B : Type) (f : A -> B) (Eq_A : A -> A -> Prop) (op_A : A -> A -> A) (e_A : A) (Eq_B : B -> B -> Prop) (op_B : B -> B -> B) (e_B : B) (MA : Is_Monoid A Eq_A op_A e_A) (MB : Is_Monoid B Eq_B op_B e_B) : Prop :=
  ((forall a b : A, Eq_A a b -> Eq_B (f a) (f b)) /\ (forall a b : A, Eq_B (f (op_A a b)) (op_B (f a) (f b)))) /\ (Eq_B (f e_A) e_B).

Definition id_is_homomorphismus {A : Type} (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (Hm : Is_Monoid A Eq op e) : Is_Monoid_Homomorphismus A A (@id A) Eq op e Eq op e Hm Hm :=
  let Hsemi : Is_Semigroup A Eq op := @monoid_semigroup A Eq op e Hm in
  let Hsetoid : Is_Setoid A Eq := semigroup_setoid Hsemi in
  let eq_refl : forall x : A, Eq x x := setoid_refl Hsetoid in
  let eq_symm {x y : A} (H : Eq x y) : Eq y x := setoid_sym Hsetoid x y H in
  let eq_trans {x y z : A} (H1 : Eq x y) (H2 : Eq y z) : Eq x z := setoid_trans Hsetoid x y z H1 H2 in
  (* Сохранение эквивалентности *)
  let Goal1 : forall x y : A, Eq x y -> Eq (id x) (id y) :=
    fun (x y : A) (Heq : Eq x y) =>
      (Heq : Eq (id x) (id y))
  in
  (* Сохранение операции *)
  let Goal2 : forall a b : A, Eq (id (op a b)) (op (id a) (id b)) :=
    fun (a b : A) =>
      (eq_refl (op a b) : Eq (id (op a b)) (op (id a) (id b)))
  in
  (* Сохранение нейтрального элемента. *)
  let Goal3 : Eq (id e) e :=
    (eq_refl e : Eq (id e) e)
  in
  (* Собираем всё вместе *)
  conj_intro (conj_intro Goal1 Goal2) Goal3.

(* y является левым обратным для x *)
Definition Is_Left_Inverse {A : Type} (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (x y : A) : Prop :=
  Eq (op y x) e.

(* y является правым обратным для x *)
Definition Is_Right_Inverse {A : Type} (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (x y : A) : Prop :=
  Eq (op x y) e.

Definition left_right_inverse_equal {A : Type} (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) (x y z : A) (Hm : Is_Monoid A Eq op e) (Hleft : Is_Left_Inverse Eq op e x y) (Hright : Is_Right_Inverse Eq op e x z) : Eq y z :=
  (* Распаковываем предикаты из моноида *)
  let Hsemi : Is_Semigroup A Eq op := @monoid_semigroup A Eq op e Hm in
  let Hsetoid : Is_Setoid A Eq := semigroup_setoid Hsemi in
  let assoc : forall x y z : A, Eq (op (op x y) z) (op x (op y z)) := semigroup_assoc Hsemi in
  let congr2 : forall x1 x2 y1 y2 : A, Eq x1 x2 -> Eq y1 y2 -> Eq (op x1 y1) (op x2 y2) := semigroup_congruence_2 Hsemi in
  let eq_refl : forall x : A, Eq x x := setoid_refl Hsetoid in
  let eq_symm {x y : A} (H : Eq x y) : Eq y x := setoid_sym Hsetoid x y H in
  let eq_trans {x y z : A} (H1 : Eq x y) (H2 : Eq y z) : Eq x z := setoid_trans Hsetoid x y z H1 H2 in
  let id_left : forall a : A, Eq (op e a) a := monoid_id_left Hm in
  let id_right : forall a : A, Eq (op a e) a := monoid_id_right Hm in
  let Hyx : Eq (op y x) e := Hleft in
  let Hxz : Eq (op x z) e := Hright in
  (* Конструируем левую часть y = ... *)
  let H1 : Eq (op y e) y := id_right y in
  let H2 : Eq y (op y e) := eq_symm H1 in
  let H3 : Eq (op y (op x z)) (op (op y e) e) := congr2 y (op y e) (op x z) e  H2 Hxz in
  let H4 : Eq (op (op y e) e) (op y e) := id_right (op y e) in
  let H5 : Eq (op y (op x z)) (op y e) := eq_trans H3 H4 in
  let H6 : Eq (op (op y x) z) (op y (op x z)) := assoc y x z in
  let H7 : Eq (op (op y x) z) (op y e) := eq_trans H6 H5 in
  let H8 : Eq (op (op y x) z) y := eq_trans H7 H1 in
  let H_left : Eq y (op (op y x) z) := eq_symm H8 in
  (* Правая часть (y * x) * z = z *)
  let H9 : Eq (op e z) z := id_left z in
  let H10 : Eq z (op e z) := eq_symm H9 in
  let H11 : Eq (op (op y x) z) (op e (op e z)) := congr2 (op y x) e z (op e z) Hyx H10 in
  let H12 : Eq (op e (op e z)) (op e z) := id_left (op e z) in
  let H13 : Eq (op (op y x) z) (op e z) := eq_trans H11 H12 in
  let H_right : Eq (op (op y x) z) z := eq_trans H13 H9 in
  eq_trans H_left H_right.
