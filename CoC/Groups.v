From CoC Require Import CoC.
Import CoC.

Definition Is_Setoid (A : Type) : Type :=
  forall P : Type,
  (forall Eq : A -> A -> Prop,
     (forall x : A, Eq x x) ->
     (forall x y : A, Eq x y -> Eq y x) ->
     (forall x y z : A, Eq x y -> Eq y z -> Eq x z) ->
     P) -> P.

Definition Build_Setoid : forall (A : Type) (Eq : A -> A -> Prop) (Refl : forall x : A, Eq x x) (Sym : forall x y : A, Eq x y -> Eq y x) (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z), Is_Setoid A :=
  fun (A : Type)
    (Eq : A -> A -> Prop)
    (Refl : forall x : A, Eq x x)
    (Sym : forall x y : A, Eq x y -> Eq y x)
    (Trans : forall x y z : A, Eq x y -> Eq y z -> Eq x z) =>
  fun (T : Type)
    (f : forall Eq : A -> A -> Prop,
             (forall x : A, Eq x x) ->
             (forall x y : A, Eq x y -> Eq y x) ->
             (forall x y z : A, Eq x y -> Eq y z -> Eq x z) ->
             T) =>
       f Eq Refl Sym Trans.

Definition setoid_destruct
  (A : Type)
  (S : Is_Setoid A)
  (T : Type)
  (k :
     forall Eq,
     (forall x, Eq x x) ->
     (forall x y, Eq x y -> Eq y x) ->
     (forall x y z, Eq x y -> Eq y z -> Eq x z) ->
     T)
  : T :=
  S T k.

Definition setoid_Eq
  (A : Type)
  (S : Is_Setoid A)
  : A -> A -> Prop :=
  setoid_destruct A S
    (A -> A -> Prop)
    (fun Eq _ _ _ => Eq).

Definition setoid_refl
  (A : Type)
  (S : Is_Setoid A)
  : { Eq : A -> A -> Prop &
      forall x : A, Eq x x } :=
  setoid_destruct A S
    _
    (fun Eq refl _ _ =>
       existT _ Eq refl).

(* Definition Is_Setoid (A : Type) (Eq : A -> A -> Prop) : Prop := *)
(*   forall P : Prop, *)
(*   ( (* Конструктор ожидает получить три доказательства: *) *)
(*     (forall x : A, Eq x x) ->                             (* Refl *) *)
(*     (forall x y : A, Eq x y -> Eq y x) ->                 (* Sym *) *)
(*     (forall x y z : A, Eq x y -> Eq y z -> Eq x z) ->     (* Trans *) *)
(*     P *)
(*   ) -> P. *)

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

(* Definition exists : forall (A : Type) (B : A -> Prop), Prop := *)
(*   fun (A : Type) (B : A -> Prop) => forall (C : Prop), (forall x : A, B x -> C) -> C. *)

Definition Is_Unit (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (e : A) : Prop :=
  (forall a : A, Eq (op e a) a) /\
  (forall a : A, Eq (op a e) a).

Definition Is_Monoid (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) : Type :=
  forall P : Type,
  (
    (Is_Semigroup A Eq op) ->
    (exists A (Is_Unit A Eq op)) ->
    P
  ) -> P.

Definition M_e
  (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A)
  (M : Is_Monoid A Eq op)
  : A :=
  M
    (fun _ => A)
    (fun _ Hsem Hk =>
        Hk
          (fun e _ _ => e)
    ).

Definition M_e : forall (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (Hm : Is_Monoid A Eq op), A :=
  fun (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (Hm : Is_Monoid A Eq op) =>
    Hm (forall x : A, x) _.

Definition e_unique : forall (A : Type) (Eq : A -> A -> Prop) (op : A -> A -> A) (Hm : Is_Monoid A Eq op), forall e1 : A, 
