From CoC Require Import CoC.
Import CoC.

Parameter nat : Type.
(* 0 есть натуральное число *)
Parameter O : nat.
(* Для любого натурального числа n существует другое натуральное число (S n), называемое
     непосредственно следующим за n  *)
Parameter S : nat -> nat.

Notation "'0'" := O.

Axiom S_not_O : forall n : nat, ~ (0 = (S n)).
Arguments S_not_O {_} _.
(* S инъективна *)
Axiom S_inj : forall x y : nat, (S x) = (S y) -> x = y.
Arguments S_inj {_} {_} _.
(* Принцип индукции *)
Axiom N_ind : forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n.

Parameter add : nat -> nat -> nat.
Parameter mul : nat -> nat -> nat.

Notation "x + y" := (add x y) (at level 50, left associativity).
Notation "x * y" := (mul x y) (at level 40, left associativity).

Axiom add_0_right : forall n : nat,  n + 0 = n.
Axiom add_S_right : forall n m : nat, n + (S m) = S (n + m).
Axiom mul_0_right : forall n : nat, n * O = O.
Axiom mul_S_right : forall n m : nat, n * (S m) = (n * m) + n.

(* Теоремы про сложение *)

Definition add_0_left : forall n : nat, 0 + n = n :=
  fun (n : nat) =>
    let Base : 0 + 0 = 0 := add_0_right 0 in
    let Step : forall n : nat, 0 + n = n -> 0 + S n = S n :=
      (fun (n : nat) (IH : 0 + n = n) =>
         let H1 : 0 + (S n) = S (0 + n) := add_S_right O n in
         let H2 : S (0 + n) = S n := eq_congr S IH in
         let H3 : 0 + S n = S n := eq_trans H1 H2 in
         H3)
    in
    N_ind (fun n : nat => 0 + n = n) Base Step n.

Definition add_S_left : forall x y : nat, S x + y = S (x + y) :=
  fun x =>
    let Base : S x + 0 = S (x + 0) :=
      let H1 : x + 0 = x := add_0_right x in
      let Heq2 : S (x + 0) = S x := eq_congr S H1 in
      let Heq3 : S x = S (x + 0) := eq_symm Heq2 in
      let Heq4 : S x + 0 = S x := add_0_right (S x) in
      let Heq5 : S x + 0 = S (x + 0) := eq_trans Heq4 Heq3 in
      Heq5
    in
    let Step : forall n, (S x + n = S (x + n)) -> (S x + S n = S (x + S n)) :=
      fun (n : nat) (IH : S x + n = S (x + n)) =>
        let H1 : S x + S n = S (S x + n) := add_S_right (S x) n in
        let H2 : S (S x + n) = S (S (x + n)) := eq_congr S IH in
        let H3 : S x + S n = S (S (x + n)) := eq_trans H1 H2 in
        let H4 : x + S n = S (x + n) := add_S_right x n in
        let H5 : S (x + n) = x + S n := eq_symm H4 in
        let H6 : S (S (x + n)) = S (x + S n) := eq_congr S H5 in
        let H7 : S x + S n = S (x + S n) := eq_trans H3 H6 in
        H7
    in
    N_ind
      (fun y : nat => S x + y = S (x + y))
      Base
      Step.

Definition add_comm : forall x y : nat, x + y = y + x :=
  fun x =>
    let Base : x + 0 = 0 + x :=
      let H1 : x + 0 = x := add_0_right x in
      let H2 : 0 + x = x := add_0_left x in
      let H3 : x = 0 + x := eq_symm H2 in
      let H4 : x + 0 = 0 + x := eq_trans H1 H3 in
      H4
    in
    let Step :=
      fun (n : nat) (IH : x + n = n + x) =>
        let H1 : x + S n = S (x + n) := add_S_right x n in
        let H2 : S n + x = S (n + x) := add_S_left n x in
        let H3 : S (n + x) = S n + x := eq_symm H2 in
        let H4 : S (x + n) = S (n + x) := eq_congr S IH in
        let H5 : x + S n = S (n + x) := eq_trans H1 H4 in
        let H6 : x + S n = S n + x := eq_trans H5 H3 in
        H6
    in
    N_ind
      (fun y : nat => x + y = y + x)
      Base
      Step.

Definition add_assoc : forall x y z : nat, (x + y) + z = x + (y + z) :=
  let Base : forall y z : nat, 0 + y + z = 0 + (y + z) :=
    fun y z : nat =>
      let H1 : 0 + y = y := add_0_left y in
      let H2 : (0 + y) + z = y + z := eq_congr (fun n : nat => n + z) H1 in
      let H3 : 0 + (y + z) = y + z := add_0_left (y + z) in
      let H4 : y + z = 0 + (y + z) := eq_symm H3 in
      let H5 : (0 + y) + z = 0 + (y + z) := eq_trans H2 H4 in
      H5
  in
  let Step : forall n : nat,
      (forall y z : nat, (n + y) + z = n + (y + z)) ->
      (forall y z : nat, (S n + y) + z = S n + (y + z))
    :=
    fun (n : nat) (IH : forall y z : nat, (n + y) + z = n + (y + z)) =>
    fun (y z : nat) =>
      let H1 : S n + y = S (n + y) := add_S_left n y in
      let H2 : (S n + y) + z = S (n + y) + z := eq_congr (fun n : nat => n + z) H1 in
      let H3 : S n + (y + z) = S (n + (y + z)) := add_S_left n (y + z) in
      let H4 : S (n + (y + z)) = S n + (y + z) := eq_symm H3 in
      let H5 : (n + y) + z = n + (y + z) := IH y z in
      let H6 : S ((n + y) + z) = S (n + (y + z)) := eq_congr S H5 in
      let H7 : S (n + y + z) = S n + (y + z) := eq_trans H6 H4 in
      let H8 : S (n + y) + z = S ((n + y) + z) := add_S_left (n + y) z in
      let H9 : S (n + y) + z = S n + (y + z) := eq_trans H8 H7 in
      let H10 : S n + y + z = S n + (y + z) := eq_trans H2 H9 in
      H10
  in
  N_ind
    (fun x : nat => forall y z : nat, (x + y) + z = x + (y + z))
    Base
    Step.

Definition add_cancel_right : forall a b c : nat, a + c = b + c -> a = b :=
  fun a b : nat =>
    let P : nat -> Prop :=
      fun k : nat => a + k = b + k -> a = b
    in
    let Base : P 0 :=
      fun (H0 : a + 0 = b + 0) =>
        let H1 : a + 0 = a := add_0_right a in
        let H2 : a = a + 0 := eq_symm H1 in
        let H3 : a = b + 0 := eq_trans H2 H0 in
        let H4 : b + 0 = b := add_0_right b in
        let H5 : a = b := eq_trans H3 H4 in
        H5
    in
    let Step : forall n, P n -> P (S n) :=
      fun (n : nat) (IH : a + n = b + n -> a = b) =>
      fun (H0 : a + S n = b + S n) =>
        let H1 : a + S n = S (a + n) := add_S_right a n in
        let H2 : S (a + n) = a + S n := eq_symm H1 in
        let H3 : S (a + n) = b + S n := eq_trans H2 H0 in
        let H4 : b + S n = S (b + n) := add_S_right b n in
        let H5 : S (a + n) = S (b + n) := eq_trans H3 H4 in
        let H6 : a + n = b + n := S_inj H5 in
        let H7 : a = b := IH H6 in
        H7
    in
    N_ind P Base Step.

Arguments add_cancel_right {_} {_} {_} _.

Definition add_right_eq_self : forall a n : nat, a + n = a -> n = 0 :=
  fun a n : nat =>
    let P : nat -> Prop :=
      fun x : nat => x + n = x -> n = 0
    in
    let Base : 0 + n = 0 -> n = 0 :=
      fun (H0 : 0 + n = 0) =>
        let H1 : 0 + n = n := add_0_left n in
        let H2 : n = 0 + n := eq_symm H1 in
        let H3 : n = 0 := eq_trans H2 H0 in
        H3
    in
    let Step : forall x : nat, P x -> P (S x) :=
      fun (x : nat) (IH : x + n = x -> n = 0) =>
      fun (H0 : S x + n = S x) =>
        let H1 : S x + n = S (x + n) := add_S_left x n in
        let H2 : S (x + n) = S x + n := eq_symm H1 in
        let H3 : S (x + n) = S x := eq_trans H2 H0 in
        let H4 : x + n = x := S_inj H3 in
        let H5 : n = 0 := IH H4 in
       H5
    in
    N_ind P Base Step a.

Arguments add_right_eq_self {_} {_} _.

Definition n_k_eq_0 : forall n k : nat, n + k = 0 -> (n = 0) /\ (k = 0) :=
  fun (n : nat) =>
    (* 1. Выносим предикат индукции в отдельную переменную *)
    let P : nat -> Prop :=
      fun k : nat => n + k = 0 -> n = 0 /\ k = 0
    in
    (* База остается вашей, мы лишь указываем более чистый тип P 0 *)
    let Base : P 0 :=
      fun (H0 : n + 0 = 0) =>
        let H1 : n + 0 = n := add_0_right n in
        let H2 : n = 0 := eq_trans (eq_symm H1) H0 in
        let H3 : 0 = 0 := eq_refl 0 in
        and_intro H2 H3
    in
    (* 2. Шаг индукции с бета-редуцированным типом *)
    let Step : forall k : nat, P k -> P (S k) :=
      fun (k : nat) (IH : n + k = 0 -> n = 0 /\ k = 0) (Contra : n + (S k) = 0) =>
        let H1 : n + (S k) = S (n + k) := add_S_right n k in
        let H2 : S (n + k) = 0 := eq_trans (eq_symm H1) Contra in
        let H3 : False := S_not_O (eq_symm H2) in
        H3 (n = 0 /\ S k = 0)
    in
    N_ind (fun k : nat => n + k = 0 -> and (n = 0) (k = 0))
      Base
      Step.

Arguments n_k_eq_0 {_} {_} _.

Definition a_plus_S0 : forall a : nat, a + S 0 = S a :=
  fun a : nat =>
    let H1 : a + S 0 = S (a + 0) := add_S_right a 0 in
    let H2 : a + 0 = a := add_0_right a in
    let H3 : S (a + 0) = S a := eq_congr S H2 in
    let H4 : a + S 0 = S a := eq_trans H1 H3 in
    H4.

Definition S0_plus_a : forall a : nat, S 0 + a = S a :=
  fun a : nat =>
    let H1 : S 0 + a = S (0 + a) := add_S_left 0 a in
    let H2 : 0 + a = a := add_0_left a in
    let H3 : S (0 + a) = S a := eq_congr S H2 in
    let H4 : S 0 + a = S a := eq_trans H1 H3 in
    H4.

(* Теоремы про умножение *)

Definition mul_0_left : forall x : nat, 0 * x = 0 :=
  let Base : 0 * 0 = 0 := mul_0_right 0 in
  let Step : forall n : nat, 0 * n = 0 -> 0 * S n = 0 :=
    fun (n : nat) (IH : 0 * n = 0) =>
      let H1 : 0 * S n = 0 * n + 0 := mul_S_right 0 n in
      let H2 : 0 * n + 0 = 0 * n := add_0_right (0 * n) in
      let H3 : 0 * S n = 0 * n := eq_trans H1 H2 in
      let H4 : 0 * S n = 0 := eq_trans H3 IH in
      H4
  in
  N_ind (fun n : nat => 0 * n = 0) Base Step.

Definition mul_S0_right : forall a : nat, a * (S 0) = a :=
  let Base : 0 * (S 0) = 0 := mul_0_left (S 0) in
  let Step : forall n : nat, n * (S 0) = n -> (S n) * (S 0) = (S n) :=
    fun (n : nat) (IH : n * (S 0) = n) =>
      let H1 : S n * (S 0) = (S n) * 0 + S n := mul_S_right (S n) 0 in
      let H2 : (S n) * 0 = 0 := mul_0_right (S n) in
      let H3 : (S n) * 0 + (S n) = 0 + (S n) := eq_congr (fun k => k + S n) H2 in
      let H4 : (S n) * (S 0) = 0 + (S n) := eq_trans H1 H3 in
      let H5 : 0 + (S n) = S n := add_0_left (S n) in
      let H6 : (S n) * (S 0) = (S n) := eq_trans H4 H5 in
      H6 in
  N_ind (fun n : nat => n * (S 0) = n) Base Step.

Definition add_2equalities : forall a b c d : nat, a = c -> b = d -> a + b = c + d :=
  fun (a b c d : nat) (H1 : a = c) (H2 : b = d) =>
    let H3 : a + b = c + b := eq_congr (fun p : nat => p + b) H1 in
    let H4 : c + b = c + d := eq_congr (fun p : nat => c + p) H2 in
    let H5 : a + b = c + d := eq_trans H3 H4 in
    H5.

Arguments add_2equalities {_} {_} {_} {_} _ _.

Definition distributivity_left : forall a b c : nat, a * (b + c) = a*b + a*c :=
  fun (a b : nat) =>
    let Base : a * (b + 0) = a*b + a*0 :=
      let H1 : b + 0 = b := add_0_right b in
      let H2 : a * (b + 0) = a * b := eq_congr (fun n => a * n) H1 in
      let H3 : a * 0 = 0 := mul_0_right a in
      let H4 : a * b + a * 0 = a * b + 0 := eq_congr (fun n => a * b + n) H3 in
      let H5 : a * b + 0 = a * b := add_0_right (a * b) in
      let H6 : a * b + a * 0 = a * b := eq_trans H4 H5 in
      let H7 : a * (b + 0) = a * b + a * 0 := eq_trans H2 (eq_symm H6) in
      H7
    in
    let Step : forall n : nat,
        (a * (b + n) = a * b + a * n) ->
        (a * (b + S n) = a * b + a * (S n)) :=
      fun (n : nat) (IH : a * (b + n) = a*b + a*n) =>
        let H1 : b + S n = S (b + n) := add_S_right b n in
        let H2 : a * (b + S n) = a * S (b + n) := eq_congr (fun n : nat => a * n) H1 in
        let H3 : a * S (b + n) = a * (b + n) + a := mul_S_right a (b + n) in
        let H4 : a * (b + n) + a = (a * b + a * n) + a := eq_congr (fun n : nat => n + a) IH in
        let H5 : a * S n = a * n + a := mul_S_right a n in
        let H6 : a * b + a * S n = a * b + (a * n + a) := eq_congr (fun n => a * b + n) H5 in
        let H7 : (a * b + a * n) + a = a * b + (a * n + a) := add_assoc (a * b) (a * n) a in
        let H8 : a * b + (a * n + a) = (a * b + a * n) + a := eq_symm H7 in
        let H9 : a * b + a * S n = (a * b + a * n) + a := eq_trans H6 H8 in
        let H10 : (a * b + a * n) + a = a * b + a * S n := eq_symm H9 in
        let H11 : a * (b + S n) = a * (b + n) + a := eq_trans H2 H3 in
        let H12 : a * (b + S n) = (a * b + a * n) + a := eq_trans H11 H4 in
        let H13 : a * (b + S n) = a * b + a * S n := eq_trans H12 H10 in
        H13
    in
    N_ind (fun n : nat => a * (b + n) = a*b + a* n)
      Base
      Step.

Definition eq_mul_eq : forall a b c : nat, a = b -> a * c = b * c :=
  fun (a b c : nat) (Heq : a = b) =>
    (* Выносим предикат индукции в отдельную переменную *)
    let P : nat -> Prop :=
      fun n : nat => a * n = b * n
    in
    let Base : P 0 :=
      let H1 : a * 0 = 0 := mul_0_right a in
      let H2 : b * 0 = 0 := mul_0_right b in
      let H3 : 0 = b * 0 := eq_symm H2 in
      let H4 : a * 0 = b * 0 := eq_trans H1 H3 in
      H4
    in
    let Step : forall n : nat, P n -> P (S n) :=
      fun (n : nat) (IH : P n) =>
        (* Раскрыли определение P *)
        let IH1 : a * n = b * n := IH in
        let H1 : a * S n = a * n + a := mul_S_right a n in
        let H2 : b * S n = b * n + b := mul_S_right b n in
        let H3 : a * n + a = b * n + a := eq_congr (fun k : nat => k + a) IH1 in
        let H4 : b * n + a = b * n + b := eq_congr (fun k : nat => b * n + k) Heq in
        let H5 : a * n + a = b * n + b := eq_trans H3 H4 in
        let H6 : a * S n = b * n + b := eq_trans H1 H5 in
        let H7 : b * n + b = b * S n := eq_symm H2 in
        let H8 : a * S n = b * S n := eq_trans H6 H7 in
        H8
    in
    N_ind (fun n : nat => P n) Base Step c.

Arguments eq_mul_eq {_} {_} _ _.

Definition mul_S_left : forall a b : nat, (S a) * b = b + a * b :=
  fun a : nat =>
    let Base : (S a) * 0 = 0 + a * 0 :=
      let H1 : (S a) * 0 = 0 := mul_0_right (S a) in
      let H2 : a * 0 = 0 := mul_0_right a in
      let H3 : 0 + a * 0 = a * 0 := add_0_left (a * 0) in
      let H4 : 0 + a * 0 = 0 := eq_trans H3 H2 in
      let H5 : (S a) * 0 = 0 + a * 0 := eq_trans H1 (eq_symm H4) in
      H5
    in
    let Step : forall n : nat,
        ((S a) * n = n + a * n) ->
        ((S a) * (S n) = (S n) + a * (S n)) :=
      fun (n : nat) (IH : (S a) * n = n + a * n) =>
        let H1 : (S a) * (S n) = (S a) * n + S a := mul_S_right (S a) n in
        let H2 : (S a) * n + S a = (n + a * n) + S a := eq_congr (fun n : nat => n + S a) IH in
        let H3 : a * (S n) = a * n + a := mul_S_right a n in
        let H4 : S n + a * (S n) = S n + (a * n + a) := eq_congr (fun k : nat => S n + k) H3 in
        let H5 : (n + a * n) + S a = S (n + a * n + a) := add_S_right (n + a * n) a in
        let H6 : S n + (a * n + a) = S (n + (a * n + a)) := add_S_left n (a * n + a) in
        let H7 : S n + a * (S n) = S (n + (a * n + a)) := eq_trans H4 H6 in
        let H8 : (S a) * (S n) = (n + a * n) + S a := eq_trans H1 H2 in
        let H9 : (S a) * (S n) = S (n + a * n + a) := eq_trans H8 H5 in
        let H10 : (n + a * n) + a = n + (a * n + a) := add_assoc n (a * n) a in
        let H11 : S ((n + a * n) + a) = S (n + (a * n + a)) := eq_congr S H10 in
        let H12 : (S a) * (S n) = S (n + (a * n + a)) := eq_trans H9 H11 in
        let H13 : (S a) * (S n) = S n + a * (S n) := eq_trans H12 (eq_symm H7) in
        H13
    in
    N_ind (fun n : nat => (S a) * n = n + a * n) Base Step.

Definition distributivity_right : forall a b c : nat, (a + b) * c = a * c + b * c :=
  fun (a b c : nat) =>
    let P : nat -> Prop :=
      fun n : nat => (a + n) * c = a * c + n * c
    in
    (* Доказать (a + 0) * c = a * c + 0 * c *)
    let Base : P 0 :=
      let Goal : (a + 0) * c = a * c + 0 * c :=
        (* Левая часть: (a + 0) * c = a * c *)
        let H1 : a + 0 = a := add_0_right a in
        let H_left : (a + 0) * c = a * c := eq_congr (fun p : nat => p * c) H1 in
        (* Правая часть: a * c = a * c + 0 * c *)
        let H2 : 0 * c = 0 := mul_0_left c in
        let H3 : a * c + 0 * c = a * c + 0 := eq_congr (fun p : nat => a * c + p) H2 in
        let H4 : a * c + 0 = a * c := add_0_right (a * c) in
        let H5 : a * c + 0 * c = a * c := eq_trans H3 H4 in
        let H_right : a * c = a * c + 0 * c := eq_symm H5 in
        eq_trans H_left H_right
      in Goal
    in
    let Step : forall n : nat, P n -> P (S n) :=
      fun (n : nat) (IH : P n) =>
        let Goal : (a + S n) * c = a * c + S n * c :=
          (* Правая часть: ... = a * c + S n * c *)
          let H1 : S n * c = c + n * c := mul_S_left n c in
          let H2 : c + n * c = n * c + c := add_comm c (n * c) in
          let H3 : S n * c = n * c + c := eq_trans H1 H2 in
          let H4 : a * c + S n * c = a * c + (n * c + c) := eq_congr (fun p : nat => a * c + p) H3 in
          let H5 : a * c + (n * c + c) = a * c + S n * c := eq_symm H4 in
          (* Преобразование правой части для получения удобной формулы для транзитивности *)
          let H6 : (a * c + n * c) + c = a * c + (n * c + c) := add_assoc (a * c) (n * c) c in
          let H7 : (a * c + n * c) + c = a * c + S n * c := eq_trans H6 H5 in
          let H8 : (a + n) * c + c = (a * c + n * c) + c := eq_congr (fun p : nat => p + c) IH in
          let H9 : (a + n) * c + c = a * c + S n * c := eq_trans H8 H7 in
          (* Левая часть: (a + S n) * c = (a + n) * c + c *)
          let H10 : a + S n = S (a + n) := add_S_right a n in
          let H11 : S (a + n) * c = c + (a + n) * c := mul_S_left (a + n) c in
          let H12 : (a + S n) * c = S (a + n) * c := eq_congr (fun p : nat => p * c) H10 in
          (* Мы получили левую часть Step *)
          let H13 : (a + S n) * c = c + (a + n) * c := eq_trans H12 H11 in
          let H14 : c + (a + n) * c = (a + n) * c + c := add_comm c ((a + n)  * c) in
          let H15 : (a + S n) * c = (a + n) * c + c := eq_trans H13 H14 in
          eq_trans H15 H9
        in Goal
    in
    N_ind (fun n : nat => P n) Base Step b.

Definition mul_assoc : forall a b c : nat, (a * b) * c = a * (b * c) :=
  fun a b : nat =>
    let Base : (a * b) * 0 = a * (b * 0) :=
      let H1 : (a * b) * 0 = 0 := mul_0_right (a*b) in
      let H2 : b * 0 = 0 := mul_0_right b in
      let H3 : a * (b * 0) = a * 0 := eq_congr (fun n : nat => a * n) H2 in
      let H4 : a * 0 = 0 := mul_0_right a in
      let H5 : a * (b * 0) = 0 := eq_trans H3 H4 in
      let H6 : (a * b) * 0 = a * (b * 0) := eq_trans H1 (eq_symm H5) in
      H6
    in
    let Step : forall n : nat,
        ((a * b) * n = a * (b * n)) ->
        ((a * b) * (S n) = a * (b * (S n))) :=
      fun (n : nat) (IH : (a * b) * n = a * (b * n)) =>
        let H1 : (a * b) * (S n) = (a * b) * n + a * b := mul_S_right (a * b) n in
        let H2 : (a * b) * n + a * b = a * (b * n) + a * b := eq_congr (fun n : nat => n + a * b) IH in
        let H3 : (a * b) * (S n) = a * (b * n) + a * b := eq_trans H1 H2 in
        let H4 : b * (S n) = b * n + b := mul_S_right b n in
        let H5 : a * (b * (S n)) = a * (b * n + b) := eq_congr (fun n : nat => a * n) H4 in
        let H6 : a * (b * n + b) = a * (b * n) + a * b := distributivity_left a (b * n) b in
        let H7 : a * (b * (S n)) = a * (b * n) + a * b := eq_trans H5 H6 in
        let H8 : a * (b * n) + a * b = a * (b * (S n)) := eq_symm H7 in
        let H9 : (a * b) * (S n) = a * (b * (S n)) := eq_trans H3 H8 in
        H9
    in
    N_ind (fun n : nat => (a * b) * n = a * (b * n)) Base Step.

Definition mul_comm : forall a b : nat, a * b = b * a :=
  fun a : nat =>
    let Base : a * 0 = 0 * a :=
      let H1 : a * 0 = 0 := mul_0_right a in
      let H2 : 0 * a = 0 := mul_0_left a in
      let H3 : 0 = 0 * a := eq_symm H2 in
      let H4 : a * 0 = 0 * a := eq_trans H1 H3 in
      H4
    in
    let Step : forall n : nat,
        (a * n = n * a) ->
        (a * (S n) = (S n) * a) :=
      fun (n : nat) (IH : a * n = n * a) =>
        let H1 : a * (S n) = a * n + a := mul_S_right a n in
        let H2 : (S n) * a = a + n * a := mul_S_left n a in
        let H3 : a * n + a = a + a * n := add_comm (a * n) a in
        let H4 : a * (S n) = a + a * n := eq_trans H1 H3 in
        let H5 : a + a * n = a + n * a := eq_congr (fun n : nat => a + n) IH in
        let H6 : a * (S n) = a + (n * a) := eq_trans H4 H5 in
        let H7 : a + n * a = (S n) * a := eq_symm H2 in
        let H8 : a * (S n) = (S n) * a := eq_trans H6 H7 in
        H8
    in
    N_ind (fun n : nat => a * n = n * a) Base Step.

Definition n_times_2_eq_n_plus_n : forall n : nat, n * (S (S 0)) = n + n :=
    fun n : nat =>
      let H1 : n * (S (S 0)) = n * (S 0) + n := mul_S_right n (S 0) in
      let H2 : n * (S 0) = n := mul_S0_right n in
      let H3 : n * (S 0) + n = n + n := eq_congr (fun k : nat => k + n) H2 in
      let H4 : n * (S (S 0)) = n + n := eq_trans H1 H3 in
      H4.

(* Теоремы про отношение le *)

(* Определение x <= y как "существует такое k, что k + x = y" *)
Definition le : nat -> nat -> Prop :=
  fun x y : nat => exists nat (fun k : nat => k + x = y).

Notation "x <= y" := (le x y) (at level 70, no associativity).

Definition check_le_refl_reduction_step_by_step :
  (forall n : nat, le n n) ->
  forall n : nat, forall C : Prop, (forall x : nat, x + n = n -> C) -> C :=
  fun H0 : forall n : nat, le n n =>
    (* Шаг 1. Раскрываем определение le *)
    let H1 : forall n : nat, (fun x y : nat => exists nat (fun k : nat => k + x = y)) n n := H0 in
    (* Шаг 2. Делаем внешнюю beta-редукцию для аргументов 'n n' *)
    let H2 : forall n : nat, exists nat (fun k : nat => k + n = n) := H1 in
    (* Шаг 3. Раскрываем определение exists *)
    let H3 : (forall n : nat, (fun (A : Type) (B : A -> Prop) => forall (C : Prop), (forall x : A, B x -> C) -> C) nat (fun k : nat => k + n = n)):= H2 in
    (* Шаг 4. Делаем beta-редукцию для 'nat' и предиката *)
    let H4 : (forall n : nat, forall (C : Prop), (forall x : nat, (fun k : nat => k + n = n) x -> C) -> C) := H3 in
    (* Шаг 5. Делаем внутреннюю beta-редукцию для '(fun k ...) x' *)
    let H5 : forall n : nat, forall (C : Prop), (forall x : nat, (x + n = n) -> C) -> C := H4 in
    H5.

Definition le_refl : forall n : nat, le n n :=
  fun n : nat =>
  fun (C : Prop)
    (Request : forall x : nat, (x + n = n) -> C) =>
    Request 0 (add_0_left n).

Definition check_ex_intro_reduction : forall n : nat, le n n :=
  fun n : nat =>
    (* Шаг 1. Полный вызов ex_intro с явно переданными параметрами A и B *)
    let term1 : le n n := @ex_intro nat (fun k : nat => k + n = n) 0 (add_0_left n) in

    (* Шаг 2. Раскрытие определения ex_intro - delta редукция
       плюс β редукция
     *)
    let term2 : exists nat (fun k : nat => k + n = n) :=
        fun C : Prop => fun (Result : forall x : nat, (fun k : nat => k + n = n) x -> C) => Result 0 (add_0_left n) in

   (* Шаг 3. Внутренняя beta-редукция предиката: (fun k => k + n = n) x  ->  x + n = n *)
   let term3 : (forall (C : Prop), (forall x : nat, (x + n = n) -> C) -> C) :=
     fun (C : Prop) =>
     fun Result : forall x : nat, (x + n = n) -> C =>
       Result 0 (add_0_left n) in
   term3.

Definition le_refl_short : forall n : nat, le n n :=
  fun n : nat => ex_intro 0 (add_0_left n).

Definition check_le_0_n_reduction_step_by_step :
  (forall n : nat, le 0 n) ->
  forall n : nat, forall C : Prop, (forall x : nat, x + 0 = n -> C) -> C :=
  (* Нам дано *)
  fun H0 : forall n : nat, le 0 n =>
    (* Шаг 1. Раскрываем определение le (δ редукция) *)
    let H1 : forall n : nat, (fun x y : nat => exists nat (fun k : nat => k + x = y)) 0 n := H0 in
    (* Шаг 2. внешняя β редукция *)
    let H2 : forall n : nat, exists nat (fun k : nat => k + 0 = n) := H1 in
    (* Шаг 3. Раскрываем определение exists (δ редукция) *)
    let H3 : forall n : nat, (fun (A : Type) (B : A -> Prop) => forall (C : Prop), (forall x : A, B x -> C) -> C) nat (fun k : nat => k + 0 = n) := H2 in
    (* Шаг 4. β редукция для exists *)
    let H4 : forall n : nat, forall (C : Prop), (forall x : nat, (fun k : nat => k + 0 = n) x -> C) -> C := H3 in
    (* Шаг 5. Внутренняя beta-редукция предиката: (fun k : nat => k + 0 = n) x  ->  x + n = n *)
    let H5 : forall n : nat, forall C : Prop, (forall x : nat, x + 0 = n -> C) -> C := H4 in
    H5.

Definition le_0_n : forall n : nat, le 0 n :=
  fun n : nat =>
  (* Нам нужно получить тип: exists nat (fun k : nat => k + 0 = n) *)
  (* Что эквивалентно: forall C : Prop, (forall k : nat, k + 0 = n -> C) -> C *)
  fun (C : Prop) (Request : forall k : nat, k + 0 = n -> C) =>
    let H_eq : n + 0 = n := add_0_right n in
    Request n H_eq.

Definition le_0_n_short : forall n : nat, le 0 n :=
  fun n : nat => ex_intro (B := fun k : nat => k + 0 = n) n (add_0_right n).

Definition le_trans : forall a b c : nat, le a b -> le b c -> le a c :=
  fun (a b c : nat) (Hab : le a b) (Hbc : le b c) =>
    (* Распаковать a <= b (получить свидетеля k1 и утверждение k1 + x = y). *)
    ex_elim Hab (fun (k1 : nat) (H1 : k1 + a = b) =>
      ex_elim Hbc (fun (k2 : nat) (H2 : k2 + b = c) =>
        let H3 : b = k1 + a := eq_symm H1 in
        let H4 : k2 + b = k2 + (k1 + a) := eq_congr (fun k => k2 + k) H3 in
        let H5 : (k2 + k1) + a = k2 + (k1 + a) := add_assoc k2 k1 a in
        let H6 : (k2 + k1) + a = k2 + b := eq_trans H5 (eq_symm H4) in
        let H7 : (k2 + k1) + a = c := eq_trans H6 H2 in
        @ex_intro nat (fun x : nat => x + a = c) (k2 + k1) H7)).

Arguments le_trans {_} {_} {_} _ _.

Definition le_antisym : forall a b : nat, le a b -> le b a -> a = b :=
  fun (a b : nat) (Hab : le a b) (Hba : le b a) =>
    let Exists_ab : exists nat (fun k : nat => k + a = b) := Hab in
    let Exists_ba : exists nat (fun k : nat => k + b = a) := Hba in
      ex_elim Exists_ab (fun (k1 : nat) (Wab : k1 + a = b) =>
        ex_elim Exists_ba (fun (k2 : nat) (Wba : k2 + b = a) =>
          let H1 : k2 + (k1 + a) = k2 + b := eq_congr (fun n : nat => k2 + n) Wab in
          let H2 : (k2 + k1) + a = k2 + (k1 + a) := add_assoc k2 k1 a in
          let H3 : (k2 + k1) + a = k2 + b := eq_trans H2 H1 in
          let H4 : (k2 + k1) + a = a := eq_trans H3 Wba in
          let H5 : (k2 + k1) + a = a + (k2 + k1) := add_comm (k2 + k1) a in
          let H6 : a + (k2 + k1) = a := eq_trans (eq_symm H5) H4 in
          let H7 : k2 + k1 = 0 := add_right_eq_self H6 in
          let H8 : k2 = 0 /\ k1 = 0 := n_k_eq_0 H7 in
          let H9 : k1 = 0 := and_elim2 H8 in
          let H10 : k1 + a = 0 + a := eq_congr (fun n : nat => n + a) H9 in
          let H11 : 0 + a = a := add_0_left a in
          let H12 : k1 + a = a := eq_trans H10 H11 in
          let H13 : a = k1 + a := eq_symm H12 in
          let H14 : a = b := eq_trans H13 Wab in
          H14)).

Arguments le_antisym {_} {_} _ _.

Definition le_not_S_le : forall n : nat, ~ (S n <= n) :=
  (* 1. Выносим предикат индукции в отдельную переменную *)
  let P : nat -> Prop :=
    fun n : nat => ~ (le (S n) n)
  in
  let Base : P 0 :=
    fun (H0 : le (S 0) 0) =>
      (* Раскрыли определение le *)
      let H1 : exists nat (fun k : nat => k + (S 0) = 0) := H0 in
        ex_elim H1 (fun (k : nat) (W : k + (S 0) = 0) =>
          let H2 : k + (S 0) = S (k + 0) := add_S_right k 0 in
          let H3 : S (k + 0) = k + (S 0) := eq_symm H2 in
          let H4 : S (k + 0) = 0 := eq_trans H3 W in
          let H5 : False := S_not_O (eq_symm H4) in
          H5)
  in
  let Step : forall n : nat, P n -> P (S n) :=
    fun (n : nat) (IH : P n) =>
    fun (H0 : le (S (S n)) (S n)) =>
      (* Раскрыли определение le *)
      let H1 : exists nat (fun k : nat => k + S (S n) = S n) := H0 in
        ex_elim H1 (fun (k : nat) (W : k + S (S n) = S n) =>
          let H2 : k + S (S n) = S (k + S n) := add_S_right k (S n) in
          let H3 : S (k + S n) = k + S (S n) := eq_symm H2 in
          let H4 : S (k + S n) = S n := eq_trans H3 W in
          let H5 : k + S n = n := S_inj H4 in
          let H6 : exists nat (fun k : nat => k + S n = n) := ex_intro k H5 in
          IH H6)
  in
  N_ind (fun n : nat => ~ (le (S n) n)) Base Step.

Definition add_le_mono : forall a b c : nat, a <= b -> a + c <= b + c :=
  fun (a b c : nat) (Le_ab: a <= b) =>
    (* 1. Выносим предикат индукции в отдельную переменную *)
    let P : nat -> Prop :=
      fun n : nat => a + n <= b + n
    in
    let Base : P 0 :=
      (* Раскрыли определение le в Le_ab *)
      let H1 : exists nat (fun k : nat => k + a = b) := Le_ab in
      ex_elim H1 (fun (k : nat) (W : k + a = b) =>
        let H2 : b + 0 = b := add_0_right b in
        let H3 : b = b + 0 := eq_symm H2 in
        let H4 : k + a = b + 0 := eq_trans W H3 in
        let H5 : a + 0 = a := add_0_right a in
        let H6 : k + (a + 0) = k + a := eq_congr (fun n : nat => k + n) H5 in
        let H7 : k + (a + 0) = b + 0 := eq_trans H6 H4 in
        let H8 : exists nat (fun k : nat => k + (a + 0) = b + 0) := ex_intro k H7 in
        H8
        )
    in
    let Step : forall n : nat, P n -> P (S n) :=
      fun (n : nat) (IH : le (a + n) (b + n)) =>
        (* Раскрыли определение le в IH *)
        let H1 : exists nat (fun k => k + (a + n) = (b + n)) := IH in
          ex_elim IH (fun (k : nat) (W : k + (a + n) = (b + n)) =>
            let H2 : a + S n = S (a + n) := add_S_right a n in
            let H3 : k + S(a + n) = S (k + (a + n)) := add_S_right k (a + n) in
            let H4 : k + (a + S n) = k + S (a + n) := eq_congr (fun p : nat => k + p) H2 in
            let H5 : k + (a + S n) = S (k + (a + n)) := eq_trans H4 H3 in
            let H6 : S (k + (a + n)) = S (b + n) := eq_congr S W in
            let H7 : k + (a + S n) = S (b + n) := eq_trans H5 H6 in
            let H8 : b + S n = S (b + n) := add_S_right b n in
            let H9 : S (b + n) = b + S n := eq_symm H8 in
            let H10 : k + (a + S n) = b + S n := eq_trans H7 H9 in
            let H11 : exists nat (fun k : nat => k + (a + S n) = b + S n) := ex_intro k H10 in
            H11)
    in
    N_ind (fun n : nat => le (a + n) (b + n)) Base Step c.

(* Definition mul_le_mono : forall a b c : nat, a <= b -> a * c <= b * c := *)
(*   fun (a b c : nat) (H0: a <= b) => *)


Definition le_Sa_le_a1 : forall a b : nat, S a <= b -> a <= b :=
  fun (a b :nat) (H0 : le (S a) b) =>
    (* Раскрыли определение le в H0 *)
    let H1 : exists nat (fun k : nat => k + (S a) = b) := H0 in
    ex_elim H1 (fun (k : nat) (W : k + (S a) = b) =>
      let H2 : a + S 0 = S a := a_plus_S0 a in
      let H3 : S a = a + S 0 := eq_symm H2 in
      let H4 : a + S 0 = S 0 + a := add_comm a (S 0) in
      let H5 : S a = S 0 + a := eq_trans H3 H4 in
      let H6 : k + S a = k + (S 0 + a) := eq_congr (fun n : nat => k + n) H5 in
      let H7 : (k + S 0) + a = k + (S 0 + a) := add_assoc k (S 0) a in
      let H8 : k + (S 0 + a) = (k + S 0) + a := eq_symm H7 in
      let H9 : k + S a = (k + S 0) + a := eq_trans H6 H8 in
      let H10 : (k + S 0) + a = k + S a := eq_symm H9 in
      let H11 : (k + S 0) + a = b := eq_trans H10 W in
      let H12 : exists nat (fun n : nat => n + a = b) := ex_intro (k + S 0) H11 in
      (* Закрыли определение le *)
      let H13 : le a b := H12 in
      H13).

(* Более элегантное доказательство теоремы *)
Definition le_Sa_le_a : forall a b : nat, S a <= b -> a <= b :=
  fun (a b :nat) (H0 : le (S a) b) =>
    (* Раскрыли определение le в H0 *)
    let H1 : exists nat (fun k : nat => k + S a = b) := H0 in
    ex_elim H1 (fun (k : nat) (W : k + S a = b) =>
      let H2 : k + S a = S (k + a) := add_S_right k a in
      let H3 : S k + a = S (k + a) := add_S_left k a in
      let H4 : S (k + a) = k + S a := eq_symm H2 in
      let H5 : S k + a = k + S a := eq_trans H3 H4 in
      let H6 : S k + a = b := eq_trans H5 W in
      let H7 : exists nat (fun k : nat => k + a = b) := ex_intro (S k) H6 in
      (* Закрыли определение le *)
      let H8 : le a b := H7 in
      H8).

Arguments le_Sa_le_a {_} {_} _.

Definition a_le_b_or : forall a b : nat, a <= b -> a = b \/ S a <= b :=
  fun (a b : nat) (H0 : a <= b) =>
    (* Раскрыл определение le в H0 *)
    let H1 : exists nat (fun k : nat => k + a = b) := H0 in
    ex_elim H1 (fun k : nat =>
      (* Выносим предикат индукции в отдельную переменную *)
      let P : nat -> Prop := fun n : nat => n + a = b -> a = b \/ S a <= b in
      (* 0 + a = b -> a = b \/ S a <= b   *)
      let Base : P 0 :=
        fun (H2 : 0 + a = b) =>
          let H3 : 0 + a = a := add_0_left a in
          let H4 : a = 0 + a := eq_symm H3 in
          let H5 : a = b := eq_trans H4 H2 in
          let H6 : a = b \/ S a <= b := or_intro_left (a = b) (S a <= b) H5 in
          H6
      in
      let Step : forall n : nat, P n -> P (S n) :=
        fun (n : nat) (IH : P n) =>
          (* Раскрыли индуктивную гипотезу *)
          let IH1 : n + a = b -> a = b \/ S a <= b := IH in
          fun (H2 : S n + a = b) =>
            let H3 : S n + a = S (n + a) := add_S_left n a in
            let H4 : n + S a = S (n + a) := add_S_right n a in
            let H5 : S (n + a) = S n + a := eq_symm H3 in
            let H6 : n + S a = S n + a := eq_trans H4 H5 in
            let H7 : n + S a = b := eq_trans H6 H2 in
            let H8 : exists nat (fun k : nat => k + S a = b) := ex_intro n H7 in
            let H9 : S a <= b := H8 in
            let H10 : a = b \/ S a <= b := or_intro_right (a = b) (S a <= b) H9 in
            H10
     in
     N_ind (fun n : nat => P n) Base Step k
      ).

Arguments a_le_b_or {_} {_} _.

Definition le_total_left_eq : forall a b : nat, a = S b -> S a <= S b \/ S b <= S a :=
  fun (a b : nat) (H0 : a = S b) =>
    let H1 : S b = a := eq_symm H0 in
    let H2 : S 0 + S b = S 0 + a := eq_congr (fun n : nat => S 0 + n) H1 in
    let H3 : S 0 + a = S a := S0_plus_a a in
    let H4 : S 0 + S b = S a := eq_trans H2 H3 in
    let H5 : exists nat (fun k : nat => k + S b = S a) := ex_intro (S 0) H4 in
    let H6 : S b <= S a := H5 in
    let H7 : S a <= S b \/ S b <= S a := or_intro_right (S a <= S b) (S b <= S a) H6 in
    H7.

Definition le_total_left : forall a b : nat, a <= b -> S a <= b \/ b <= S a :=
  fun (a b : nat) (H0 : a <= b) =>
    let H_disj : a = b \/ S a <= b := a_le_b_or H0 in
    let H_right : S a <= b -> S a <= b \/ b <= S a := or_intro_left (S a <= b) (b <= S a) in
    let H_left : a = b -> S a <= b \/ b <= S a :=
      (fun Heq : a = b =>
         let H1 : b = a := eq_symm Heq in
         let H2 : S 0 + b = S 0 + a := eq_congr (fun k : nat => S 0 + k) H1 in
         let H3 : S 0 + a = S a := S0_plus_a a in
         let H4 : S 0 + b = S a := eq_trans H2 H3 in
         let H5 : exists nat (fun k : nat => k + b = S a) := ex_intro (S 0) H4 in
         let H6 : b <= S a := H5 in
         let H7 : S a <= b \/ b <= S a := or_intro_right (S a <= b) (b <= S a) H6 in
         H7
      )
    in
    let H_disj_elim : forall (C : Prop), (a = b -> C) -> (S a <= b -> C) -> C := H_disj in
    H_disj_elim (S a <= b \/ b <= S a) H_left H_right.

Definition le_a_b_le_a_Sb : forall a b : nat, a <= b -> a <= S b :=
  fun (a b : nat) (H0 : a <= b) =>
    (* Раскрыли определение le в H0 *)
    let H1 : exists nat (fun k : nat => k + a = b) := H0 in
    ex_elim H1 (fun (k : nat) (W : k + a = b) =>
      let H2 : S(k + a) = S b := eq_congr S W in
      let H3 : S k + a = S (k + a) := add_S_left k a in
      let H4 : S k + a = S b := eq_trans H3 H2 in
      let H5 : exists nat (fun n : nat => n + a = S b) := ex_intro (S k) H4 in
      let H6 : a <= S b := H5 in
      H6
      ).

Arguments le_a_b_le_a_Sb {_} {_} _.

Definition le_total_right : forall a b : nat, b <= a -> S a <= b \/ b <= S a :=
  fun (a b : nat) (H0 : b <= a) =>
    let H1 : b <= S a := le_a_b_le_a_Sb  H0 in
    let H2 : S a <= b \/ b <= S a := or_intro_right (S a <= b) (b <= S a) H1 in
    H2.

Definition le_total : forall a b : nat, a <= b \/ b <= a :=
  fun (a b : nat) =>
    (* 1. Выносим предикат индукции в отдельную переменную *)
    let P : nat -> Prop :=
      fun n : nat => (n <= b) \/ (b <= n)
    in
    let Base : P 0 :=
      let H1 : le 0 b := le_0_n b in
      or_intro_left (le 0 b) (le b 0) H1
    in
    let Step : forall n : nat, P n -> P (S n) :=
      fun (n : nat) (IH : P n) =>
        (* Раскрыли определение IH *)
        let H_disj : n <= b \/ b <= n := IH in
        let H_left : n <= b -> (S n <= b) \/ (b <= S n) := le_total_left n b in
        let H_right : b <= n -> (S n <= b) \/ (b <= S n) := le_total_right n b in
        (* Раскрыли определение дизъюнкции как элиминатора *)
        let H_disj_elim : forall (C : Prop), (n <= b -> C) -> (b <= n -> C) -> C := H_disj in
        H_disj_elim (S n <= b \/ b <= S n) H_left H_right
    in
    N_ind (fun n : nat => P n) Base Step a.

(* Теоремы про отношение lt *)

Definition lt : nat -> nat -> Prop :=
  fun a b : nat => S a <= b.

Notation "x < y" := (lt x y) (at level 70, no associativity).

Definition check_lt_antirefl_reduction :
  (forall n : nat, ~ (lt n n)) ->
  forall n : nat, ~ (exists nat (fun k : nat => k + S n = n))
  :=
  fun H0 : forall n : nat, ~ (lt n n) =>
    (* Шаг 1. Раскрыли определение lt - δ редукция *)
    let H1 : forall n : nat, ~ (le (S n) n) := H0 in
    (* Шаг 2. Раскрыли определение le - δ редукция *)
    let H2 : forall n : nat, ~ (exists nat (fun k => k + S n = n)) := H1 in
    H2.

(* Раскрыв определение, мы получили старого знакомого -
Definition le_not_S_le : forall n : nat, ~ (le (S n) n) := *)

Definition lt_antirefl : forall n : nat, ~ (n < n) := le_not_S_le.

Definition lt_trans : forall a b c : nat, a < b -> b < c -> a < c :=
  fun (a b c : nat) (H1 : lt a b) (H2 : lt b c) =>
    (* Раскрыли определение lt *)
    let H3 : le (S a) b := H1 in
    let H4 : le (S b) c := H2 in
    let H5 : le b c := le_Sa_le_a H4 in
    let H6 : le (S a) c := le_trans H3 H5 in
    H6.
