Module CoC.

Notation "A -> B" := (forall (_ : A), B)
                      (right associativity, at level 99).

Definition False : Prop :=
  forall P : Prop, P.

Definition True : Prop :=
  forall P : Prop, P -> P.

Definition I : True :=
  fun (P : Prop) (p : P) => p.

Definition not (P : Prop) : Prop :=
  P -> False.

Notation "~ A" := (not A) (at level 75, right associativity).

(* Смысл определения: если высказывание C следует из A и B, и у нас есть оба конъюнкта, то мы можем получить C. *)
Definition and (A B : Prop) : Prop :=
  forall C : Prop, (A -> B -> C) -> C.

Notation "A /\ B" := (and A B) (at level 80, right associativity).

  (* Закон исключения дизъюнкции *)
  Definition or (A B : Prop) : Prop :=
    forall (C : Prop), (A -> C) -> (B -> C) -> C.

  Notation "A \/ B" := (or A B) (at level 85, right associativity).

  (* Эквивалентность на универсуме: два объекта эквивалентны,
     если они обладают одинаковыми свойствами
  *)
  Definition eq {A : Type} (x y : A) : Prop :=
    forall P : A -> Prop, P x -> P y.

  Notation "x = y" := (eq x y) (at level 70, no associativity).

  (* exists - это свойство предиката B на универсуме A, что B не пусто *)
  Definition exists : forall (A : Type) (B : A -> Prop), Prop :=
    fun (A : Type) (B : A -> Prop) => forall (C : Prop), (forall x : A, B x -> C) -> C.

  Definition ex_intro {A : Type} {B : A -> Prop} (t : A) (p : B t) : exists A B :=
    fun (C : Prop) => fun (H : forall x : A, B x -> C) => H t p.

(*
  Γ ⊢ t : ∃x : A, B Γ, x : A, p : B ⊢ u : C x !∈ Γ, C
  Γ ⊢ t C (fun (x : A)(p : B) ⇒ u) : C
*)
  Definition ex_elim {A : Type} {P : A -> Prop} {C : Prop}
    (H_exists : exists A P)                    (* Γ ⊢ ∃x:A, P x *)
    (* Γ ⊢ ∀x:A, P x → C *)
    : (forall x : A, P x -> C) -> C := H_exists C.

  Definition eq_subst :
    forall (A : Type) (x y : A) (P : A -> Prop), x = y -> P x -> P y :=
    fun (A : Type) (x y : A) (P : A -> Prop) (Heq : x = y) (Px : P x) =>
      Heq P Px.

  Definition eq_refl {U : Type} (x : U) : x = x :=
    fun (P : U -> Prop) (Px : P x) => Px.

  Definition eq_symm {U : Type} {x y : U} : x = y -> y = x :=
    fun Heq : x = y =>
    fun (P : U -> Prop) (Py : P y) =>
      let HPz : U -> Prop := (fun z : U => P z -> P x) in
      let H1 : HPz x -> HPz y := (Heq HPz) in
      let PxPx : P x -> P x := (fun h : P x => h) in
      let H2 : P y -> P x := H1 PxPx in
      H2 Py.

  Definition eq_trans {U : Type} {x y z : U} :
    x = y -> y = z -> x = z :=
    fun
      (Heq1 : x = y)
      (Heq2 : y = z)
      (P : U -> Prop)
      (Px : P x) => Heq2 P (Heq1 P Px).

  Definition eq_congr :
    forall {A B : Type} (f : A -> B) {x y : A},
      x = y -> (f x) = (f y) :=
    fun (A B : Type) (f : A -> B) (x y : A) (Heq : x = y) =>
    fun (P : B -> Prop) (Pfx : P (f x)) =>
      Heq (fun z : A => P (f z)) Pfx.

End CoC.

Module Bool.
  Import CoC.
  Definition bool : Type := forall P : Type, P -> P -> P.

  Definition true : bool := fun (P : Type) (t f : P) => t.
  Definition false : bool := fun (P : Type) (t f : P) => f.

  Definition andb (b1 b2 : bool) : bool :=
    fun (P : Type) (t f : P) => b1 P (b2 P t f) f.

  Definition orb (b1 b2 : bool) : bool :=
    fun (P : Type) (t f : P) => b1 P t (b2 P t f).

  Definition notb_CoC (b : bool) : bool :=
    fun (P : Type) (t f : P) => b P f t.

  Definition true_ne_false : ~ (true = false) :=
    fun (Heq : true = false) =>
      (* 1. Define a predicate that evaluates to True if given true, *)
      (* and False if given false. *)
      let P_discr : bool -> Prop :=
        fun (b : bool) => b Prop True False in
      (* 2. Apply your equality hypothesis to your custom predicate. *)
      (* Because Coq beta-reduces silently, the type of H_impl *)
      (* is exactly: True_CoC -> False *)
      let H_impl : P_discr true -> P_discr false :=
        Heq P_discr in
      (* You now have H_impl, which expects a proof of True. *)
      (* You also have I. *)
      let H_False : False := H_impl I in
      H_False.
End Bool.

Section CoC_example.
  Import CoC.
  Variable U : Type. (* Универсум *)
  Variable B : U -> Prop. (* Предикат на универсуме *)
  Variable t : U. (* Объект универсума *)

  (* If Γ ⊢ p : B t *)
  (* В контексте Γ p - это доказательство того, что
    объект универсума t удовлетворяет предикату B
   *)
  Variable p : B t.

  Variable Person : Type.
  Variable is_happy : Person -> Prop.
  Variable bob : Person.
  Variable bob_is_happy : is_happy bob.

  (* Proving that someone is happy using our manual Ex *)
  Definition someone_is_happy : exists Person is_happy :=
      @ex_intro Person is_happy bob bob_is_happy.

End CoC_example.

Section CoC_theorems.
  Import CoC.

  Definition ex_not_forall (A : Type) (P : A -> Prop) (C : Prop) :
    exists A P -> ~ (forall x : A, ~ (P x)) :=
      fun (Hex : exists A P) (Hcontra : (forall x : A, ~ (P x))) =>
        let false : False := ex_elim Hex Hcontra in
      false.

  Definition and_elim1 : forall {A B : Prop}, A /\ B -> A :=
    fun A B : Prop =>
      fun Hand : A /\ B => Hand A (fun (a : A) (b : B) => a).

  Definition and_elim2 : forall {A B : Prop}, A /\ B -> B :=
    fun (A B : Prop) =>
     fun (Hand : A /\ B) => Hand B (fun (a : A) (b : B) => b).

  Definition and_intro : forall {A B : Prop}, A -> B -> A /\ B :=
    fun A B : Prop =>
      fun (a : A) (b : B) =>
        fun (C : Prop) (HAB_C : A -> B -> C) => HAB_C a b.

  Definition and_comm {A B : Prop} : A /\ B -> B /\ A :=
    fun (Hand : A /\ B) =>
      fun (C : Prop) (f : B -> A -> C) =>
        Hand C (fun (a : A) (b : B) => f b a).

  Definition ex_falso (A : Prop) : A -> ~ A -> False :=
    fun (a : A) (na : ~ A) =>
      na a.

  Definition or_intro_left : forall (A B : Prop), A -> A \/ B :=
    fun (A B : Prop) (Ha : A) =>
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hac Ha.

  Definition or_intro_right : forall (A B : Prop), B -> A \/ B :=
    fun (A B : Prop) (Hb : B) =>
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hbc Hb.

  Definition or_comm (A B : Prop) : A \/ B -> B \/ A :=
    fun (Hor : A \/ B) =>
      fun (C : Prop) (fB : B -> C) (fA : A -> C) =>
        Hor C fA fB.

  Definition id : forall A : Type, A -> A :=
    fun (A : Type) (a : A) => a.

  Definition or_idempotent : forall {A : Prop}, A \/ A -> A :=
    fun (A : Prop) (Hor : A \/ A) =>
      Hor A (id A) (id A).

  Definition and_idempotent : forall {A : Prop}, A /\ A -> A :=
    fun (A : Prop) (Hand : A /\ A) =>
      Hand A (fun (a _ : A) => a).

  Definition uncurry: forall {A B C : Prop}, (A -> B -> C) -> (A /\ B) -> C :=
    fun (A B C : Prop) (HAB_C : A -> B -> C) (Hconj : A /\ B) =>
      Hconj C HAB_C.

  Definition curry : forall {A B C : Prop}, (A /\ B -> C) -> A -> B -> C :=
    fun (A B C : Prop) =>
      fun (f : (A /\ B) -> C) (a : A) (b : B) =>
        let Hconj : A /\ B := and_intro a b in
        f Hconj.

  Definition contrapos : forall P Q : Prop, (P -> Q) -> ~Q -> ~P :=
    fun (P Q : Prop) (HP_Q : P -> Q) (nQ : ~Q) (p : P) => nQ (HP_Q p).

  Definition deMorgan_disj {A B : Prop} :
    ~ (A \/ B) -> ~ A /\ ~ B :=
    fun (NotOr : ~ (A \/ B)) =>
      fun (C : Prop) (H : ~ A -> ~ B -> C) =>
        H
          (fun (a : A) => NotOr (or_intro_left A B a))
          (fun (b : B) => NotOr (or_intro_right A B b)).

  Definition deMorgan_disj_back : forall {A B : Prop},
    ~ A /\ ~ B -> ~ (A \/ B) :=
    fun (A B : Prop) =>
      fun (Hand : ~ A /\ ~ B) =>
        fun (Hor : A \/ B) =>
          Hor False (and_elim1 Hand) (and_elim2 Hand).

  Definition frobenius_dir (A : Type) (P : A -> Prop) (Q : Prop) :
    exists A (fun x => (P x) /\ Q) -> (exists A P) /\ Q :=
      fun (Hex : exists A (fun x : A => (P x) /\ Q)) =>
        Hex ((exists A P) /\ Q) (
            fun (x : A) (Hpq : (P x) /\ Q) =>
              let Px : P x := and_elim1 Hpq in
              let q : Q := and_elim2 Hpq in
              let exP : exists A P := ex_intro x Px in
                        and_intro exP q).

  Definition and_or_distr (A B C : Prop) : A /\ (B \/ C) -> (A /\ B) \/ (A /\ C) :=
      fun (H : A /\ (B \/ C)) =>
        let a := and_elim1 H in
        let b_or_c := and_elim2 H in
        let case1 := (fun b : B =>
                      let a_and_b := and_intro a b in
                      or_intro_left (A /\ B) (A /\ C) a_and_b
                   ) in
      let case2 := (fun c : C =>
                      let a_and_c := and_intro a c in
                      or_intro_right (A /\ B) (A /\ C) a_and_c
                   ) in
      b_or_c (A /\ B \/ A /\ C) case1 case2.

  Definition ex1 (A : Prop) : ~ ~ (~ A \/ A) := fun (H : ~ ((~ A) \/ A)) =>
    let conj1 := (deMorgan_disj H) in
      (uncurry (ex_falso (~ A))) (and_comm conj1).

(*
  Следующий вызов: Попробуй формализовать числа Чёрча (Nat_CoC) и операцию plus_CoC. Доказательство того, что plus_CoC zero n = n через прямой терм — это отличная тренировка «умственной выносливости».
 *)

End CoC_theorems.

Module PeanoArithmetic.
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

  Definition mul_S0 : forall a : nat, a * (S 0) = a :=
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
      (* 1. Выносим предикат индукции в отдельную переменную *)
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
      N_ind (fun n : nat => (S a) * n = n + a * n)
        Base
        Step.

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
      N_ind (fun n : nat => (a * b) * n = a * (b * n))
        Base
        Step.

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
      N_ind (fun n : nat => a * n = n * a)
        Base
        Step.

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

  Definition n_times_2_eq_n_plus_n : forall n : nat, n * (S (S 0)) = n + n :=
    fun n : nat =>
      let H1 : n * (S (S 0)) = n * (S 0) + n := mul_S_right n (S 0) in
      let H2 : n * (S 0) = n := mul_S0 n in
      let H3 : n * (S 0) + n = n + n := eq_congr (fun k : nat => k + n) H2 in
      let H4 : n * (S (S 0)) = n + n := eq_trans H1 H3 in
      H4.

  Definition le_not_S_le : forall n : nat, ~ (le (S n) n) :=
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
      N_ind (fun n : nat => ~ (le (S n) n))
        Base
        Step.

  Definition add_le_mono : forall a b c : nat, le a b -> le (a + c) (b + c) :=
    fun (a b c : nat) (Le_ab: le a b) =>
      (* 1. Выносим предикат индукции в отдельную переменную *)
      let P : nat -> Prop :=
        fun n : nat => le (a + n) (b + n)
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

  Definition lt : nat -> nat -> Prop :=
    fun a b : nat => le (S a) b.

  Definition check_lt_antirefl_reduction :
    (forall n : nat, ~ (lt n n)) ->
    forall n : nat, ~ (exists nat (fun k => k + S n = n))
    :=
    fun H0 : forall n : nat, ~ (lt n n) =>
      (* Шаг 1. Раскрыли определение lt (δ редукция) *)
      let H1 : forall n : nat, ~ (le (S n) n) := H0 in
      let H2 : forall n : nat, ~ (exists nat (fun k => k + S n = n)) := H1 in
      H2.

  (* Расрыв определение, мы получили старого знакомого -
  Definition le_not_S_le : forall n : nat, ~ (le (S n) n) := *)

  Definition lt_antirefl : forall n : nat, ~ (lt n n) := le_not_S_le.

  Definition a_plus_S0 : forall a : nat, a + S 0 = S a :=
    fun a : nat =>
      let H1 : a + S 0 = S (a + 0) := add_S_right a 0 in
      let H2 : a + 0 = a := add_0_right a in
      let H3 : S (a + 0) = S a := eq_congr S H2 in
      let H4 : a + S 0 = S a := eq_trans H1 H3 in
      H4.

  Definition le_Sa_le_a1 : forall a b : nat, le (S a) b -> le a b :=
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
  Definition le_Sa_le_a : forall a b : nat, le (S a) b -> le a b :=
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

  Definition lt_trans : forall a b c : nat, lt a b -> lt b c -> lt a c :=
    fun (a b c : nat) (H1 : lt a b) (H2 : lt b c) =>
      (* Раскрыли определение lt *)
      let H3 : le (S a) b := H1 in
      let H4 : le (S b) c := H2 in
      let H5 : le b c := le_Sa_le_a H4 in
      let H6 : le (S a) c := le_trans H3 H5 in
      H6.

  Definition a_le_b_or : forall a b : nat, a <= b -> a = b \/ S a <= b :=
    fun (a b : nat) (H0 : a <= b) =>
      (* Раскрыл определение le в H0 *)
      let H1 : exists nat (fun k : nat => k + a = b) := H0 in
      ex_elim H1 (fun k : nat =>
        (* 1. Выносим предикат индукции в отдельную переменную *)
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
      let H3 : S 0 + a = a + S 0 := add_comm (S 0) a in
      let H4 : a + S 0 = S a := a_plus_S0 a in
      let H5 : S 0 + a = S a := eq_trans H3 H4 in
      let H6 : S 0 + S b = S a := eq_trans H2 H5 in
      let H7 : exists nat (fun k : nat => k + S b = S a) := ex_intro (S 0) H6 in
      let H8 : S b <= S a := H7 in
      let H9 : S a <= S b \/ S b <= S a := or_intro_right (S a <= S b) (S b <= S a) H8 in
      H9.

  Definition le_total_left : forall a b : nat, a <= b -> S a <= b \/ b <= S a :=
    fun a b : nat =>
      (* Выносим предикат индукции в отдельную переменную *)
      let P : nat -> Prop :=
        fun n : nat => a <= n -> S a <= n \/ n <= S a
      in
      let Base : P 0 :=
        fun (_ : a <= 0) =>
          let H1 : 0 <= S a := le_0_n (S a) in
          let H2 : S a <= 0 \/ 0 <= S a := or_intro_right (S a <= 0) (0 <= S a) H1 in
          H2
      in
      let Step : forall n : nat, P n -> P (S n) :=
        fun (n : nat) (IH : P n) =>
          fun (H0 : a <= S n) =>
            let IH1 : a <= n -> S a <= n \/ n <= S a := IH in
            let H_disj : a = S n \/ S a <= S n := a_le_b_or H0 in
            let H_right : S a <= S n -> S a <= S n \/ S n <= S a := or_intro_left (S a <= S n) (S n <= S a) in
            (* Раскрыли определение дизъюнкции как элиминатора *)
            let H_disj_elim : forall (C : Prop), (a = S n -> C) -> (S a <= S n -> C) -> C := H_disj in
            H_disj_elim (S a <= S n \/ S n <= S a) (le_total_left_eq a n) H_right
      in
      N_ind (fun n : nat => P n) Base Step b.

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

  Definition le_total : forall a b : nat, or (le a b) (le b a) :=
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

End PeanoArithmetic.

Module ChurchArithmetic.

  Import CoC.
  (* A Church numeral is a function that takes a type, a step function,
     and a starting base value. *)
  Definition nat_C : Type :=
    forall P : Type, (P -> P) -> P -> P.

  Definition zero : nat_C :=
    fun (P : Type) (S : P -> P) (z : P) => z.

  Definition succ : nat_C -> nat_C :=
    fun (n : nat_C) (P : Type) (S : P -> P) (z : P) => S (n P S z).

  Definition plus : nat_C -> nat_C -> nat_C :=
    fun (n m : nat_C) (P : Type) (S : P -> P) (z : P) => n P S (m P S z).

  (* Short-hand definitions for 1 and 2 *)
  Definition one : nat_C := succ zero.
  Definition two : nat_C := succ (succ zero).

  (* THE CHALLENGE: Prove 1 + 1 = 2 *)
  Definition plus_one_one_eq_two : (plus one one) = two :=
    fun (P : nat_C -> Prop) (Hplus : P (plus one one)) =>

      (* 1. Expand the definition of 'plus' *)
      let H1 : P (fun (P0 : Type) (S : P0 -> P0) (z : P0) => one P0 S (one P0 S z)) := Hplus in

      (* 2. Expand the outer 'one' (which is 'succ zero') *)
      let H2 : P (fun (P0 : Type) (S : P0 -> P0) (z : P0) => S (zero P0 S (one P0 S z))) := H1 in

      (* 3. Beta-reduce 'zero' (which ignores 'S' and returns its base argument) *)
      let H3 : P (fun (P0 : Type) (S : P0 -> P0) (z : P0) => S (one P0 S z)) := H2 in

      (* 4. Expand the inner 'one' *)
      let H4 : P (fun (P0 : Type) (S : P0 -> P0) (z : P0) => S (S (zero P0 S z))) := H3 in

      (* 5. Beta-reduce the inner 'zero' *)
      let H5 : P (fun (P0 : Type) (S : P0 -> P0) (z : P0) => S (S z)) := H4 in

      (* 6. Recognize that this final normal form is exactly 'two' *)
      let H6 : P two := H5 in
      H6.

  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
    fun x : A => g (f x).

  Notation "g ∘ f" := (compose g f) (at level 50, right associativity).
  Definition apply_twice {A : Type} (f : A -> A) : A -> A := f ∘ f.

  Definition compose_assoc {A B C D : Type} (f : A -> B) (g : B -> C) (h : C -> D) :
    forall x : A, (h ∘ (g ∘ f)) x = ((h ∘ g) ∘ f) x :=
    fun (x : A) => eq_refl.

  (* Теорема 2: Четырехкратное применение.
     Если мы применим `apply_twice` к функции `apply_twice f`,
     это должно быть эквивалентно f(f(f(f(x)))). *)
  Definition apply_four_times {A : Type} (f : A -> A) :
    forall x : A, apply_twice (apply_twice f) x = f (f (f (f x))) :=
    fun (x : A) => eq_refl.

  Definition K_comb {A B : Type} : A -> B -> A :=
    fun (x : A) (_ : B) => x.

  Definition K_comb_keeps_first {A B : Type} : forall (x : A) (y : B), K_comb x y = x := fun (x : A) (y : B) => eq_refl.

  Definition C_comb {A B C : Type} : (A -> B -> C) -> (B -> A -> C) :=
    fun (f : A -> B -> C) (b : B) (a : A) => f a b.

  Definition C_comb_involutive {A B C : Type} (f : A -> B -> C) :
    forall (x : A) (y : B), C_comb (C_comb f) x y = f x y :=
  fun (x : A) (y : B) => eq_refl.

  Definition mul : nat_C -> nat_C -> nat_C :=
    fun (n m : nat_C) (P : Type) (S : P -> P) (z : P) => n P (m P S) z.

End ChurchArithmetic.

(* Local Variables: *)
(* coq-prog-args: ("-noinit") *)
(* End: *)
