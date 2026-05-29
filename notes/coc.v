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
    (H_goal : forall x : A, P x -> C)      (* Γ ⊢ ∀x:A, P x → C *)
    : C := H_exists C H_goal.

  Definition eq_subst :
    forall (A : Type) (x y : A) (P : A -> Prop), x = y -> P x -> P y :=
    fun (A : Type) (x y : A) (P : A -> Prop) (Heq : x = y) (Px : P x) =>
      Heq P Px.

  Definition eq_refl {U : Type} {x : U} : x = x :=
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
           and_intro exP q
       ).

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
                                                                           let conj1 := (deMorgan_disj H) in                                                            (uncurry (ex_falso (~ A))) (and_comm conj1).

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
  (* S инъективна *)
  Axiom S_inj : forall x y : nat, (S x) = (S y) -> x = y.
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
      N_ind (fun n : nat => (a*b) * n = a * (b*n))
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
    (forall n : nat, forall (C : Prop), (forall x : nat, x + n = n -> C) -> C) :=
    fun H =>
      (* Шаг 1. Исходный тип из аргумента H *)
      let H0 : forall n : nat, le n n := H in
      (* Шаг 2. Раскрываем определение le *)
      let H1 : (forall n : nat, (fun x y : nat => exists nat (fun k : nat => k + x = y)) n n) := H0 in
      (* Шаг 3. Делаем внешнюю beta-редукцию для аргументов 'n n' *)
      let H2 : (forall n : nat, exists nat (fun k : nat => k + n = n)) := H1 in
      (* Шаг 4. Раскрываем определение exists *)
      let H3 : (forall n : nat, (fun (A : Type) (B : A -> Prop) => forall (C : Prop), (forall x : A, B x -> C) -> C) nat (fun k : nat => k + n = n)):= H2 in
      (* Шаг 5. Делаем beta-редукцию для 'nat' и предиката *)
      let H4 : (forall n : nat, forall (C : Prop), (forall x : nat, (fun k : nat => k + n = n) x -> C) -> C) := H3 in
      (* Шаг 6. Делаем внутреннюю beta-редукцию для '(fun k ...) x' *)
      let H5 : (forall n : nat, forall (C : Prop), (forall x : nat, (x + n = n) -> C) -> C) := H4 in
      H5.

  Definition le_refl : forall n : nat, n <= n :=
    fun n : nat =>
    fun (C : Prop)
      (Request : forall x : nat, (x + n = n) -> C) =>
      Request 0 (add_0_left n).

  Definition check_ex_intro_reduction : forall n : nat, le n n :=
    fun n : nat =>
      (* Шаг 1. Полный вызов ex_intro с явно переданными параметрами A и B *)
      let term1 : le n n := @ex_intro nat (fun k : nat => k + n = n) 0 (add_0_left n) in

      (* Шаг 2. Раскрытие определения ex_intro - delta редукция *)
      let term2 : (exists nat (fun k : nat => k + n = n)) :=
          (fun (C : Prop) => fun (H : forall x : nat, (fun k : nat => k + n = n) x -> C) => H 0 (add_0_left n)) in

      (* Шаг 3. Внутренняя beta-редукция предиката: (fun k => k + n = n) x  ->  x + n = n *)
      let term3 : (forall (C : Prop), (forall x : nat, (x + n = n) -> C) -> C) :=
        (fun (C : Prop) =>
         fun H : forall x : nat, (x + n = n) -> C =>
           H 0 (add_0_left n)) in
      term3.

  Definition le_refl_short : forall n : nat, le n n :=
    fun n : nat => ex_intro 0 (add_0_left n).

  Definition le_0_n : forall n : nat, 0 <= n :=
    fun n : nat =>
    (* Нам нужно получить тип: exists nat (fun k : nat => k + 0 = n) *)
    (* Что эквивалентно: forall C : Prop, (forall k : nat, k + 0 = n -> C) -> C *)
    fun (C : Prop) (H : forall k : nat, k + 0 = n -> C) =>
      let H_eq : n + 0 = n := add_0_right n in
      H n H_eq.

  Definition le_trans : forall a b c : nat, a <= b -> b <= c -> a <= c :=
    fun (a b c : nat) (Le1 : a <= b) (Le2 : b <= c) =>
      (* Нам нужно вернуть x <= z, то есть:
         forall C : Prop, (forall k : nat, k + x = z -> C) -> C *)
      fun (C : Prop) (H : forall k : nat, k + a = c -> C) =>
      (* Распаковать a <= b (получить свидетеля k1 и утверждение k1 + x = y). *)

      _.

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
