Module CoC.

  Notation "A -> B" := (forall (_ : A), B)
                         (right associativity, at level 99).

  Definition False : Prop :=
    forall P : Prop, P.

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
  Definition exists (A : Type) (B : A -> Prop) : Prop :=
    forall C : Prop, (forall x : A, B x -> C) -> C.

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
    forall {A B : Type} (f : A -> B) (x y : A),
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

  (* Definition true_ne_false : ~ (true = false) := *)
  (*   _. *)
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

Section PeanoNat.
  Import CoC.

  Variable nat : Type.
  (* 0 есть натуральное число *)
  Variable O : nat.

  Notation "'0'" := O (at level 0, format "0").
  (* Для любого натурального числа n существует другое натуральное число (S n), называемое
     непосредственно следующим за n *)
  Variable S : nat -> nat.
  (* Для любого натурального n, 0 != S n *)
  Variable S_not_O : forall n : nat, ~ (0 = (S n)).

  (* S инъективна *)
  Variable S_inj :
    forall x y : nat, (S x) = (S y) -> x = y.

  (* Принцип индукции *)
  Variable N_ind :
    forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n.

  Variable add : nat -> nat -> nat.
  Variable mul : nat -> nat -> nat.

  Notation "x + y" := (add x y) (at level 50, left associativity).
  Notation "x * y" := (mul x y) (at level 40, left associativity).

  Variable add_O_right : forall n : nat,  n + 0 = n.
  Variable add_S_right : forall n m : nat, n + (S m) = S (n + m).
  Variable mul_O_right : forall n : nat, n * O = O.
  Variable mul_S_right : forall n m : nat, n * (S m) = (n * m) + n.

  Definition add_0_left : forall n : nat, 0 + n = n :=
    fun (n : nat) =>
      let Base : 0 + 0 = 0 := add_O_right 0 in
      let Step : forall n : nat, 0 + n = n -> 0 + S n = S n :=
        (fun (n : nat) (IH : 0 + n = n) =>
        let H : 0 + (S n) = S (0 + n) := add_S_right O n in
        let H1 : 0 + n = n -> S (0 + n) = S n := eq_congr S (O + n) n in
        let H2 : S (0 + n) = S n := H1 IH in
        let H3 : 0 + S n = S n := eq_trans H H2 in
        H3)
          in
      N_ind (fun n : nat => 0 + n = n) Base Step n.
         
  Theorem add_S_left : forall x y : N, Eq_CoC (add (S x) y) (S (add x y)).
  Proof.
    intros x y.
    revert x.
    apply N_ind with
      (P := fun y => forall x : N, Eq_CoC (add (S x) y) (S $x+y$))
      (n := y).
    - intro x.
      specialize (add_O_right x) as Heq1.
      specialize (eq_congr S $x + O$ x Heq1) as Heq2.
      apply eq_symm in Heq2.
      apply @eq_trans with
        (y := (S x)).
      2 : { exact Heq2. }
      specialize (add_O_right (S x)) as Heq3.
      exact Heq3.
    - intros n IH.
      intro x.
      specialize (add_S_right (S x) n) as Heq1.
      apply eq_symm.
      apply @eq_trans with
        (y := (S (add (S x) n))).
      2 : {
        apply eq_symm.
        exact Heq1.
      }
      specialize (IH x).
      apply eq_symm in IH.
      specialize (eq_congr S (add x (S n)) (add (S x) n)) as Himpl.
      apply Himpl.
      apply @eq_trans with
        (y := S $x+n$).
      2 : {
        exact IH.
      }
      specialize (add_S_right x n) as Heq2.
      exact Heq2.
  Qed.

  Theorem add_comm : forall x y : N, Eq_CoC $x + y$ $y + x$.
  Proof.
    intro x.
    apply N_ind with
      (P := fun x => forall y : N, Eq_CoC $x + y$ $y + x$)
      (n := x).
    - intro y.
      unfold Eq_CoC.
      intros P H0y.
      specialize (add_O_right y) as Heq1.
      apply eq_symm in Heq1.
      apply Heq1.
      specialize (add_0_left y) as Heq2.
      unfold Eq_CoC in Heq2.
      specialize (Heq2 P H0y).
      exact Heq2.
    - intros n IH.
      intro y.
      specialize (add_S_right y n) as Heq1.
      apply eq_symm in Heq1.
      apply @eq_trans with
        (y := S $y+n$).
      2 : exact Heq1.
      specialize (add_S_left n y) as Heq2.
      apply @eq_trans with
        (y := S $n+y$).
      1 : { exact Heq2. }
      specialize (IH y).
      apply eq_congr.
      exact IH.
  Qed.

  Theorem add_assoc : forall x y z : N, Eq_CoC $(x + y) + z$ $x + (y + z)$.
  Proof.
    intro x.
    apply N_ind with
      (P := fun x => forall y z : N, Eq_CoC $(x + y) + z$ $x + (y + z)$)
      (n := x).
    - (* x = O *)
      intros y z.
      unfold Eq_CoC.
      intros P H.
      specialize (add_0_left y) as Heq1.
      specialize (eq_congr (fun n : N => add n z) (add O y) y) as Heq2.
      specialize (Heq2 Heq1).
      cbn in Heq2.
      specialize (add_0_left (add y z)) as Heq3.
      apply eq_symm in Heq3.
      unfold Eq_CoC in Heq3.
      specialize (Heq3 P).
      apply Heq3.
      apply Heq2.
      exact H.
    - (* x = S x *)
      intros n IH.
      intros y z.
      specialize (IH y z).
      specialize (add_S_left n (add y z)) as Heq1.
      apply eq_symm in Heq1.
      apply @eq_trans with
        (y := S (add n (add y z))).
      2 : exact Heq1.
      specialize (add_S_left n y) as H2.
      specialize (eq_congr (fun n : N => add n z) (add (S n) y) (S (add n y))) as H3.
      cbn in H3.
      specialize (H3 H2).
      apply @eq_trans with
        (y := add (S (add n y)) z).
      1 : exact H3.
      specialize (add_S_left (add n y) z) as H4.
      apply @eq_trans with
        (y := S (add (add n y) z)).
      1 : exact H4.
      apply eq_congr.
      exact IH.
  Qed.

  Lemma mul_O_left : forall x : N, Eq_CoC O (mul O x).
  Proof.
    intro x.
    apply N_ind with
      (P := fun x => Eq_CoC O (mul O x))
      (n := x).
    - specialize (mul_O_right O) as H0.
      apply eq_symm in H0.
      exact H0.
    - intros n IH.
      specialize (mul_S_right O n) as H1.
      specialize (add_O_right (mul O n)) as H2.
      specialize (eq_trans H1 H2) as H3.
      apply eq_symm in H3.
      specialize (eq_trans IH H3) as H4.
      exact H4.
  Qed.

  Theorem distributivity : forall a b c : N, Eq_CoC $a * (b + c)$ $a*b + a*c$.
  Proof.
    intros a b c.
    apply N_ind with
      (P := fun x => Eq_CoC $a * (b + x)$ $a*b + a*x$)
      (n := c).
    - specialize (add_O_right b) as H1.
      specialize (eq_congr (fun n : N => mul a n) $b + 0$ b) as H2.
      cbn in H2.
      specialize (H2 H1).
  (* Variable add_O_right : forall n : N,  Eq_CoC (add n O) n. *)
  (* Variable add_S_right : forall n m : N, Eq_CoC (add n (S m)) (S (add n m)). *)
  (* Variable mul_O_right : forall n : N, Eq_CoC (mul n O) O. *)
  (* Variable mul_S_right : forall n m : N, Eq_CoC (mul n (S m)) (add (mul n m) n). *)
  (* add_S_left : forall x y : N, Eq_CoC (add (S x) y) (S (add x y)). *)

  Theorem mul_S_left : forall n m : N, Eq_CoC $(Succ m) * n$ $n + (n * m)$.
  Proof.
    intro n.
    apply N_ind with
      (P := fun x => forall m : N, Eq_CoC $Succ m * x$ $x + x * m$)
      (n := n).
    - intro m.
      specialize (mul_O_right (S m)) as H1.
      specialize (mul_O_left m) as H2.
      specialize (add_0_left $0 * m$) as H3.
      apply eq_symm in H3.
      specialize (eq_trans H2 H3) as H4.
      specialize (eq_trans H1 H4) as H5.
      exact H5.
    - intros x IH.
      intro m.
      specialize (IH m).
      specialize (mul_S_right (S m) x) as H1.
      specialize (add_S_left x $Succ x * m$) as H2.
      specialize (add_comm $Succ x * m$ $Succ x$) as H3.
      apply @eq_trans with
        (y := $Succ x * m + Succ x$).
      2: exact H3.


      $Succ m * x + Succ m$
      specialize (eq_congr (fun n : N => S n) $Succ m * x$ $x + x * m$) as H2.
      cbn in H2.
      specialize (H2 IH).

    (* intros n m. *)
    (* revert n. *)
    (* apply N_ind with *)
    (*   (P := fun x => forall n : N, Eq_CoC $Succ x * n$ $n + n * x$) *)
    (*   (n := m). *)
    (* - admit. *)
    (* - intros x IH. *)
    (*   intro n. *)
    (*   specialize (mul_S_right n (S x)) as H1. *)
    (*   specialize (add_comm $n * Succ x$ n) as H2. *)
    (*   specialize (eq_trans H1 H2) as H3. *)
    (*   clear H2. *)
    (*   (1 + (1 + x)) * n = n + (1 + x) * n *)
    (*   (1 + x) * (1 + n) = (1 + x) * n + (1 + n) *)

  Theorem mul_comm : forall x y : N, Eq_CoC $x * y$ $y * x$.
  Proof.
    intro x.
    apply N_ind with
      (P := fun x => forall y : N, Eq_CoC $x * y$ $y * x$)
      (n := x).
    - intro y.
      specialize (mul_O_right y) as H0_right.
      specialize (mul_O_left y) as H0_left.
      specialize (eq_trans H0_right H0_left) as H.
      apply eq_symm.
      exact H.
    - intros n IH.
      intro y.
      specialize (mul_S_right y n) as H1.

End PeanoNat.


(* Module ChurchBool. *)
(*   Import CoC. *)

(*   Theorem and_comm (b1 b2 : Bool_CoC) : Eq_CoC Bool_CoC (andb_CoC b1 b2) (andb_CoC b2 b1). *)
(*   Proof. *)
(*     unfold Eq_CoC. *)
(*     intros P Hand. *)
(*     unfold andb_CoC in Hand. *)
(*     unfold andb_CoC. *)
(*     unfold Bool_CoC in P. *)
(* End ChurchBool. *)

(*   Definition Bool_CoC : Type := forall P : Type, P -> P -> P. *)

(*   Definition true_CoC : Bool_CoC := fun (P : Type) (t f : P) => t. *)
(*   Definition false_CoC : Bool_CoC := fun (P : Type) (t f : P) => f. *)

(*   Definition andb_CoC (b1 b2 : Bool_CoC) : Bool_CoC := *)
(*     fun (P : Type) (t f : P) => b1 P (b2 P t f) f. *)

(*   Definition orb_CoC (b1 b2 : Bool_CoC) : Bool_CoC := *)
(*     fun (P : Type) (t f : P) => b1 P t (b2 P t f). *)

(*   Definition notb_CoC (b : Bool_CoC) : Bool_CoC := *)
(*     fun (P : Type) (t f : P) => b P f t. *)

(* Local Variables: *)
(* coq-prog-args: ("-noinit") *)
(* End: *)
