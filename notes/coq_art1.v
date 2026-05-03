From Coq Require Import Arith.
From Coq Require Import ZArith.
From Coq Require Import Bool.

Open Scope Z_scope.

Locate "_ * _".

Print Scope Z_scope.

Check 33%nat.

Print positive.

Check 33%Z.
Check (-12)%Z.

Check negb.

Check true.

Check (negb true).

Check (S (S (S O))).

Check (mult 5 7).

Check (Z.opp (Zmult 3 (Zminus (-5) (-8)))).

Check ((-4)*(7 - 7)).

Open Scope nat_scope.

Check (plus 3).

Check (Zmult (-5)).

Check Z.abs_nat.
Check (5 + Z.abs_nat (5 - 19)).

Fail Check (mult 3 (-45)%Z).

Check fun n : nat => (n*n*n)%nat.

Check fun n : nat => fun p : nat => fun z : Z => (Z_of_nat (n + p) + z)%Z.
Check fun (n p : nat) => fun z : Z => (Z_of_nat (n + p) + z)%Z.
Check fun (n p : nat) (z : Z) => (Z_of_nat (n + p) + z)%Z.

Check fun (f g : nat -> nat) (n : nat) => g (f n).

Check (fun n (z : Z) f => (n + (Z.abs_nat (f z))))%nat.

Check (fun f x => Z.abs_nat (f x x)).

(* Закон утверждения консеквента *)
Check (fun n _ : nat => n).

Check (fun _ : nat => 4).

(* Закон тождества как консеквент *)
Check (fun n p : nat => p).

Definition f1 := fun n p : nat =>
                  (let diff := n - p in
                   let square := diff*diff in
                    square * (square + n))%nat.

Check f1.

Parameter max_int : Z.
Definition min_int : Z := 1 - max_int.
Print min_int.

Open Scope Z_scope.
Definition cube := fun z : Z => z*z*z.
Definition cube2 (z : Z) : Z := z*z*z.
Definition cube3 z := z*z*z.

Check cube3.
Print cube3.

Definition Z_thrice (f : Z -> Z) (z : Z) : Z := f (f (f z)).
Definition plus9 := Z_thrice (Z_thrice (fun z : Z => z + 1)).

Compute (plus9 1).

Section binomial_def.
  Variables a b : Z.
  Definition binomial (z : Z) : Z := a*z + b.
  Section trinomial_def.
    Variable c : Z.
    Definition trinomial (z : Z) : Z := (binomial z)*z + c.
  End trinomial_def.
End binomial_def.

Reset binomial_def.
Section binomial_def.
  Variables a b : Z.
  Definition binomial (z : Z) : Z := a*z + b.
  Print binomial.
  Section trinomial_def.
    Variable c : Z.
    Definition trinomial (z : Z) : Z := (binomial z)*z + c.
  End trinomial_def.

  Print trinomial.
End binomial_def.

Print binomial.
Print trinomial.

Definition p1 : Z -> Z := binomial 5 (-3).
Definition p2 : Z -> Z := trinomial 1 0 (-1).
Definition p3 := trinomial 1 (-2) 1.

Section mab.
  Variables m a b : Z.
  Definition f := m*a*m.
  Definition g := m*(a + b).
End mab.

Reset mab.

Section f5.
  Variables a b c d e : Z.
  Definition f := a + b + c + d + e.
End f5.

Compute f 1 2 3 4 5.

Section h_def.
  Variables a b : Z.
  Let s : Z := a + b.
  Let d : Z := a - b.
  Definition h : Z := s*s + d*d.
End h_def.

Print h.

Definition Zsqr (z : Z) : Z := z*z.
Definition my_fun (f : Z -> Z) (z : Z) : Z := f (f z).
Eval cbv delta [my_fun Zsqr] in (my_fun Zsqr).
Eval cbv delta [my_fun] in (my_fun Zsqr).

Eval cbv beta zeta delta [h] in (h 56 78).

Eval cbv iota beta zeta delta in (h 56 78).
Eval vm_compute in (h 56 78).
Eval vm_compute in (my_fun Zsqr 3).

Definition polynom : Z -> Z := fun x : Z => 2*x*x + 3*x + 3.
Eval vm_compute in (polynom 2).
Eval vm_compute in (polynom 3).
Eval vm_compute in (polynom 4).

(*

Да. Здесь у Коq Art используются два очень специфических, но важных термина.1) Что такое SetВ Coq есть иерархия «типов типов». Сам тип типа называется sort.Set — один из таких sort-ов.Формально:если A : Set, то A — это не значение, а тип;если a : A, то a — это терм, то есть значение/конструктор/выражение, принадлежащее этому типу.Примеры:nat : Set bool : Set list nat : Set nat -> nat : Set То есть Set обычно содержит данные и вычислимые типы, а не логические утверждения в строгом смысле слова.2) Почему типы в Set называют «спецификациями»В этой книге слово specification означает просто:любой терм, чьим типом является Set.Иначе говоря, спецификация = тип данных.Это звучит непривычно, потому что в обычной информатике спецификация — это текстовое описание того, что должна делать программа.У Coq Art смысл другой: тип сам задаёт, что допустимо.Например:nat : Set Значит, nat — это спецификация.Она говорит: допустимы ровно натуральные числа.Еще:nat -> na
Еще:Coqnat -> nat : SetЭто тоже спецификация.
Она говорит: допустимы функции, которые берут 
натуральное число и возвращают натуральное число.

3) Почему термы с типом-спецификацией называют «программами»
Определение книги:Every term whose type is a specification 
is called a program.
То есть если у вас есть терм t, и его тип — это некоторая 
спецификация A : Set, то сам t : A называется program.
Примеры:
Coq
0 : nat
S 0 : nat
true : bool
fun x : nat => x : nat -> nat
fun x : nat => x + 1 : nat -> nat

Во всех этих случаях:nat, bool, nat -> nat — это спецификации;
0, true, fun x => x + 1 — это программы.
*)

Check Z.
Check ((Z -> Z) -> nat -> nat).

Set Printing Universes.
Check Set.
Check Type.

Definition Z_bin : Set := Z -> Z -> Z.

Check (fun z0 z1 : Z => 
        let d := z0 - z1 in d*d).

Definition Zdist2 : Z_bin :=
  fun z z0 : Z => let d := z - z0 in d*d.

Check Zdist2.
Check (nat -> nat).

Section my_nat.
  Variable N : Type.
  Variable z : N.
  Variable S : N -> N.

  Check z : N.
  Check S z : N.
  Check S (S z) : N.

  Variable le : N -> N -> Prop.
  Hypothesis lez : forall x : N, le z x.
  Hypothesis leS : forall x y : N, le x y -> le (S x) (S y).
  Theorem le_z_z : le z z.
  Proof.
    apply lez.
  Defined.

  Theorem leS_z_z : le (S z) (S z).
  Proof.
    apply leS.
    apply lez.
  Qed.

  Hypothesis ind : forall P : N -> Prop, P z -> (forall x : N, P x -> P (S x)) -> forall x : N, P x.
  Definition le_x_x : forall x : N, le x x := ind 
    (fun x : N => le x x) 
    le_z_z 
    (fun (x : N) (I : le x x) => leS x x I).

  Theorem le_x_x1 : forall x : N, le x x.
  Proof.
    intro x.
    refine (ind (fun x : N => le x x) _ _ x).
    - exact le_z_z.
    - intros x0 H.
      exact (leS x0 x0 H).
  Qed.
End my_nat.

Section domain.
  Variables (D : Set) (op : D -> D -> D) (sym : D -> D) (e : D).
  Let diff : D -> D -> D :=
    fun (x y : D) => op x (sym y).
End domain.

Section realization.
  Variables (A B : Set).
  Let spec : Set := (((A -> B) -> B) -> B) -> A -> B.
  Let realization : spec
    := fun (f : ((A -> B) -> B) -> B) (a : A) => f (fun (g : A -> B) => g a).
End realization.

Definition nat_fun_to_Z_fun : Set :=
  (nat -> nat) -> Z -> Z.

Definition absolute_fun : nat_fun_to_Z_fun :=
  fun f z => Z_of_nat (f (Z.abs_nat z)).

Definition always_0 : nat_fun_to_Z_fun :=
  fun _ _ => 0%Z.

Definition to_marignan : nat_fun_to_Z_fun :=
  fun _ _ => 1515%Z.

Definition ignore_f : nat_fun_to_Z_fun :=
  fun _ z => z.

Definition from_marignan : nat_fun_to_Z_fun :=
  fun f _ => Z_of_nat (f 1515%nat).

Definition Z_fun_to_nat_fun : Set :=
  (Z -> Z) -> nat -> nat.

Module CoC.
  (* Ex - это свойство предиката B на универсуме A, что B не пусто *)
  Definition Ex (A : Type) (B : A -> Prop) : Prop :=
    forall C : Prop, (forall x : A, B x -> C) -> C.

  Definition ex_intro (A : Type) (B : A -> Prop) (t : A) (p : B t) : Ex A B :=
    fun (C : Prop) => fun (H : forall x : A, B x -> C) => H t p.

(*
  Γ ⊢ t : ∃x : A, B Γ, x : A, p : B ⊢ u : C x 6∈ Γ, C
  Γ ⊢ t C (fun (x : A)(p : B) ⇒ u) : C
*)
  Definition ex_elim (A : Type) (P : A -> Prop) (C : Prop) 
    (H_exists : Ex A P)                    (* Γ ⊢ ∃x:A, P x *)
    (H_goal : forall x : A, P x -> C)      (* Γ ⊢ ∀x:A, P x → C *)
    : C := H_exists C H_goal.

  Definition False_CoC : Prop :=
    forall P : Prop, P.

  Definition not_CoC (P : Prop) : Prop :=
    P -> False_CoC.

  Definition And_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> B -> C) -> C.

  Definition Or_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> C) -> (B -> C) -> C.

  Definition Eq_CoC (A : Type) (x y : A) : Prop :=
    forall (P : A -> Prop), P x -> P y.
End CoC.

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
  Lemma someone_is_happy : Ex Person is_happy.
  Proof.
    (* This is exactly applying the term: fun C H => H bob bob_is_happy *)
    apply (ex_intro Person is_happy bob bob_is_happy).
  Qed.
End CoC_example.

Section CoC_theorems.
  Import CoC.

  Lemma ex_not_forall (A : Type) (P : A -> Prop) (C : Prop) :
    Ex A P -> not_CoC (forall x : A, not_CoC (P x)).
  Proof.
    intro Hex.
    unfold not_CoC.
    intro Hwit.
    unfold False_CoC.
    intro P0.
    unfold Ex in Hex.
    specialize (Hex P0).
    apply Hex.
    intros x Px.
    specialize (Hwit x Px).
    unfold False_CoC in Hwit.
    specialize (Hwit P0).
    exact Hwit.
  Qed.

  Lemma and_proj1 (A B : Prop) : And_CoC A B -> A.
  Proof.
    intro Hand.
    unfold And_CoC in Hand.
    specialize (Hand A).
    apply Hand.
    intros HA _.
    exact HA.
  Qed.

  Definition and_elim1 : forall {A B : Prop}, And_CoC A B -> A :=
    fun (A B : Prop) =>
      fun (Hand : And_CoC A B) => Hand A (fun (a : A) (b : B) => a).

  Lemma and_proj2 (A B : Prop) : And_CoC A B -> B.
  Proof.
    intro Hand.
    unfold And_CoC in Hand.
    specialize (Hand B).
    apply Hand.
    intros _ HB.
    exact HB.
  Qed.

  Definition and_elim2 : forall {A B : Prop}, And_CoC A B -> B :=
    fun (A B : Prop) =>
     fun (Hand : And_CoC A B) => Hand B (fun (a : A) (b : B) => b).

  Definition and_intro : forall {A B : Prop}, A -> B -> And_CoC A B :=
    fun (A B : Prop) =>
      fun (a : A) (b : B) => 
        fun (C : Prop) (HAB_C : A -> B -> C) => HAB_C a b.

  Lemma and_comm (A B : Prop) : And_CoC A B -> And_CoC B A.
  Proof.
    intro Hand.
    unfold And_CoC in Hand.
    unfold And_CoC.
    intros C H.
    apply Hand.
    intros HA HB.
    specialize (H HB HA).
    exact H.
  Qed.

  Definition and_comm_dir (A B : Prop) : And_CoC A B -> And_CoC B A :=
    fun (Hand : And_CoC A B) => 
      fun (C : Prop) (f : B -> A -> C) =>
        Hand C (fun (a : A) (b : B) => f b a).

  Theorem and_comm_refine (A B : Prop) : And_CoC A B -> And_CoC B A.
  Proof.
    refine (fun Hand : And_CoC A B => 
      fun (C : Prop) (f : B -> A -> C) => Hand C 
        (fun (a : A) (b : B) => _)).
    exact (f b a).
  Qed.

  Lemma or_comm (A B : Prop) : Or_CoC A B -> Or_CoC B A.
  Proof.
    intro Hor.
    unfold Or_CoC in Hor.
    unfold Or_CoC.
    intros C HBC HAC.
    specialize (Hor C HAC HBC).
    exact Hor.
  Qed.

  Definition or_intro_left : forall (A B : Prop), A -> Or_CoC A B :=
    fun (A B : Prop) (Ha : A) => 
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hac Ha.

  Definition or_intro_right : forall (A B : Prop), B -> Or_CoC A B :=
    fun (A B : Prop) (Hb : B) => 
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hbc Hb.

  Definition uncurry : forall {A B C : Prop}, (A -> B -> C) -> (And_CoC A B) -> C :=
    fun (A B C : Prop) =>
      fun (f_abc : A -> B -> C) (Hconj : And_CoC A B) =>
        f_abc (and_elim1 Hconj) (and_elim2 Hconj).

  Definition id : forall A : Type, A -> A :=
    fun (A : Type) (a : A) => a.

  Definition or_idempotent : forall {A : Prop}, Or_CoC A A -> A :=
    fun (A : Prop) (Hor : Or_CoC A A) => 
      Hor A (id A) (id A).

  Definition and_idempotent : forall {A : Prop}, And_CoC A A -> A :=
    fun (A : Prop) (Hand : And_CoC A A) => 
      Hand A (fun (a _ : A) => a).

  Definition or_comm_dir (A B : Prop) : Or_CoC A B -> Or_CoC B A :=
    fun (Hor : Or_CoC A B) =>
      fun (C : Prop) (fB : B -> C) (fA : A -> C) =>
        Hor C fA fB.

  Lemma eq_sym (U : Type) (x y : U) : Eq_CoC U x y -> Eq_CoC U y x.
  Proof.
    unfold Eq_CoC.
    intros Hxy P Py.
    apply (Hxy (fun z => P z -> P x)).
    - intro H.
      exact H.
    - exact Py.
  Qed.

  Definition eq_trans_dir (U : Type) (x y z : U) : 
    Eq_CoC U x y -> Eq_CoC U y z -> Eq_CoC U x z :=
    fun (Heq1 : Eq_CoC U x y) (Heq2 : Eq_CoC U y z) =>
      fun (P : U -> Prop) (Px : P x) => Heq2 P (Heq1 P Px).

  Definition contrapos (A B : Prop) : (A -> B) -> not_CoC B -> not_CoC A :=
    fun (Impl : A -> B) (notB : not_CoC B) =>
      fun (Ha : A) => notB (Impl Ha).

  Theorem deMorgan_disj : forall A B : Prop, not_CoC (Or_CoC A B) -> And_CoC (not_CoC A) (not_CoC B).
  Proof.
    intros A B H.
    unfold And_CoC.
    intros C H1.
    unfold not_CoC in H.
    unfold Or_CoC in H.
    apply H1.
    - unfold not_CoC.
      intro a.
      apply H.
      intros C0 A_C0 B_C0.
      specialize (A_C0 a).
      exact A_C0.
    - unfold not_CoC.
      intro b.
      apply H.
      intros C0 A_C0 B_C0.
      specialize (B_C0 b).
      exact B_C0.
  Qed.

  Definition deMorgan_disj_dir (A B : Prop) : 
    not_CoC (Or_CoC A B) -> And_CoC (not_CoC A) (not_CoC B) :=
    fun (NotOr : not_CoC (Or_CoC A B)) =>
      fun (C : Prop) (H : (not_CoC A) -> (not_CoC B) -> C) =>
        H 
          (fun (a : A) => NotOr (or_intro_left A B a))
          (fun (b : B) => NotOr (or_intro_right A B b))
        .

  Definition deMorgan_disj_back : forall (A B : Prop),
    And_CoC (not_CoC A) (not_CoC B) -> not_CoC (Or_CoC A B) :=
    fun (A B : Prop) =>
      fun (Hand : And_CoC (not_CoC A) (not_CoC B)) =>
        fun (Hor : Or_CoC A B) => 
          Hor False_CoC (and_elim1 Hand) (and_elim2 Hand).

 Definition Or_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> C) -> (B -> C) -> C.

fun (C1 : Prop) (f1 : A -> C1) (f2: B -> C1) => H ?1 ?2

Definition False_CoC : Prop :=
    forall P : Prop, P.

 Definition And_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> B -> C) -> C.


  Definition not_CoC (P : Prop) : Prop :=
    P -> False_CoC.


  $\neg (A \lor B) \to \neg A \land \neg B$


End CoC_theorems.
  Definition Eq_CoC (A : Type) (x z : A) : Prop :=
    forall (P : A -> Prop), P x -> P z.

 Eq_CoC (A : Type) (y z : A) : Prop :=
    forall (P : A -> Prop), P y -> P z.

Universe u.

(* This will FAIL to typecheck *)
Fail Definition False_type_broken : Type@{u} := 
  forall (P : Type@{u}), P.