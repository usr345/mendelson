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

End CoC_theorems.

(* This will FAIL to typecheck *)
Fail Definition False_type_broken : Type@{u} :=
  forall (P : Type@{u}), P.
