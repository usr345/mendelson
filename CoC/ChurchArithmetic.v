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
