Module CoC_core.

#[global] Notation "A -> B" := (forall (_ : A), B)
                      (right associativity, at level 99).

Definition False : Prop :=
  forall P : Prop, P.

Definition True : Prop :=
  forall P : Prop, P -> P.

Definition I : True :=
  fun (P : Prop) (p : P) => p.

Definition not (P : Prop) : Prop :=
  P -> False.

#[global] Notation "~ A" := (not A) (at level 75, right associativity).

(* Смысл определения: если высказывание C следует из A и B, и у нас есть оба конъюнкта, то мы можем получить C. *)
Definition conj (A B : Prop) : Prop :=
  forall C : Prop, (A -> B -> C) -> C.

#[global] Notation "A /\ B" := (conj A B) (at level 80, right associativity).

(* Закон исключения дизъюнкции *)
Definition disj (A B : Prop) : Prop :=
  forall (C : Prop), (A -> C) -> (B -> C) -> C.

#[global] Notation "A \/ B" := (disj A B) (at level 85, right associativity).

(* Эквивалентность на универсуме: два объекта эквивалентны,
   если они обладают одинаковыми свойствами
*)
Definition eq {A : Type} (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

#[global] Notation "x = y" := (eq x y) (at level 70, no associativity).

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

End CoC_core.

Module Bool.
  Import CoC_core.
  Definition bool : Type := forall P : Type, P -> P -> P.

  Definition true : bool := fun (P : Type) (t f : P) => t.
  Definition false : bool := fun (P : Type) (t f : P) => f.

  Definition conjb (b1 b2 : bool) : bool :=
    fun (P : Type) (t f : P) => b1 P (b2 P t f) f.

  Definition orb (b1 b2 : bool) : bool :=
    fun (P : Type) (t f : P) => b1 P t (b2 P t f).

  Definition notb_CoC (b : bool) : bool :=
    fun (P : Type) (t f : P) => b P f t.

  Definition true_ne_false : ~ (true = false) :=
    fun (Heq : true = false) =>
      (* 1. Define a predicate that evaluates to True if given true, *)
      (* conj False if given false. *)
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
  Import CoC_core.
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

Module CoC_theorems.
  Import CoC_core.

  Definition ex_not_forall (A : Type) (P : A -> Prop) (C : Prop) :
    exists A P -> ~ (forall x : A, ~ (P x)) :=
      fun (Hex : exists A P) (Hcontra : (forall x : A, ~ (P x))) =>
        let false : False := ex_elim Hex Hcontra in
      false.

  Definition conj_elim1 : forall {A B : Prop}, A /\ B -> A :=
    fun A B : Prop =>
      fun Hconj : A /\ B => Hconj A (fun (a : A) (b : B) => a).

  Definition conj_elim2 : forall {A B : Prop}, A /\ B -> B :=
    fun (A B : Prop) =>
     fun (Hconj : A /\ B) => Hconj B (fun (a : A) (b : B) => b).

  Definition conj_intro : forall {A B : Prop}, A -> B -> A /\ B :=
    fun A B : Prop =>
      fun (a : A) (b : B) =>
        fun (C : Prop) (HAB_C : A -> B -> C) => HAB_C a b.

  Definition conj_comm {A B : Prop} : A /\ B -> B /\ A :=
    fun (Hconj : A /\ B) =>
      fun (C : Prop) (f : B -> A -> C) =>
        Hconj C (fun (a : A) (b : B) => f b a).

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
    fun (Hdisj : A \/ B) =>
      fun (C : Prop) (fB : B -> C) (fA : A -> C) =>
        Hdisj C fA fB.

  Definition id : forall {A : Type}, A -> A :=
    fun (A : Type) (a : A) => a.

  Definition or_idempotent : forall {A : Prop}, A \/ A -> A :=
    fun (A : Prop) (Hdisj : A \/ A) =>
      Hdisj A id id.

  Definition conj_idempotent : forall {A : Prop}, A /\ A -> A :=
    fun (A : Prop) (Hconj : A /\ A) =>
      Hconj A (fun (a _ : A) => a).

  Definition uncurry: forall {A B C : Prop}, (A -> B -> C) -> (A /\ B) -> C :=
    fun (A B C : Prop) (HAB_C : A -> B -> C) (Hconj : A /\ B) =>
      Hconj C HAB_C.

  Definition curry : forall {A B C : Prop}, (A /\ B -> C) -> A -> B -> C :=
    fun (A B C : Prop) =>
      fun (f : (A /\ B) -> C) (a : A) (b : B) =>
        let Hconj : A /\ B := conj_intro a b in
        f Hconj.

  Definition contrapos : forall P Q : Prop, (P -> Q) -> ~Q -> ~P :=
    fun (P Q : Prop) (HP_Q : P -> Q) (nQ : ~Q) (p : P) => nQ (HP_Q p).

  Definition deMorgan_disj {A B : Prop} :
    ~ (A \/ B) -> ~ A /\ ~ B :=
    fun (NotDisj : ~ (A \/ B)) =>
      fun (C : Prop) (H : ~ A -> ~ B -> C) =>
        H
          (fun (a : A) => NotDisj (or_intro_left A B a))
          (fun (b : B) => NotDisj (or_intro_right A B b)).

  Definition deMorgan_disj_back : forall {A B : Prop},
    ~ A /\ ~ B -> ~ (A \/ B) :=
    fun (A B : Prop) =>
      fun (Hconj : ~ A /\ ~ B) =>
        fun (Hdisj : A \/ B) =>
          Hdisj False (conj_elim1 Hconj) (conj_elim2 Hconj).

  Definition frobenius_dir (A : Type) (P : A -> Prop) (Q : Prop) :
    exists A (fun x => (P x) /\ Q) -> (exists A P) /\ Q :=
      fun (Hex : exists A (fun x : A => (P x) /\ Q)) =>
        Hex ((exists A P) /\ Q) (
            fun (x : A) (Hpq : (P x) /\ Q) =>
              let Px : P x := conj_elim1 Hpq in
              let q : Q := conj_elim2 Hpq in
              let exP : exists A P := ex_intro x Px in
                        conj_intro exP q).

  Definition conj_or_distr (A B C : Prop) : A /\ (B \/ C) -> (A /\ B) \/ (A /\ C) :=
      fun (H : A /\ (B \/ C)) =>
        let a := conj_elim1 H in
        let b_or_c := conj_elim2 H in
        let case1 := (fun b : B =>
                      let a_conj_b := conj_intro a b in
                      or_intro_left (A /\ B) (A /\ C) a_conj_b
                   ) in
      let case2 := (fun c : C =>
                      let a_conj_c := conj_intro a c in
                      or_intro_right (A /\ B) (A /\ C) a_conj_c
                   ) in
      b_or_c (A /\ B \/ A /\ C) case1 case2.

  Definition ex1 (A : Prop) : ~ ~ (~ A \/ A) := fun (H : ~ ((~ A) \/ A)) =>
    let conj1 := (deMorgan_disj H) in
      (uncurry (ex_falso (~ A))) (conj_comm conj1).

(*
  Следующий вызов: Попробуй формализовать числа Чёрча (Nat_CoC) и операцию plus_CoC. Доказательство того, что plus_CoC zero n = n через прямой терм — это отличная тренировка «умственной выносливости».
 *)

End CoC_theorems.
