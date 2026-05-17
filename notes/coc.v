Module CoC.

  Notation "A -> B" := (forall (_ : A), B)
                         (right associativity, at level 99).
  
  Definition False_CoC : Prop :=
    forall P : Prop, P.

  Definition not_CoC (P : Prop) : Prop :=
    P -> False_CoC.

  Notation "~ A" := (not_CoC A) (at level 75, right associativity).
  
  Definition And_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> B -> C) -> C.

  Notation "A /\ B" := (And_CoC A B) (at level 80, right associativity).

  Definition Or_CoC (A B : Prop) : Prop :=
    forall (C : Prop), (A -> C) -> (B -> C) -> C.

  Notation "A \/ B" := (Or_CoC A B) (at level 85, right associativity).

  Definition Eq_CoC {A : Type} (x y : A) : Prop :=
    forall (P : A -> Prop), P x -> P y.

  (* Notation "x == y" := (Eq_CoC x y) *)
  (*                       (at level 70, no associativity). *)
  (* Ex - это свойство предиката B на универсуме A, что B не пусто *)
  Definition Ex (A : Type) (B : A -> Prop) : Prop :=
    forall C : Prop, (forall x : A, B x -> C) -> C.

  Definition ex_intro {A : Type} {B : A -> Prop} (t : A) (p : B t) : Ex A B :=
    fun (C : Prop) => fun (H : forall x : A, B x -> C) => H t p.

(*
  Γ ⊢ t : ∃x : A, B Γ, x : A, p : B ⊢ u : C x !∈ Γ, C
  Γ ⊢ t C (fun (x : A)(p : B) ⇒ u) : C
*)
  Definition ex_elim {A : Type} {P : A -> Prop} {C : Prop}
    (H_exists : Ex A P)                    (* Γ ⊢ ∃x:A, P x *)
    (H_goal : forall x : A, P x -> C)      (* Γ ⊢ ∀x:A, P x → C *)
    : C := H_exists C H_goal.

  Definition Bool_CoC : Type := forall P : Type, P -> P -> P.

  Definition true_CoC : Bool_CoC := fun (P : Type) (t f : P) => t.
  Definition false_CoC : Bool_CoC := fun (P : Type) (t f : P) => f.

  Definition andb_CoC (b1 b2 : Bool_CoC) : Bool_CoC :=
    fun (P : Type) (t f : P) => b1 P (b2 P t f) f.

  Definition orb_CoC (b1 b2 : Bool_CoC) : Bool_CoC :=
    fun (P : Type) (t f : P) => b1 P t (b2 P t f).

  Definition notb_CoC (b : Bool_CoC) : Bool_CoC :=
    fun (P : Type) (t f : P) => b P f t.

  Lemma Eq_CoC_subst :
    forall (A : Type) (x y : A) (P : A -> Prop),
      Eq_CoC x y ->
      P x ->
      P y.
  Proof.
    intros A x y P H Px.
    apply H.
    exact Px.
  Qed.

  Definition eq_refl {U : Type} {x : U} : Eq_CoC x x :=
    fun (P : U -> Prop) (Px : P x) => Px.

  Lemma eq_symm {U : Type} {x y : U} : Eq_CoC x y -> Eq_CoC y x.
  Proof.
    unfold Eq_CoC.
    intro Heq.
    intros P Py.
    specialize (Heq (fun z => P z -> P x)).
    simpl in Heq.
    specialize (Heq (fun x => x)).
    specialize (Heq Py).
    exact Heq.
  Qed.
  
  Definition eq_trans {U : Type} {x y z : U} :
    Eq_CoC x y -> Eq_CoC y z -> Eq_CoC x z :=
    fun (Heq1 : Eq_CoC x y) (Heq2 : Eq_CoC y z) =>
    fun (P : U -> Prop) (Px : P x) => Heq2 P (Heq1 P Px).

  Lemma eq_congr :
    forall {A B : Type} (f : A -> B) x y,
      Eq_CoC x y -> Eq_CoC (f x) (f y).
  Proof.
    intros A B f x y H P Hfx.
    apply (H (fun a : A => P (f a))).
    exact Hfx.
  Qed.

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
    apply (@ex_intro Person is_happy bob bob_is_happy).
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

  Lemma and_comm {A B : Prop} : And_CoC A B -> And_CoC B A.
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

  Definition ex_falso (A : Prop) : A -> not_CoC A -> False_CoC :=
    fun (a : A) (na : not_CoC A) =>
      na a.

  Definition and_comm_dir {A B : Prop} : And_CoC A B -> And_CoC B A :=
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

  Definition or_intro_left : forall (A B : Prop), A -> Or_CoC A B :=
    fun (A B : Prop) (Ha : A) =>
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hac Ha.

  Definition or_intro_right : forall (A B : Prop), B -> Or_CoC A B :=
    fun (A B : Prop) (Hb : B) =>
      fun (C : Prop) (Hac : A -> C) (Hbc : B -> C) => Hbc Hb.

  Lemma or_comm (A B : Prop) : Or_CoC A B -> Or_CoC B A.
  Proof.
    intro Hor.
    unfold Or_CoC in Hor.
    unfold Or_CoC.
    intros C HBC HAC.
    specialize (Hor C HAC HBC).
    exact Hor.
  Qed.

  Definition or_comm_dir (A B : Prop) : Or_CoC A B -> Or_CoC B A :=
    fun (Hor : Or_CoC A B) =>
      fun (C : Prop) (fB : B -> C) (fA : A -> C) =>
        Hor C fA fB.

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

  Lemma eq_sym (U : Type) (x y : U) : Eq_CoC x y -> Eq_CoC y x.
  Proof.
    unfold Eq_CoC.
    intros Hxy P Py.
    apply (Hxy (fun z => P z -> P x)).
    - intro H.
      exact H.
    - exact Py.
  Qed.

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

  Definition deMorgan_disj_dir {A B : Prop} :
    not_CoC (Or_CoC A B) -> And_CoC (not_CoC A) (not_CoC B) :=
    fun (NotOr : not_CoC (Or_CoC A B)) =>
      fun (C : Prop) (H : (not_CoC A) -> (not_CoC B) -> C) =>
        H
          (fun (a : A) => NotOr (or_intro_left A B a))
          (fun (b : B) => NotOr (or_intro_right A B b)).

  Definition deMorgan_disj_back : forall {A B : Prop},
    And_CoC (not_CoC A) (not_CoC B) -> not_CoC (Or_CoC A B) :=
    fun (A B : Prop) =>
      fun (Hand : And_CoC (not_CoC A) (not_CoC B)) =>
        fun (Hor : Or_CoC A B) =>
          Hor False_CoC (and_elim1 Hand) (and_elim2 Hand).

  Theorem frobenius (A : Type) (P : A -> Prop) (Q : Prop) :
    Ex A (fun x => And_CoC (P x) Q) -> And_CoC (Ex A P) Q.
  Proof.
    intro Hex.
    unfold And_CoC.
    refine (fun (C : Prop) (g : Ex A P -> Q -> C) => ?[C]).
    unfold Ex in Hex.
    specialize (Hex C).
    unfold Ex in g.
    refine (Hex _).
    refine (fun (x : A) (Hand : And_CoC (P x) Q) => _).
    unfold And_CoC in Hand.
    specialize (Hand C).
    refine (Hand _).
    refine (fun (Hp : P x) (Hq : Q) => _).
    apply g.
    - intros C0 H1.
      specialize (H1 x).
      specialize (H1 Hp).
      exact H1.
    - exact Hq.
  Qed.

 Definition frobenius_dir (A : Type) (P : A -> Prop) (Q : Prop) :
    Ex A (fun x => And_CoC (P x) Q) -> And_CoC (Ex A P) Q :=
    fun (Hex : Ex A (fun x : A => And_CoC (P x) Q)) =>
      Hex (And_CoC (Ex A P) Q)
        (fun (x : A) (Hpq : And_CoC (P x) Q) =>
           let px := and_elim1 Hpq in
           let q := and_elim2 Hpq in
           and_intro (ex_intro x px) q).

 Definition frobenius_dir1 (A : Type) (P : A -> Prop) (Q : Prop) :
   Ex A (fun x => And_CoC (P x) Q) -> And_CoC (Ex A P) Q :=
   fun (Hex : Ex A (fun x : A => And_CoC (P x) Q)) =>
     Hex (And_CoC (Ex A P) Q) (
         fun (x : A) (Hpq : And_CoC (P x) Q) =>
           let Px := and_elim1 Hpq in
           let q := and_elim2 Hpq in
           let exP := ex_intro x Px in
           and_intro exP q
       ).

 Definition and_or_distr (A B C : Prop) : And_CoC A (Or_CoC B C) -> Or_CoC (And_CoC A B) (And_CoC A C) :=
   fun (H : And_CoC A (Or_CoC B C)) =>
          let a := and_elim1 H in
          let b_or_c := and_elim2 H in
          let case1 := (fun b : B =>
                         let a_and_b := and_intro a b in
                         or_intro_left (And_CoC A B) (And_CoC A C) a_and_b
                      ) in
          let case2 := (fun c : C =>
                         let a_and_c := and_intro a c in
                         or_intro_right (And_CoC A B) (And_CoC A C) a_and_c
                      ) in
          b_or_c (Or_CoC (And_CoC A B) (And_CoC A C)) case1 case2.

  Definition ex1 (A : Prop) : not_CoC (not_CoC (Or_CoC (not_CoC A) A)) := fun (H : not_CoC (Or_CoC (not_CoC A) A)) =>
                                                                           let conj1 := (deMorgan_disj_dir H) in                                                            (uncurry (ex_falso (not_CoC A))) (and_comm_dir conj1).

(*
  Definition and_or_distr (A B C : Prop) : And_CoC A (Or_CoC B C) -> Or_CoC (And_CoC A B) (And_CoC A C)
  Definition f_equal_CoC (U V : Type) (f : U -> V) (x y : U) :
    Eq_CoC U x y -> Eq_CoC V (f x) (f y) :=

Задача: Докажи через терм инволютивность отрицания для булевых значений: forall b : Bool_CoC, Eq_CoC Bool_CoC (notb_CoC (notb_CoC b)) b. Это потребует аккуратного применения b к соответствующим аргументам.
4. Закон Фробениуса (Часть 1)

Это классическая теорема из логики предикатов, которая в CoC доказывается напрямую.

Теорема: (∃x:A,P(x)∧Q)→(∃x:A,P(x))∧Q
Coq

  Следующий вызов: Попробуй формализовать числа Чёрча (Nat_CoC) и операцию plus_CoC. Доказательство того, что plus_CoC zero n = n через прямой терм — это отличная тренировка «умственной выносливости».
 *)

End CoC_theorems.

Section PeanoNat.
  Import CoC.

  Variable N : Type.
  (* 0 есть натуральное число *)
  Variable O : N.
  (* Для любого натурального числа n существует другое натуральное число (S n), называемое
     непосредственно следующим за n *)
  Variable S : N -> N.
  (* Для любого натурального n, 0 != S n *)
  Variable S_not_O : forall n : N, not_CoC (Eq_CoC O (S n)).

  (* S инъективна *)
  Variable S_inj :
    forall x y : N, Eq_CoC (S x) (S y) -> Eq_CoC x y.

  (* Принцип индукции *)
  Variable N_ind :
    forall P : N -> Prop, P O -> (forall n : N, P n -> P (S n)) -> forall n : N, P n.

  Variable add : N -> N -> N.
  Variable mul : N -> N -> N.

  Variable add_O_right : forall n : N,  Eq_CoC (add n O) n.
  Variable add_S_right : forall n m : N, Eq_CoC (add n (S m)) (S (add n m)).
  Variable mul_O_right : forall n : N, Eq_CoC (mul n O) O.
  Variable mul_S_right : forall n m : N, Eq_CoC (mul n (S m)) (add (mul n m) n).

  Declare Scope peano_nat_scope.
  Declare Custom Entry peano_nat_view.

  Notation "x" := x (x global, in custom peano_nat_view at level 0).
  Notation "( p )" := p (p custom peano_nat_view at level 5, in custom peano_nat_view at level 0).
  Notation "'$' p '$'" := p (format "'$' p '$'", p custom peano_nat_view at level 5).
  Notation "'0'" := O (in custom peano_nat_view at level 0, format "0").

  Notation "'Succ' x" := (S x)
                        (in custom peano_nat_view at level 1,
                            x custom peano_nat_view at level 1,
                            format "Succ  x").
  
  Notation "x + y" := (add x y)
                        (in custom peano_nat_view at level 3,
                            y custom peano_nat_view at level 3,
                            format "x  +  y").

  Notation "x * y" := (mul x y)
                        (in custom peano_nat_view at level 2,
                            y custom peano_nat_view at level 2,
                            format "x  *  y").
  
  (* Lemma Eq_CoC_subst : *)
  (*   forall (A : Type) (x y : A) (P : A -> Prop), *)
  (*     Eq_CoC x y -> *)
  (*     P x -> *)
  (*     P y. *)

  Theorem add_0_left : forall n : N, Eq_CoC $0 + n$ n.
  Proof.
    apply N_ind.
    - specialize (add_O_right O) as H0.
      exact H0.
    - intros n H0n.
      specialize (add_S_right O n) as H.
      specialize (eq_congr S (add O n) n H0n) as Heq1.
      specialize (eq_trans H Heq1) as Heq2.
      exact Heq2.
  Qed.

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
