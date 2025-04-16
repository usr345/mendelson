Require Import Classical.
From Mendelson Require Import Formula.

Module Syntactic.
(* We now come to main definitions. We first define a type
   Γ |- A whose elements are derivations of formula A
   from assumptions Γ. These are presented as derivation trees,
   rather than more traditional lists.

   Note the difference between declaring that Γ |- A
   is a Prop vs. a Type:

   - if Γ |- A is a Prop, then it is expresses *provability*
   - if Γ |- A is a Type, then it expresses *proof derivations*

   The practical difference is this: if Γ |- A is a Type, then
   its element is a derivation tree which can be freely inspected
   and used; but if Γ |- A is a Prop, then its elements are
   (abstract) witnesses of provability that can only be expected
   for the purpose of constructing an element of Prop.
 *)
Definition f_axiom1 {atom : Set} (A B : @formula atom) : formula :=
  $A -> (B -> A)$.

Definition f_axiom2 {atom : Set} (A B C : @formula atom) : formula :=
  $(A -> B -> C) -> (A -> B) -> (A -> C)$.

Definition f_axiom3 {atom : Set} (A B : @formula atom) : formula :=
  $(~ B -> ~ A) -> (~ B -> A) -> B$.

Reserved Notation "Γ |- A" (at level 98).
Inductive entails {atom : Set} (Γ : @formula atom -> Prop) : @formula atom -> Type :=
  | hypo : forall A, A ∈ Γ -> Γ |- A (* every hypothesis is provable *)
  | axiom1 : forall A B , Γ |- f_axiom1 A B
  | axiom2 : forall A B C, Γ |- f_axiom2 A B C
  | axiom3 : forall A B, Γ |- f_axiom3 A B
  | mp : forall A B, Γ |- B -> Γ |- $B -> A$ -> Γ |- A (* modus ponens *)
where "Γ |- A" := (entails Γ A).

(* It is convenient to make some parameters implicit. *)
Arguments hypo {_} {_} _.
Arguments axiom1 {_} {_} _ _.
Arguments axiom2 {_} {_} _ _ _.
Arguments axiom3 {_} {_} _ _.
Arguments mp {_} {_} {_} (_).

(* Если $\Gamma \subseteq \Delta$ и $\Gamma \vdash A$, то $\Delta \vdash A$ *)
Theorem weaken {atom : Set} (Γ : @formula atom -> Prop) Δ A : Γ ⊆ Δ -> Γ |- A -> Δ |- A.
Proof.
  intros S H.
  induction H as [A H|A B|A B C|A B|A B H1 H2 IH1 IH2].
  (* Пусть A ∈ Γ *)
  - unfold subset in S.
    specialize (S A H).
    apply hypo.
    exact S.
  - apply (axiom1 A B).
  - apply (axiom2 A B C).
  - apply (axiom3 A B).
  - pose proof (mp B H2 IH2) as H3.
    exact H3.
Qed.

(* Here are some basic observation about |-. *)
(* Лемма 1.7. $\vdash_L A \supset A$ для любой формулы A. *)
Lemma imply_self {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A -> A$.
Proof.
  (* (1) $(A \supset ((A \supset A) \supset A)) \supset ((A \supset (A \supset A)) \supset (A \supset A))$ --- подстановка в схему аксиом A2 *)
  pose proof (@axiom2 _ Γ A $A -> A$ A) as H1.
  unfold f_axiom2 in H1.
  (* (2) $A \supset ((A \supset A) \supset A)$ --- схема аксиом A1 *)
  pose proof (@axiom1 _ Γ A $A -> A$) as H2.
  unfold f_axiom1 in H2.
  (* (3) $((A \supset (A \supset A)) \supset (A \supset A))$ --- из (1) и (2) по MP *)
  specialize (mp $A -> (A -> A) -> A$ H2 H1) as H3.
  (* (4) $A \supset (A \supset A)$ --- схема аксиом A1 *)
  pose proof (@axiom1 _ Γ A A) as H4.
  unfold f_axiom1 in H4.
  (* (5) $A \supset A$ --- из (3) и (4) по MP *)
  specialize (mp $A -> (A -> A)$ H4 H3) as H5.
  exact H5.
Qed.

(* "extend Γ A" is the set Γ ∪ {A}. *)
Definition extend {atom : Set} (Γ : @formula atom -> Prop) (A : formula) : formula -> Prop := fun B => or (B ∈ Γ) (A = B).

Notation "Γ ,, A" := (extend Γ A) (at level 32, left associativity).

(* Множество Gamma является подмножеством расширения (Gamma,, A) *)
Lemma subset_extend {atom : Set} {Γ : @formula atom -> Prop} {A} : subset Γ (extend Γ A).
Proof.
  unfold subset, extend.
  intros A0 H.
  unfold elem.
  left.
  exact H.
Qed.

(* We need this lemma in the deduction theorem. *)
Lemma drop_antecedent {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- B -> Γ |- $A -> B$.
Proof.
  intro H.
  (* 1. $B \supset (A \supset B)$ --- схема аксиом A1 *)
  pose proof (@axiom1 _ Γ B A) as H1.
  unfold f_axiom1 in H1.
  (* 2. $A \supset B$ --- из H и H1 по MP *)
  specialize (@mp _ _ _ B H H1) as H2.
  exact H2.
Qed.

(* We conclude with the proof of the deduction theorem, just to show
   that it is quite painless to formalize. *)
Theorem deduction {atom : Set} {Γ : @formula atom -> Prop} {A B} : extend Γ A |- B -> Γ |- $A -> B$.
Proof.
  intro H.
  induction H as [B H|?|?|?|B C H1 IH1 H2 IH2].
  (* Пусть B является элементом Γ,, A *)
  - destruct (formula_eq A B) as [Heq|Hneq].
    (* Если B = A, применяем лемму imply_self *)
    + rewrite Heq.
      apply imply_self.
    (* Если B != A, по аксиоме 1 получаем формулу *)
    (* $B \supset (A \supset B)$ *)
    + pose proof (@axiom1 _ Γ B A) as H1.
      unfold f_axiom1 in H1.
      (* Поскольку B != A, B содержится в Γ *)
      assert (H2: Γ |- B).
      {
        apply hypo.
        unfold extend in H.
        unfold elem in H.
        destruct H as [Hin|Heq].
        * unfold elem.
          exact Hin.
        * apply Hneq in Heq.
          contradiction Heq.
      }

      (* По MP из H1 : Γ |- $B -> (A -> B)$ *)
      (* и H2 : Γ |- B получаем Γ |- $A -> B$ *)
      specialize (mp B H2 H1) as H3.
      exact H3.
  - (* Пусть B является аксиомой *)
    apply drop_antecedent.
    apply axiom1.
  - apply drop_antecedent.
    apply axiom2.
  - apply drop_antecedent.
    apply axiom3.
  - (* Modus Ponens:
       Пусть B получена по MP из 2-х формул C и $C -> B$, и пусть они доказуемы в контексте (Γ,, A):
       H1 : Γ,, A |- B
       H2 : Γ,, A |- $B -> C$

       Пусть истинны индуктивные гипотезы:
       IH1 : Γ |- $A -> B$
       IH2 : Γ |- $A -> B -> C$
    *)

    (* По аксиоме 2: $(A -> (C -> B)) -> ((A -> C) -> (A -> B))$ *)
    + pose proof (@axiom2 _ Γ A C B) as H3.
      unfold f_axiom2 in H3.

      (* По MP из IH2 : Γ |- $A -> C -> B$ *)
      (* и H3 : Γ |- $(A -> C -> B) -> (A -> C) -> A -> B$ *)
      specialize (mp $A -> C -> B$ IH2 H3) as H4.

      (* MP *)
      (* IH1 : Γ |- $A -> C$ *)
      (*  H4 : Γ |- $(A -> C) -> A -> B$ *)
      specialize (mp $A -> C$ IH1 H4) as H5.
      exact H5.
Qed.

(* Now we can define a tactic that does the above steps.
   Note the difference between the tactic "hypo" and the constructor "hypo"!
   If you type "hypo" in tactic mode, it will use the tactic defined below,
   but if you type "apply hypo" it will use the constructor hypo. *)
Ltac hypo := (apply hypo ; cbv in * ; auto 6).

(* Упражнения *)
Lemma T1_7ex1 {atom : Set} (Γ : @formula atom -> Prop) A : Γ |- $(~A -> A) -> A$.
Proof.
  (* 1 *)
  pose proof (@axiom3 _ Γ A A) as H1.
  unfold f_axiom3 in H1.
  (* 2 *)
  pose proof (@imply_self _ Γ $~A$) as H2.
  (* 3 *)
  assert (H3 : Γ |- $(~A -> A) -> A$).
  apply (@mp _ Γ _ $~A -> ~A$ H2 H1).
  (* 4 *)
  exact H3.
Qed.

Lemma T1_7ex2 {atom : Set} (Γ : @formula atom -> Prop) A B C : Γ ,, $A -> B$ ,, $B -> C$ |- $A -> C$.
Proof.
  (* 1 *)
  pose proof (@axiom1 _ (Γ ,, $A -> B$ ,, $B -> C$) $B -> C$ A) as H1.
  unfold f_axiom1 in H1.
  (* 2 *)
  assert (H2 : Γ,, $A -> B$,, $B -> C$ |- $A -> (B -> C)$).
  apply mp with (B := $B -> C$).
  hypo.
  apply H1.
  (* 3  *)
  pose proof (@axiom2 _ (Γ ,, $A -> B$ ,, $B -> C$) A B C) as H3.
  unfold f_axiom2 in H3.
  (* 4 *)
  assert (H4 : Γ,, $A -> B$,, $B -> C$ |- $(A -> B) -> A -> C$).
  apply (@mp _ (Γ,, $A -> B$,, $B -> C$) _ $A -> B -> C$ H2 H3).
  (* 5 *)
  assert (H5 : Γ,, $A -> B$,, $B -> C$ |- $A -> C$).
  apply mp with (B := $A -> B$).
  hypo.
  exact H4.
  (* 6 *)
  exact H5.
Qed.

Lemma T1_7ex3 {atom : Set} (Γ : @formula atom -> Prop) A B C : Γ ,, $A -> (B -> C)$ |- $B -> (A -> C)$.
Proof.
  (* 1 *)
  pose proof (@axiom2 _ (Γ,, $A -> (B -> C)$) A B C) as H1.
  (* 2 *)
  assert (H2 : Γ,, $A -> (B -> C)$ |- $(A -> B) -> (A -> C)$).
  apply mp with (B := $A -> (B -> C)$).
  hypo.
  exact H1.
  (* 3 *)
  pose proof (@axiom1 _ (Γ,, $A -> (B -> C)$) $((A -> B) -> (A -> C))$ B) as H3.
  (* 4 *)
  assert (H4 : Γ,, $A -> (B -> C)$ |- $B -> ((A -> B) -> (A -> C))$).
  apply mp with (B := $((A -> B) -> (A -> C))$).
  exact H2.
  exact H3.
  (* 5 *)
  pose proof (@axiom2 _ (Γ,, $A -> (B -> C)$) B $A -> B$ $A -> C$) as H5.
  (* 6 *)
  assert (H6 : Γ,, $A -> (B -> C)$ |- $(B -> (A -> B)) -> (B -> (A -> C))$).
  apply mp with (B := $B -> (A -> B) -> A -> C$).
  exact H4.
  exact H5.
  (* 7 *)
  pose proof (@axiom1 _ (Γ,, $A -> B -> C$) B A) as H7.
  (* 8 *)
  assert (H8 : Γ,, $A -> (B -> C)$ |- $B -> A -> C$).
  apply (@mp _ (Γ,, $A -> B -> C$) _ $B -> A -> B$ H7 H6).
  (* 9 *)
  exact H8.
Qed.

Corollary transitivity {atom : Set} {Γ : @formula atom -> Prop} {A} B {C} :
  Γ |- $A -> B$ -> Γ |- $B -> C$ -> Γ |- $A -> C$.
Proof.
  intros H1 H2.
  apply (mp $A -> B$).
  - exact H1.
  - apply (mp $A -> B -> C$).
    + apply drop_antecedent.
      exact H2.
    + apply axiom2.
Qed.

(* теорема, обратная теореме дедукции *)
Lemma impl_intro {atom : Set} {Γ : @formula atom -> Prop} {A B} :
  Γ |- $A -> B$ -> extend Γ A |- B.
Proof.
  intro H.
  apply (mp A).
  - hypo.
  (* weaken Γ Δ A : Γ ⊆ Δ -> Γ |- A -> Δ |- A. *)
  - apply (weaken Γ).
    + apply subset_extend.
    + exact H.
Qed.

Corollary flip {atom : Set} {Γ : @formula atom -> Prop} {A} B {C} :
  Γ |- $A -> B -> C$ -> Γ |- B -> Γ |- $A -> C$.
Proof.
  intros H1 H2.
  apply deduction.
  apply (mp B).
  - apply (weaken Γ).
    + apply subset_extend.
    + exact H2.
  - apply impl_intro.
    exact H1.
Qed.

Corollary meta_flip {atom : Set} {Γ : @formula atom -> Prop} {A} B {C} :
  Γ |- $A -> B -> C$ -> Γ |- $B -> A -> C$.
Proof.
  intros H.
  apply deduction.
  apply deduction.
  assert (H1 : Γ,, B,, A |- $B -> C$).
  apply mp with (B := A).
  hypo.
  apply (weaken Γ).
  - unfold subset.
    intros.
    unfold extend.
    unfold elem.
    unfold elem in H0.
    auto.
  - exact H.
  - apply mp with (B := B).
    + hypo.
    + exact H1.
Qed.

(* 1.10 a *)
Theorem neg_neg_pos {atom : Set} {Γ : @formula atom -> Prop} B : Γ |- $~~B -> B$.
Proof.
  apply (transitivity $~B -> ~~B$).
  - apply axiom1.
  - apply (flip $~B -> ~B$).
    + apply axiom3 with (B := B) (A := $~B$).
    + apply imply_self.
Qed.

(* 1.10 b *)
Theorem pos_neg_neg {atom : Set} {Γ : @formula atom -> Prop} B : Γ |- $B -> ~~B$.
Proof.
  apply transitivity with (B := $~ ~ ~ B -> B$).
  - apply axiom1.
  - apply mp with (B := $~ ~ ~ B -> ~ B$).
    + apply neg_neg_pos with (B := $~B$).
    + exact (axiom3 B $~~B$).
Qed.

Theorem meta_neg_neg_pos {atom : Set} {Γ : @formula atom -> Prop} B : (Γ |- $~~B$) -> (Γ |- B).
Proof.
  intro H.
  set (H1 := @neg_neg_pos atom Γ B).
  apply mp with (B := $~~ B$).
  - assumption.
  - assumption.
Qed.

Theorem meta_pos_neg_neg {atom : Set} {Γ : @formula atom -> Prop} B : (Γ |- B) -> (Γ |- $~~B$).
Proof.
  intro H.
  set (H1 := @pos_neg_neg atom Γ B).
  apply mp with (B := B).
  - assumption.
  - assumption.
Qed.

(* 1.10 c *)
Theorem neg_a_impl_a_b {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $~A -> A -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply mp with (B := $~B -> A$).
  - apply mp with (B := A).
    + hypo.
    + apply axiom1.
  - apply mp with (B := $~B -> ~A$).
    + apply mp with (B := $~A$).
      * hypo.
      * apply axiom1.
    + apply axiom3.
Qed.

(* 1.10 d *)
Theorem contraposition2 {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $(~B -> ~A) -> A -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply mp with (B := A).
  - hypo.
  - apply transitivity with (B := $~B -> A$) (C := B).
    + apply axiom1.
    + apply mp with (B := $~B -> ~A$).
      * hypo.
      * apply axiom3.
Qed.

Theorem meta_neg_a_impl_a_b {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $~A$ -> Γ |- $A -> B$.
Proof.
  intro H1.
  (* 1 *)
  pose proof (@axiom1 _ Γ $~A$ $~B$) as H2.
  (* 2 *)
  pose proof (@mp _ Γ _ $~A$ H1 H2) as H3.
  (* 3 *)
  pose proof (@contraposition2 _ Γ A B) as H4.
  (* 4 *)
  pose proof (@mp _ Γ _ $~B -> ~A$ H3 H4) as H5.
  (* 5 *)
  exact H5.
Qed.

(* 1.10 e *)
Theorem contraposition {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $(A -> B) -> ~B -> ~ A$.
Proof.
  apply deduction.
  apply mp with (B := $~~A -> ~~B$).
  - apply @transitivity with (A := $~~A$) (B := B) (C := $~~B$).
    + apply transitivity with (B := A).
      * apply neg_neg_pos.
      * hypo.
    + apply pos_neg_neg.
  - apply contraposition2.
Qed.

(* 1.10 f *)
(* сначала докажем вспомогательную лемму *)
Lemma T_1_10_6' {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $A -> (A -> B) -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply mp with (B := A) ; hypo.
Qed.

(* теперь основную теорему *)
Theorem T_1_10_6 {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $A -> ~B -> ~(A -> B)$.
Proof.
  apply transitivity with (B := $(A -> B) -> B$).
  - apply T_1_10_6'.
  - apply contraposition with (A := $A -> B$) (B := B).
Qed.

(* 1.10 g *)
Theorem T_1_10_7 {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $(A -> B) -> (~ A -> B) -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply mp with (B := $~B -> ~A$).
  - apply mp with (B := $A -> B$).
    + hypo.
    + apply contraposition.
  - apply mp with (B := $~B -> ~~A$).
    + apply mp with (B := $~A -> B$).
      * hypo.
      * apply contraposition with (A := $~A$).
    + apply axiom3 with (A := $~A$).
Qed.

Theorem meta_T_1_10_7 {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $A -> B$ -> Γ |- $~A -> B$ -> Γ |- B.
Proof.
  intros H1 H2.
  (* 1 *)
  pose proof (@T_1_10_7 _ Γ A B) as H3.
  (* 2 *)
  pose proof (@mp _ Γ _ $A -> B$ H1 H3) as H4.
  (* 3 *)
  pose proof (@mp _ Γ _ $~A -> B$ H2 H4) as H5.
  (* 5 *)
  exact H5.
Qed.

(* Задачи *)
(* 1 *)
Theorem disj_intro_left {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $A -> (A \/ B)$.
Proof.
  unfold disjunction.
  apply meta_flip.
  apply neg_a_impl_a_b.
Qed.

(* 2 *)
Theorem disj_intro_right {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $A -> (B \/ A)$.
Proof.
  unfold disjunction.
  apply deduction.
  apply deduction.
  hypo.
Qed.

(* 3 *)
Theorem disj_comm {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $(A \/ B) -> (B \/ A)$.
Proof.
   unfold disjunction.
   apply deduction.
   (* (~B -> ~~A) -> (~~A -> A) -> (~B -> A) *)
   apply transitivity with (B := $~~A$).
   - apply mp with (B := $~A -> B$).
     + hypo.
     + apply contraposition with (A := $~A$).
   - apply neg_neg_pos.
Qed.

(* 4 *)
Theorem conj_elim_left {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $(A /\ B) -> A$.
Proof.
  unfold conjunction.
  apply deduction.
  (* 1 *)
  pose proof (@axiom3 _ (Γ,, $~ (A -> ~ B)$) $(A -> ~B)$ A) as H1.
  (* 2 *)
  pose proof (@axiom1 _ (Γ,, $~ (A -> ~ B)$) $~(A -> ~B)$ $~A$) as H2.
  (* 3 *)
  assert (H3 : Γ,, $~ (A -> ~ B)$ |- $~A -> ~(A -> ~B)$).
  apply mp with (B := $~(A -> ~B)$).
  hypo.
  apply H2.
  (* 4 *)
  pose proof (@mp _ (Γ,, $~ (A -> ~ B)$) _ $~A -> ~(A -> ~B)$ H3 H1) as H4.
  (* 5 *)
  pose proof (@neg_a_impl_a_b _ (Γ,, $~ (A -> ~ B)$) A $~B$) as H5.
  (* 6 *)
  pose proof (@mp _ (Γ,, $~ (A -> ~ B)$) _ $~ A -> A -> ~ B$ H5 H4) as H6.
  exact H6.
Qed.

(* 5 *)
Theorem conj_elim_right {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $(A /\ B) -> B$.
Proof.
  unfold conjunction.
  apply deduction.
  (* 1 *)
  pose proof (@axiom3 _ (Γ,, $~(A -> ~B)$) $A -> ~B$ B) as H1.
  (* 2 *)
  pose proof (@axiom1 _ (Γ,, $~(A -> ~B)$) $~(A -> ~B)$ $~B$) as H2.
  (* 3 *)
  assert (H3 : Γ,, $~(A -> ~B)$ |- $~B -> ~(A -> ~B)$).
  apply mp with (B := $~(A -> ~B)$).
  hypo.
  apply H2.
  (* 4 *)
  pose proof (@mp _ (Γ,, $~(A -> ~B)$) _ $~B -> ~(A -> ~B)$ H3 H1) as H4.
  (* 5 *)
  pose proof (@axiom1 _ (Γ,, $~(A -> ~B)$) $~B$ A) as H5.
  (* 6 *)
  pose proof (@mp _ (Γ,, $~(A -> ~B)$) _ $~B -> A -> ~B$ H5 H4) as H6.
  exact H6.
Qed.

(* 6 *)
(* Простая конструктивная дилемма *)
Theorem T_48_6 {atom : Set} {Γ : @formula atom -> Prop} A B C : Γ |- $(A -> C) -> (B -> C) -> (A \/ B) -> C$.
Proof.
  unfold disjunction.
  apply deduction.
  apply deduction.
  apply deduction.
  apply mp with (B := $~A -> C$).
  - apply transitivity with (B := B).
    + hypo.
    + hypo.
  - apply mp with (B := $A -> C$).
    + hypo.
    + apply T_1_10_7.
Qed.

Theorem T_48_7 {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $((A -> B) -> A) -> A$.
Proof.
  apply deduction.
  (* 1 *)
  pose proof (@contraposition _ (Γ,, $((A -> B) -> A)$) $A -> B$ A) as H1.
  (* 2 *)
  assert (H2 : Γ,, $((A -> B) -> A)$ |- $~A -> ~(A -> B)$).
  apply mp with (B := $(A -> B) -> A$).
  hypo.
  apply H1.
  (* 3 *)
  pose proof (@axiom3 _ (Γ,, $((A -> B) -> A)$) $A -> B$ A) as H3.
  (* 4 *)
  pose proof (@mp _ (Γ,, $((A -> B) -> A)$) _ $~A -> ~(A -> B)$ H2 H3) as H4.
  (* 5 *)
  pose proof (@neg_a_impl_a_b _ (Γ,, $((A -> B) -> A)$) A B) as H5.
  (* 6 *)
  pose proof (@mp _ (Γ,, $((A -> B) -> A)$) _ $~A -> A -> B$ H5 H4) as H6.
  exact H6.
Qed.

(* 8 *)
Theorem conj_intro {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $A -> B -> (A /\ B)$.
Proof.
  unfold conjunction.
  apply deduction.
  apply deduction.
  apply mp with (B := $~~B$).
  - apply mp with (B := B).
    + hypo.
    + apply pos_neg_neg.
  - apply mp with (B := A).
    + hypo.
    + apply T_1_10_6.
Qed.

Theorem meta_conj_intro {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- A -> Γ |- B -> Γ |- $A /\ B$.
Proof.
  intros H1 H2.
  (* 1 *)
  pose proof (@conj_intro _ Γ A B) as H3.
  (* 2 *)
  pose proof (@mp _ Γ _ A H1 H3) as H4.
  (* 3 *)
  pose proof (@mp _ Γ _ B H2 H4) as H5.
  exact H5.
Qed.

Theorem not_impl_conj_not {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $~(A -> B)$ -> Γ |- $A /\ ~B$.
Proof.
  intro H.
  unfold conjunction.
  apply mp with (B := $~ (A -> B)$).
  exact H.
  (* 1 *)
  pose proof (@contraposition _ Γ $A -> ~~B$ $A -> B$) as H1.
  (* 2 *)
  assert (H2 : Γ |- $((A -> ~~B) -> A -> B)$).
  apply deduction.
  apply deduction.
  apply meta_neg_neg_pos.
  apply mp with (B := A).
  hypo.
  hypo.
  (* 3 *)
  pose proof (@mp _ Γ _ $(A -> ~ ~ B) -> A -> B$ H2 H1) as H3.
  exact H3.
Qed.

Theorem conj_not_not_impl {atom : Set} {Γ : @formula atom -> Prop} A B : Γ |- $A /\ ~B$ -> Γ |- $~(A -> B)$.
Proof.
  unfold conjunction.
  intro H.
  apply mp with (B := $~(A -> ~~ B)$).
  exact H.
  (* 1 *)
  pose proof (@contraposition _ Γ $A -> B$ $A -> ~~B$) as H1.
  (* 2 *)
  assert (H2 : Γ |- $((A -> B) -> A -> ~ ~ B)$).
  apply deduction.
  apply deduction.
  apply meta_pos_neg_neg.
  apply mp with (B := A) ; hypo.
  (* 3 *)
  pose proof (@mp _ Γ _ $(A -> B) -> A -> ~ ~ B$ H2 H1) as H3.
  exact H3.
Qed.

Theorem eq_entails {atom : Set} (Γ Γ' : @formula atom -> Prop) (A: @formula atom) :
  (forall A, Γ A <-> Γ' A) -> (Γ |- A) -> Γ' |- A.
Proof.
  intros H1 H2.
  induction H2 as [A H|?|?|?|A B HΓ HΓ' IH1 IH2].
  - apply hypo.
    unfold elem.
    unfold elem in H.
    specialize H1 with A.
    rewrite <-H1.
    exact H.
  - apply axiom1.
  - apply axiom2.
  - apply axiom3.
  - apply mp with (B := B).
    + apply HΓ'.
    + apply IH2.
Qed.

(* The cut rule is admissible. *)
Theorem CutRule {atom : Set} (A : @formula atom) {Γ B} : Γ |- A -> extend Γ A |- B -> Γ |- B.
Proof.
  intros H G.
  induction G as [B L|?|?|?|?].
  - destruct (formula_eq A B) as [Heq|Hneq].
    + rewrite <- Heq. exact H.
    + apply hypo.
      destruct L as [Hin|Heq].
      * exact Hin.
      * specialize (Hneq Heq). destruct Hneq.
  - apply axiom1.
  - apply axiom2.
  - apply axiom3.
  - apply (mp B).
    + apply IHG1.
    + apply IHG2.
Qed.

End Syntactic.
Export Syntactic.
