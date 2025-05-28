Require Import Setoid.
From Mendelson Require Import Sets.
From Mendelson Require Import FSignature.
From Mendelson Require Import EqDec.
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
  | mp : forall A B, Γ |- $A -> B$ -> Γ |- A -> Γ |- B (* modus ponens *)
where "Γ |- A" := (entails Γ A).

(* It is convenient to make some parameters implicit. *)
Arguments hypo {_} {_} _.
Arguments axiom1 {_} {_} _ _.
Arguments axiom2 {_} {_} _ _ _.
Arguments axiom3 {_} {_} _ _.
Arguments mp {_} {_} {_} {_} (_) (_).

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
  - pose proof (mp H2 IH2) as H3.
    exact H3.
Qed.

(* Now we can define a tactic that does the above steps.
   Note the difference between the tactic "hypo" and the constructor "hypo"!
   If you type "hypo" in tactic mode, it will use the tactic defined below,
   but if you type "apply hypo" it will use the constructor hypo. *)
Ltac hypo := (apply hypo ; cbv in * ; auto 6).

Ltac specialize_axiom A H :=
  pose proof A as H;
  try match type of H with
  | (_ |- f_axiom1 _ _) => unfold f_axiom1 in H
  | (_ |- f_axiom2 _ _ _) => unfold f_axiom2 in H
  | (_ |- f_axiom3 _ _) => unfold f_axiom3 in H
  end.

(* Here are some basic observation about |-. *)
(* Лемма 1.7. $\vdash_L A \supset A$ для любой формулы A. *)
Lemma imply_self {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A -> A$.
Proof.
  (* (1) $(A \supset ((A \supset A) \supset A)) \supset ((A \supset (A \supset A)) \supset (A \supset A))$ --- подстановка в схему аксиом A2 *)
  specialize_axiom (@axiom2 _ Γ A $A -> A$ A) H1.
  (* (2) $A \supset ((A \supset A) \supset A)$ --- схема аксиом A1 *)
  specialize_axiom (@axiom1 _ Γ A $A -> A$) H2.
  (* (3) $((A \supset (A \supset A)) \supset (A \supset A))$ --- из (1) и (2) по MP *)
  specialize (mp H1 H2) as H3.
  (* (4) $A \supset (A \supset A)$ --- схема аксиом A1 *)
  specialize_axiom (@axiom1 _ Γ A A) H4.
  (* (5) $A \supset A$ --- из (3) и (4) по MP *)
  specialize (mp H3 H4) as H5.
  exact H5.
Qed.

(* We need this lemma in the deduction theorem. *)
Lemma drop_antecedent {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- B -> Γ |- $A -> B$.
Proof.
  intro H.
  (* 1. $B \supset (A \supset B)$ --- схема аксиом A1 *)
  specialize_axiom (@axiom1 _ Γ B A) H1.
  (* 2. $A \supset B$ --- из H и H1 по MP *)
  specialize (mp H1 H) as H2.
  exact H2.
Defined.

(* We conclude with the proof of the deduction theorem, just to show
   that it is quite painless to formalize. *)
Theorem deduction {atom : Set} `{HeqDec : EqDec atom} {Γ : @formula atom -> Prop} {A B} : extend Γ A |- B -> Γ |- $A -> B$.
Proof.
  intro H.
  induction H as [B H|?|?|?|B C H1 IH1 H2 IH2].
  (* Пусть B является элементом Γ,, A *)
  - unfold elem in H.
    unfold extend in H.
    destruct (formula_eq A B) as [Heq|Hneq].
    (* Если B = A, применяем лемму imply_self *)
    + rewrite Heq.
      apply imply_self.
    (* Если B != A, по аксиоме 1 получаем формулу *)
    (* $B \supset (A \supset B)$ *)
    + specialize_axiom (@axiom1 _ Γ B A) H1.
      (* Поскольку B != A, B содержится в Γ *)
      assert (H2: Γ |- B).
      {
        apply hypo.
        unfold elem in H.
        destruct H as [Hin|Heq].
        * unfold elem.
          exact Hin.
        * apply Hneq in Heq.
          contradiction Heq.
      }

      (* По MP из H1 : Γ |- $B -> (A -> B)$ *)
      (* и H2 : Γ |- B получаем Γ |- $A -> B$ *)
      specialize (mp H1 H2) as H3.
      exact H3.
  - (* Пусть B является аксиомой *)
    apply drop_antecedent.
    apply axiom1.
  - apply drop_antecedent.
    apply axiom2.
  - apply drop_antecedent.
    apply axiom3.
  - (* Modus Ponens:
       Пусть C получена по MP из 2-х формул B и $B -> C$ по Modus Ponens, и пусть они доказуемы в контексте (Γ,, A):
       H1 : Γ,, A |- $B -> C$
       H2 : Γ,, A |- B

       Пусть истинны индуктивные гипотезы:
       IH1 : Γ |- $A -> B -> C$
       IH2 : Γ |- $A -> B$
    *)

    (* По аксиоме 2: $(A -> (B -> C)) -> ((A -> B) -> (A -> C))$ *)
    specialize_axiom (@axiom2 _ Γ A B C) H3.

    (* MP *)
    (* IH1 : Γ |- $A -> B -> C$ *)
    (*  H3 : Γ |- $(A -> B -> C) -> (A -> B) -> A -> C$ *)
    specialize (mp H3 IH1) as H4.

    (* MP *)
    (* IH2 : Γ |- $A -> B$ *)
    (*  H4 : Γ |- $(A -> B) -> A -> C$ *)
    specialize (mp H4 IH2) as H5.
    exact H5.
Defined.

(* Упражнения *)
Lemma T1_7ex1 {atom : Set} (Γ : @formula atom -> Prop) A : Γ |- $(~A -> A) -> A$.
Proof.
  specialize_axiom (@axiom3 _ Γ A A) H1.
  pose proof (imply_self Γ $~A$) as H2.
  specialize (mp H1 H2) as H3.
  exact H3.
Qed.

Lemma T1_7ex2 {atom : Set} (Γ : @formula atom -> Prop) A B C : Γ ,, $A -> B$ ,, $B -> C$ |- $A -> C$.
Proof.
  (* 1 *)
  specialize_axiom (@axiom1 _ (Γ ,, $A -> B$ ,, $B -> C$) $B -> C$ A) H1.
  (* 2 *)
  assert (H2 : Γ,, $A -> B$,, $B -> C$ |- $A -> (B -> C)$).
  {
    apply @mp with (A := $B -> C$).
    - apply H1.
    - hypo.
  }
  (* 3  *)
  specialize_axiom (@axiom2 _ (Γ ,, $A -> B$ ,, $B -> C$) A B C) H3.
  (* 4 *)
  specialize (mp H3 H2) as H4.
  (* 5 *)
  assert (H5 : Γ,, $A -> B$,, $B -> C$ |- $A -> C$).
  {
    apply @mp with (A := $A -> B$).
    exact H4.
    hypo.
  }
  (* 6 *)
  exact H5.
Qed.

Lemma T1_7ex3 {atom : Set} (Γ : @formula atom -> Prop) A B C : Γ ,, $A -> (B -> C)$ |- $B -> (A -> C)$.
Proof.
  (* 1 *)
  specialize_axiom (@axiom2 _ (Γ,, $A -> (B -> C)$) A B C) H1.
  (* 2 *)
  assert (H2 : Γ,, $A -> (B -> C)$ |- $(A -> B) -> (A -> C)$).
  {
    apply @mp with (A := $A -> (B -> C)$).
    exact H1.
    hypo.
  }
  (* 3 *)
  specialize_axiom (@axiom1 _ (Γ,, $A -> (B -> C)$) $((A -> B) -> (A -> C))$ B) H3.
  (* 4 *)
  specialize (mp H3 H2) as H4.
  (* 5 *)
  specialize_axiom (@axiom2 _ (Γ,, $A -> (B -> C)$) B $A -> B$ $A -> C$) H5.
  (* 6 *)
  specialize (mp H5 H4) as H6.
  (* 7 *)
  specialize_axiom (@axiom1 _ (Γ,, $A -> B -> C$) B A) H7.
  (* 8 *)
  specialize (mp H6 H7) as H8.
  exact H8.
Qed.

Corollary transitivity {atom : Set} {Γ : @formula atom -> Prop} {A} B {C} :
  Γ |- $A -> B$ -> Γ |- $B -> C$ -> Γ |- $A -> C$.
Proof.
  intros H1 H2.
  apply @mp with (A := $A -> B$).
  - apply @mp with (A := $A -> B -> C$).
    + apply axiom2.
    + apply drop_antecedent.
      exact H2.
  - exact H1.
Qed.

(* теорема, обратная теореме дедукции *)
Lemma impl_intro {atom : Set} {Γ : @formula atom -> Prop} {A B} :
  Γ |- $A -> B$ -> extend Γ A |- B.
Proof.
  intro H.
  apply @mp with (A := A).
  (* weaken Γ Δ A : Γ ⊆ Δ -> Γ |- A -> Δ |- A. *)
  - apply (weaken Γ).
    + apply subset_extend.
    + exact H.
  - hypo.
Qed.

Corollary flip {atom : Set} `{HEqDec : EqDec atom} {Γ : @formula atom -> Prop} {A} B {C} :
  Γ |- $A -> B -> C$ -> Γ |- B -> Γ |- $A -> C$.
Proof.
  intros H1 H2.
  apply deduction.
  apply @mp with (A := B).
  - apply impl_intro.
    exact H1.
  - apply (weaken Γ).
    + apply subset_extend.
    + exact H2.
Qed.

Corollary meta_flip {atom : Set} `{HEqDec : EqDec atom} {Γ : @formula atom -> Prop} {A} B {C} :
  Γ |- $A -> B -> C$ -> Γ |- $B -> A -> C$.
Proof.
  intros H.
  apply deduction.
  apply deduction.
  assert (H1 : Γ,, B,, A |- $B -> C$).
  apply @mp with (A := A).
  - apply (weaken Γ).
    + unfold subset.
      intros.
      unfold extend.
      unfold elem in *.
      left.
      auto.
    + exact H.
  - hypo.
  - apply @mp with (A := B).
    + exact H1.
    + hypo.
Qed.

(* 1.10 a *)
Theorem neg_neg_pos {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) B : Γ |- $~~B -> B$.
Proof.
  apply (transitivity $~B -> ~~B$).
  - apply axiom1.
  - apply (flip $~B -> ~B$).
    + apply axiom3 with (B := B) (A := $~B$).
    + apply imply_self.
Qed.

(* 1.10 b *)
Theorem pos_neg_neg {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) B : Γ |- $B -> ~~B$.
Proof.
  apply transitivity with (B := $~ ~ ~ B -> B$).
  - apply axiom1.
  - apply @mp with (A := $~ ~ ~ B -> ~ B$).
    + exact (axiom3 B $~~B$).
    + apply neg_neg_pos with (B := $~B$).
Qed.

Theorem meta_neg_neg_pos {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) B : (Γ |- $~~B$) -> (Γ |- B).
Proof.
  intro H.
  apply @mp with (A := $~~ B$).
  - apply neg_neg_pos.
  - exact H.
Qed.

Theorem meta_pos_neg_neg {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) B : (Γ |- B) -> (Γ |- $~~B$).
Proof.
  intro H.
  specialize (pos_neg_neg Γ B) as H1.
  apply @mp with (A := B).
  - exact H1.
  - exact H.
Qed.

(* 1.10 c *)
Theorem neg_a_impl_a_b {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $~A -> A -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply @mp with (A := $~B -> A$).
  - apply @mp with (A := $~B -> ~A$).
    + apply axiom3.
    + apply @mp with (A := $~A$).
      * apply axiom1.
      * hypo.
  - apply @mp with (A := A).
    + apply axiom1.
    + hypo.
Qed.

(* 1.10 d *)
Theorem contraposition2 {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $(~B -> ~A) -> A -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply @mp with (A := A).
  - apply transitivity with (B := $~B -> A$) (C := B).
    + apply axiom1.
    + apply @mp with (A := $~B -> ~A$).
      * apply axiom3.
      * hypo.
  - hypo.
Qed.

Theorem meta_neg_a_impl_a_b {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $~A$ -> Γ |- $A -> B$.
Proof.
  intro H1.
  specialize_axiom (@axiom1 _ Γ $~A$ $~B$) H2.
  specialize (mp H2 H1) as H3.
  specialize (contraposition2 Γ A B) as H4.
  specialize (mp H4 H3) as H5.
  exact H5.
Qed.

(* 1.10 e *)
Theorem contraposition {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $(A -> B) -> ~B -> ~ A$.
Proof.
  apply deduction.
  apply @mp with (A := $~~A -> ~~B$).
  - apply contraposition2.
  - apply @transitivity with (A := $~~A$) (B := B) (C := $~~B$).
    + apply transitivity with (B := A).
      * apply neg_neg_pos.
      * hypo.
    + apply pos_neg_neg.
Qed.

(* 1.10 f *)
(* сначала докажем вспомогательную лемму *)
Lemma T_1_10_6' {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $A -> (A -> B) -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply @mp with (A := A) ; hypo.
Qed.

(* теперь основную теорему *)
Theorem T_1_10_6 {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $A -> ~B -> ~(A -> B)$.
Proof.
  apply transitivity with (B := $(A -> B) -> B$).
  - apply T_1_10_6'.
  - apply contraposition with (A := $A -> B$) (B := B).
Qed.

(* 1.10 g *)
Theorem T_1_10_7 {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $(A -> B) -> (~ A -> B) -> B$.
Proof.
  apply deduction.
  apply deduction.
  apply @mp with (A := $~B -> ~A$).
  - apply @mp with (A := $~B -> ~~A$).
    + apply axiom3 with (A := $~A$).
    + apply @mp with (A := $~A -> B$).
      * apply contraposition with (A := $~A$).
      * hypo.
  - apply @mp with (A := $A -> B$).
    + apply contraposition.
    + hypo.
Qed.

Theorem meta_T_1_10_7 {atom : Set} `{HEqDec : EqDec atom} {Γ : @formula atom -> Prop} A B : Γ |- $A -> B$ -> Γ |- $~A -> B$ -> Γ |- B.
Proof.
  intros H1 H2.
  specialize (T_1_10_7 Γ A B) as H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

(* Задачи *)
(* 1 *)
Theorem disj_intro_left {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $A -> (A \/ B)$.
Proof.
  unfold disjunction.
  apply meta_flip.
  apply neg_a_impl_a_b.
Qed.

(* 2 *)
Theorem disj_intro_right {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $A -> (B \/ A)$.
Proof.
  unfold disjunction.
  apply deduction.
  apply deduction.
  hypo.
Qed.

(* 3 *)
Theorem disj_comm {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $(A \/ B) -> (B \/ A)$.
Proof.
   unfold disjunction.
   apply deduction.
   (* (~B -> ~~A) -> (~~A -> A) -> (~B -> A) *)
   apply transitivity with (B := $~~A$).
   - apply @mp with (A := $~A -> B$).
     + apply contraposition with (A := $~A$).
     + hypo.
   - apply neg_neg_pos.
Qed.

(* 4 *)
Theorem conj_elim_left {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $(A /\ B) -> A$.
Proof.
  unfold conjunction.
  apply deduction.
  (* 1 *)
  specialize_axiom (@axiom3 _ (Γ,, $~ (A -> ~ B)$) $(A -> ~B)$ A) H1.
  (* 2 *)
  specialize_axiom (@axiom1 _ (Γ,, $~ (A -> ~ B)$) $~(A -> ~B)$ $~A$) H2.
  (* 3 *)
  assert (H3 : Γ,, $~ (A -> ~ B)$ |- $~A -> ~(A -> ~B)$).
  {
    apply @mp with (A := $~(A -> ~B)$).
    - apply H2.
    - hypo.
  }
  (* 4 *)
  specialize (mp H1 H3) as H4.
  (* 5 *)
  specialize (neg_a_impl_a_b (Γ,, $~ (A -> ~ B)$) A $~B$) as H5.
  (* 6 *)
  specialize (mp H4 H5) as H6.
  exact H6.
Qed.

(* 5 *)
Theorem conj_elim_right {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $(A /\ B) -> B$.
Proof.
  unfold conjunction.
  apply deduction.
  (* 1 *)
  specialize_axiom (@axiom3 _ (Γ,, $~(A -> ~B)$) $A -> ~B$ B) H1.
  (* 2 *)
  specialize_axiom (@axiom1 _ (Γ,, $~(A -> ~B)$) $~(A -> ~B)$ $~B$) H2.
  (* 3 *)
  assert (H3 : Γ,, $~(A -> ~B)$ |- $~B -> ~(A -> ~B)$).
  {
    apply @mp with (A := $~(A -> ~B)$).
    - apply H2.
    - hypo.
  }
  (* 4 *)
  specialize (mp H1 H3) as H4.
  (* 5 *)
  specialize_axiom (@axiom1 _ (Γ,, $~(A -> ~B)$) $~B$ A) H5.
  (* 6 *)
  specialize (mp H4 H5) as H6.
  exact H6.
Qed.

(* 6 *)
(* Простая конструктивная дилемма *)
Theorem T_48_6 {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B C : Γ |- $(A -> C) -> (B -> C) -> (A \/ B) -> C$.
Proof.
  unfold disjunction.
  apply deduction.
  apply deduction.
  apply deduction.
  apply @mp with (A := $~A -> C$).
  - apply @mp with (A := $A -> C$).
    + apply T_1_10_7.
    + hypo.
  - apply transitivity with (B := B).
    + hypo.
    + hypo.
Qed.

Theorem T_48_7 {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $((A -> B) -> A) -> A$.
Proof.
  apply deduction.
  (* 1 *)
  specialize (contraposition (Γ,, $((A -> B) -> A)$) $A -> B$ A) as H1.
  (* 2 *)
  assert (H2 : Γ,, $((A -> B) -> A)$ |- $~A -> ~(A -> B)$).
  apply @mp with (A := $(A -> B) -> A$).
  apply H1.
  hypo.
    (* 3 *)
  specialize_axiom (@axiom3 _ (Γ,, $((A -> B) -> A)$) $A -> B$ A) H3.
  (* 4 *)
  specialize (mp H3 H2) as H4.
  (* 5 *)
  specialize (neg_a_impl_a_b (Γ,, $((A -> B) -> A)$) A B) as H5.
  (* 6 *)
  specialize (mp H4 H5) as H6.
  exact H6.
Qed.

(* 8 *)
Theorem conj_intro {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $A -> B -> (A /\ B)$.
Proof.
  unfold conjunction.
  apply deduction.
  apply deduction.
  apply @mp with (A := $~~B$).
  - apply @mp with (A := A).
    + apply T_1_10_6.
    + hypo.
  - apply @mp with (A := B).
    + apply pos_neg_neg.
    + hypo.
Qed.

Theorem meta_conj_intro {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- A -> Γ |- B -> Γ |- $A /\ B$.
Proof.
  intros H1 H2.
  (* 1 *)
  specialize (conj_intro Γ A B) as H3.
  (* 2 *)
  specialize (mp H3 H1) as H4.
  (* 3 *)
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Theorem not_impl_conj_not {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $~(A -> B)$ -> Γ |- $A /\ ~B$.
Proof.
  intro H.
  unfold conjunction.
  apply @mp with (A := $~ (A -> B)$).
  - specialize (contraposition Γ $A -> ~~B$ $A -> B$) as H1.
    assert (H2 : Γ |- $((A -> ~~B) -> A -> B)$).
    {
      apply deduction.
      apply deduction.
      apply meta_neg_neg_pos.
      apply @mp with (A := A).
      + hypo.
      + hypo.
    }

    specialize (mp H1 H2) as H3.
    exact H3.
  - exact H.
Qed.

Theorem conj_not_not_impl {atom : Set} `{HEqDec : EqDec atom} (Γ : @formula atom -> Prop) A B : Γ |- $A /\ ~B$ -> Γ |- $~(A -> B)$.
Proof.
  unfold conjunction.
  intro H.
  apply @mp with (A := $~(A -> ~~ B)$).
  - specialize (contraposition Γ $A -> B$ $A -> ~~B$) as H1.
    assert (H2 : Γ |- $((A -> B) -> A -> ~ ~ B)$).
    {
      apply deduction.
      apply deduction.
      apply meta_pos_neg_neg.
      apply @mp with (A := A) ; hypo.
    }

    specialize (mp H1 H2) as H3.
    exact H3.
  - exact H.
Qed.

Theorem eq_entails {atom : Set} `{HEqDec : EqDec atom} (Γ Γ' : @formula atom -> Prop) (A: @formula atom) :
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
  - apply @mp with (A := A).
    + apply HΓ'.
    + apply IH2.
Qed.

(* The cut rule is admissible. *)
Theorem CutRule {atom : Set} `{HEqDec : EqDec atom} (A : @formula atom) {Γ B} : Γ |- A -> extend Γ A |- B -> Γ |- B.
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
  - apply @mp with (A := A0).
    + apply IHG1.
    + apply IHG2.
Qed.

End Syntactic.
Export Syntactic.
