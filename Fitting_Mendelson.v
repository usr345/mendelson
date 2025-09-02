Require Import Setoid.
From Mendelson Require Import Sets.
From Mendelson Require Import FSignature.
From Mendelson Require Import EqDec.
Require Import Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Logic.
From Coq Require Import List.
Import ListNotations.
Require Import Logic.Classical_Prop.
Require Import Logic.Classical_Pred_Type.

Module Formula1 <: TFormula.
  (* Синтаксис модальной формулы *)
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula
  | f_imp  : formula -> formula -> formula
  | f_box  : formula -> formula
  | f_diamond  : formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} := @f_conj atom.
  Definition disjunction {atom : Type} := @f_disj atom.
  Definition implication {atom : Type} := @f_imp atom.
  Definition equivalence {atom : Type} (A B: @formula atom) : formula := conjunction (implication A B) (implication B A).

  #[global] Notation "'box' p" := (f_box p) (p custom formula_view at level 1, in custom formula_view at level 1) : formula_scope.
  #[global] Notation "'diamond' p" := (f_diamond p) (p custom formula_view at level 1, in custom formula_view at level 1) : formula_scope.
End Formula1.
Export Formula1.

Module Formula.

  Module F1:= Make_Formula(Formula1).
  Import F1.
  Export F1.

  (* We assume atomic propositions form a set with decidable equality. *)
  Parameter atom_eq : forall {atom : Set} (a b : atom), {a = b} + {a <> b}.

  (* Equality of formulas is decidable. *)
  Lemma formula_eq {atom : Set} (A B : @formula atom) : {A = B} + {A <> B}.
  Proof.
    decide equality.
    now apply atom_eq.
  Qed.

  Fixpoint formula_beq {atom : Set} `{EqDec atom} (A B : @formula atom) : bool :=
    match A, B with
    | f_atom a, f_atom b  => eqb a b
    | f_not A', f_not B' => formula_beq A' B'
    | f_conj A1 A2, f_conj B1 B2 => andb (formula_beq A1 B1) (formula_beq A2 B2)
    | f_disj A1 A2, f_disj B1 B2 => andb (formula_beq A1 B1) (formula_beq A2 B2)
    | f_imp A1 A2, f_imp B1 B2 => andb (formula_beq A1 B1) (formula_beq A2 B2)
    | f_box A', f_box B' => formula_beq A' B'
    | f_diamond A', f_diamond B' => formula_beq A' B'
    | _, _ => false
    end.

  Lemma formula_beq_eq {atom : Set} `{EqDec atom} (A B : @formula atom) :
    (formula_beq A B) = true <-> A = B.
  Proof.
    split ; intro H1.
    - generalize dependent B.
      induction A.
      + intros B H1.
        destruct B ; unfold formula_beq in H1 ; try discriminate H1.
        (* f_atom *)
        * apply eqb_eq in H1.
          rewrite H1.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* f_not *)
        * specialize (IHA B).
          specialize (IHA H1).
          rewrite IHA.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* conj *)
        * apply andb_prop in H1.
          destruct H1 as [H1 H2].
          specialize (IHA1 B1).
          specialize (IHA1 H1).
          specialize (IHA2 B2).
          specialize (IHA2 H2).
          rewrite IHA1.
          rewrite IHA2.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* disj *)
        * apply andb_prop in H1.
          destruct H1 as [H1 H2].
          specialize (IHA1 B1).
          specialize (IHA1 H1).
          specialize (IHA2 B2).
          specialize (IHA2 H2).
          rewrite IHA1.
          rewrite IHA2.
          reflexivity.
      + intros B H1.
        destruct B ; simpl in H1 ; try discriminate H1.
        (* impl *)
        * apply andb_prop in H1.
          destruct H1 as [H1 H2].
          specialize (IHA1 B1).
          specialize (IHA1 H1).
          specialize (IHA2 B2).
          specialize (IHA2 H2).
          rewrite IHA1.
          rewrite IHA2.
          reflexivity.
      + intros B H1.
        destruct B ; try (simpl in H1 ; discriminate H1).
        (* f_box *)
        * specialize (IHA B).
          specialize (IHA H1).
          rewrite IHA.
          reflexivity.
      + intros B H1.
        destruct B ; try (simpl in H1 ; discriminate H1).
        (* f_diamond *)
        * specialize (IHA B).
          specialize (IHA H1).
          rewrite IHA.
          reflexivity.
    - generalize dependent B.
      induction A.
      (* atom *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        apply eqb_reflexive.
      (* not *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        specialize (IHA A).
        assert (Ha : A = A).
        { reflexivity. }
        specialize (IHA Ha).
        apply IHA.
      (* conj *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        apply andb_true_intro.
        split.
        * specialize (IHA1 A1).
        assert (Ha : A1 = A1).
        { reflexivity. }
        specialize (IHA1 Ha).
        apply IHA1.
        * specialize (IHA2 A2).
        assert (Ha : A2 = A2).
        { reflexivity. }
        specialize (IHA2 Ha).
        apply IHA2.
      (* disj *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        apply andb_true_intro.
        split.
        * specialize (IHA1 A1).
        assert (Ha : A1 = A1).
        { reflexivity. }
        specialize (IHA1 Ha).
        apply IHA1.
        * specialize (IHA2 A2).
        assert (Ha : A2 = A2).
        { reflexivity. }
        specialize (IHA2 Ha).
        apply IHA2.
      (* impl *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        apply andb_true_intro.
        split.
        * specialize (IHA1 A1).
        assert (Ha : A1 = A1).
        { reflexivity. }
        specialize (IHA1 Ha).
        apply IHA1.
        * specialize (IHA2 A2).
        assert (Ha : A2 = A2).
        { reflexivity. }
        specialize (IHA2 Ha).
        apply IHA2.
      (* box *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        specialize (IHA A).
        assert (Ha : A = A).
        { reflexivity. }
        specialize (IHA Ha).
        apply IHA.
      (* diamond *)
      + intros B H1.
        rewrite <-H1.
        simpl.
        specialize (IHA A).
        assert (Ha : A = A).
        { reflexivity. }
        specialize (IHA Ha).
        apply IHA.
  Qed.

  #[export] Instance eqFormula {atom : Set} `{EqDec atom} : EqDec (@formula atom) :=
    {
      eqb := formula_beq;
      eqb_eq := formula_beq_eq;
    }.

End Formula.
Export Formula.

Module Syntactic.

Axiom Possibility : forall {atom : Type} (A: @formula atom), $diamond A$ = $~ (box ~A)$.

Definition f_axiom1 {atom : Set} (A B : @formula atom) : formula :=
  $A -> (B -> A)$.

Definition f_axiom2 {atom : Set} (A B C : @formula atom) : formula :=
  $(A -> B -> C) -> (A -> B) -> (A -> C)$.

Definition f_conj_elim1 {atom : Set} (A B : @formula atom) : formula :=
  $(A /\ B) -> A$.

Definition f_conj_elim2 {atom : Set} (A B : @formula atom) : formula :=
  $(A /\ B) -> B$.

Definition f_conj_intro {atom : Set} (A B : @formula atom) : formula :=
  $A -> (B -> (A /\ B))$.

Definition f_disj_intro1 {atom : Set} (A B : @formula atom) : formula :=
  $A -> (A \/ B)$.

Definition f_disj_intro2 {atom : Set} (A B : @formula atom) : formula :=
  $B -> (A \/ B)$.

Definition f_case_analysis {atom : Set} (A B C : @formula atom) : formula :=
  $(A -> C) -> (B -> C) -> (A \/ B -> C)$.

Definition f_ex_falso {atom : Set} (A B : @formula atom) : formula :=
  $~A -> (A -> B)$.

Definition f_tertium_non_datur {atom : Set} (A : @formula atom) : formula := $A \/ ~A$.

Definition f_axiomK {atom : Set} (A B : @formula atom) : formula :=
  $box (A -> B) -> (box A -> box B)$.

Reserved Notation "Γ |- A" (at level 98).
Inductive entails {atom : Set} (Γ : @formula atom -> Prop) : @formula atom -> Type :=
  | hypo : forall A, A ∈ Γ -> Γ |- A (* every hypothesis is provable *)
  | axiom1 : forall A B , Γ |- f_axiom1 A B
  | axiom2 : forall A B C, Γ |- f_axiom2 A B C
  | conj_elim1 : forall A B, Γ |- f_conj_elim1 A B
  | conj_elim2 : forall A B , Γ |- f_conj_elim2 A B
  | conj_intro : forall A B, Γ |- f_conj_intro A B
  | disj_intro1 : forall A B, Γ |- f_disj_intro1 A B
  | disj_intro2 : forall A B , Γ |- f_disj_intro2 A B
  | case_analysis : forall A B C, Γ |- f_case_analysis A B C
  | ex_falso : forall A B, Γ |- f_ex_falso A B
  | tertium_non_datur : forall A, Γ |- f_tertium_non_datur A
  | axiomK : forall A B, Γ |- f_axiomK A B
  | mp : forall A B, Γ |- $A -> B$ -> Γ |- A -> Γ |- B (* modus ponens *)
  | nec : forall A, Γ |- A -> Γ |- $box A$            (* necessitation *)
where "Γ |- A" := (entails Γ A).

(* It is convenient to make some parameters implicit. *)
Arguments hypo {_} {_} _.
Arguments axiom1 {_} (_) _ _.
Arguments axiom2 {_} (_) _ _ _.
Arguments conj_elim1 {_} (_) _ _.
Arguments conj_elim2 {_} (_) _ _.
Arguments conj_intro {_} (_) _ _.
Arguments disj_intro1 {_} (_) _ _.
Arguments disj_intro2 {_} (_) _ _.
Arguments case_analysis {_} _ _ _ _.
Arguments ex_falso {_} (_) _ _.
Arguments tertium_non_datur {_} (_) _.
Arguments axiomK {_} {_} _ _.
Arguments mp {_} {_} {_} {_} (_) (_).
Arguments nec {_} {_} {_} (_).

Ltac hypo := (apply hypo ; cbv in * ; auto 6).

Ltac specialize_axiom A H :=
  pose proof A as H;
  try match type of H with
  | (_ |- f_axiom1 _ _) => unfold f_axiom1 in H
  | (_ |- f_axiom2 _ _ _) => unfold f_axiom2 in H
  | (_ |- f_conj_elim1 _ _) => unfold f_conj_elim1 in H
  | (_ |- f_conj_elim2 _ _) => unfold f_conj_elim2 in H
  | (_ |- f_conj_intro _ _) => unfold f_conj_intro in H
  | (_ |- f_disj_intro1 _ _) => unfold f_disj_intro1 in H
  | (_ |- f_disj_intro2 _ _) => unfold f_disj_intro2 in H
  | (_ |- f_case_analysis _ _ _) => unfold f_case_analysis in H
  | (_ |- f_ex_falso _ _) => unfold f_ex_falso in H
  | (_ |- f_tertium_non_datur _) => unfold f_tertium_non_datur in H
  | (_ |- f_axiomK _ _) => unfold f_axiomK in H
  end.

Lemma meta_conj_elim1 {atom : Set} {Γ : @formula atom -> Prop} {A B : @formula atom} : Γ |- $(A /\ B)$ -> Γ |- A.
Proof.
  intro H1.
  specialize_axiom (conj_elim1 Γ A B) H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Lemma meta_conj_elim2 {atom : Set} {Γ : @formula atom -> Prop} {A B : @formula atom} : Γ |- $(A /\ B)$ -> Γ |- B.
Proof.
  intro H1.
  specialize_axiom (conj_elim2 Γ A B) H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Lemma meta_conj_intro {atom : Set} {Γ : @formula atom -> Prop} {A B : @formula atom} : Γ |- A -> Γ |- B -> Γ |- $A /\ B$.
Proof.
  intros H1 H2.
  specialize_axiom (conj_intro Γ A B) H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

(* Импликация из объектного в метаязык *)
Lemma obj_meta_impl {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $A -> B$ -> (Γ |- A -> Γ |- B).
Proof.
  intros H1 H2.
  specialize (mp H1 H2) as H3.
  exact H3.
Qed.

Lemma obj_meta_equiv1 {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $A <-> B$ -> (Γ |- A -> Γ |- B).
Proof.
  intros H1 H2.
  unfold equivalence in H1.
  specialize (meta_conj_elim1 H1) as H3.
  specialize (mp H3 H2) as H4.
  exact H4.
Qed.

Lemma obj_meta_equiv2 {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $A <-> B$ -> (Γ |- B -> Γ |- A).
Proof.
  intros H1 H2.
  unfold equivalence in H1.
  specialize (meta_conj_elim2 H1) as H3.
  specialize (mp H3 H2) as H4.
  exact H4.
Qed.


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
Lemma add_context {atom : Set} (Γ : @formula atom -> Prop) (A B : @formula atom) : Γ |- B -> Γ |- $A -> B$.
Proof.
  intro H.
  (* 1. $B \supset (A \supset B)$ --- схема аксиом A1 *)
  specialize_axiom (@axiom1 _ Γ B A) H1.
  (* 2. $A \supset B$ --- из H и H1 по MP *)
  specialize (mp H1 H) as H2.
  exact H2.
Qed.

Lemma A_impl_conj {atom : Set} (Γ : @formula atom -> Prop) (A X Y : @formula atom) : Γ |- $(A -> X) -> (A -> Y) -> (A -> (X /\ Y))$.
Proof.
  specialize_axiom (@axiom1 _ Γ $A -> X$ $A -> Y$) H1.
  specialize (imply_self Γ $A -> Y$) as H2.
  specialize (add_context Γ $A -> X$ $(A -> Y) -> (A -> Y)$ H2) as H3.
Admitted.

Lemma transitivity {atom : Set} {Γ : @formula atom -> Prop} {A} B {C} :
  Γ |- $(A -> B) -> (B -> C) -> A -> C$.
Proof.
Admitted.

Lemma meta_transitivity {atom : Set} {Γ : @formula atom -> Prop} {A B C: @formula atom} :
  Γ |- $A -> B$ -> Γ |- $B -> C$ -> Γ |- $A -> C$.
Proof.
  intros H1 H2.
  specialize (@transitivity _ Γ A B C) as H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Lemma impl_conj {atom : Set} (Γ : @formula atom -> Prop) X Y Z :
  Γ |- $(X -> (Y -> Z)) -> (X /\ Y -> Z)$.
Proof.
Admitted.

Lemma conj_comm {atom : Set} (Γ : @formula atom -> Prop) (X Y: @formula atom) :
  Γ |- $(X /\ Y) -> (Y /\ X)$.
Proof.
  specialize_axiom (conj_elim1 Γ X Y) H1.
  specialize_axiom (conj_elim2 Γ X Y) H2.
  specialize_axiom (conj_intro Γ Y X) H3.
  specialize (meta_transitivity H2 H3) as H4.
  specialize_axiom (axiom2 Γ $X /\ Y$ X $Y /\ X$) H5.
  specialize (mp H5 H4) as H6.
  specialize (mp H6 H1) as H7.
  exact H7.
Qed.

(* 2.6.3 *)
Lemma disj_commutativity_impl {atom : Set} (Γ : @formula atom -> Prop) (X Y: @formula atom) :
  Γ |- $(X \/ Y) -> (Y \/ X)$.
Proof.
  specialize_axiom (disj_intro2 Γ Y X) H1.
  specialize_axiom (disj_intro1 Γ Y X) H2.
  specialize_axiom (case_analysis Γ X Y $Y \/ X$) H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Lemma disj_comm {atom : Set} (Γ : @formula atom -> Prop) (X Y: @formula atom) :
  Γ |- $(X \/ Y) <-> (Y \/ X)$.
Proof.
  unfold equivalence.
  specialize (disj_commutativity_impl Γ X Y) as H1.
  specialize (disj_commutativity_impl Γ Y X) as H2.
  specialize_axiom (conj_intro Γ $(X \/ Y -> Y \/ X)$ $(Y \/ X -> X \/ Y)$) H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Lemma reguarity {atom : Set} {Γ : @formula atom -> Prop} {A B : @formula atom} : Γ |- $A -> B$ -> Γ |- $box A -> box B$.
Proof.
  intro H1.
  specialize (nec H1) as H2.
  specialize_axiom (@axiomK _ Γ A B) H3.
  specialize (mp H3 H2) as H4.
  exact H4.
Qed.

(* Example 6.1.4 *)
Lemma box_conj {atom : Set} (Γ : @formula atom -> Prop) (A B : @formula atom) : Γ |- $box (A /\ B) -> (box A /\ box B)$.
Proof.
  specialize_axiom (@conj_elim1 _ Γ A B) H1.
  specialize (reguarity H1) as H2.
  specialize_axiom (@conj_elim2 _ Γ A B) H3.
  specialize (reguarity H3) as H4.
  specialize (A_impl_conj Γ $box (A /\ B)$ $box A$ $box B$) as H5.
  specialize (mp H5 H2) as H6.
  specialize (mp H6 H4) as H7.
  exact H7.
Qed.

Lemma meta_box_conj {atom : Set} {Γ : @formula atom -> Prop} (A B : @formula atom) : Γ |- $box (A /\ B)$ -> Γ |-  $box A /\ box B$.
Proof.
  intro H1.
  specialize (box_conj Γ A B) as H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

(* Example 6.1.5 *)
Lemma conj_box {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $(box X /\ box Y) -> box (X /\ Y)$.
Proof.
  specialize_axiom (@conj_intro _ Γ X Y) H1.
  specialize (reguarity H1) as H2.
  specialize_axiom (@axiomK _ Γ Y $X /\ Y$) H3.
  specialize (@transitivity _ Γ $box X$ $box (Y -> X /\ Y)$ $box Y -> box (X /\ Y)$) as H4.
  specialize (mp H4 H2) as H5.
  specialize (mp H5 H3) as H6.
  specialize (impl_conj Γ $box X$ $box Y$ $box (X /\ Y)$) as H7.
  specialize (mp H7 H6) as H8.
  exact H8.
Qed.

Theorem contraposition {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $(A -> B) -> ~B -> ~ A$.
Proof.
Admitted.

Theorem meta_contraposition {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $(A -> B)$ -> Γ |- $~B -> ~ A$.
Proof.
  intro H1.
  specialize (contraposition Γ A B) as H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Theorem deMorganDisj {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $~(A \/ B) -> ~A /\ ~B$.
Proof.
Admitted.

Theorem meta_deMorganDisj {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $~(A \/ B)$ -> Γ |- $~A /\ ~B$.
Proof.
  intro H1.
  specialize (deMorganDisj Γ A B) as H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Theorem deMorganDisj_rev {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $~A /\ ~B -> ~(A \/ B)$.
Proof.
Admitted.

Theorem deMorganConj {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $~(A /\ B) -> ~A \/ ~B$.
Proof.
Admitted.

Theorem meta_deMorganConj {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $~(A /\ B)$ -> Γ |- $~A \/ ~B$.
Proof.
  intro H1.
  specialize (deMorganConj Γ A B) as H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Theorem deMorganConj_rev {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- $~A \/ ~B -> ~(A /\ B)$.
Proof.
Admitted.

(* Импликация из метаязыка в объектный *)
(* Lemma meta_obj_impl {atom : Set} (Γ : @formula atom -> Prop) A B : (Γ |- A -> Γ |- B) -> Γ |- $A -> B$. *)
(* Proof. *)

(* Exercize 6.1.1 *)
Proposition impl_diamond {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ ,, $X -> Y$ |- (f_imp (f_diamond X) (f_diamond Y)).
Proof.
  assert (H1 : Γ ,, $X -> Y$ |- $X -> Y$).
  {
    hypo.
  }

  specialize (contraposition (Γ,, $X -> Y$) X Y) as H2.
  specialize (mp H2 H1) as H3.
  specialize (nec H3) as H4.
  pose proof (@axiomK _ (Γ,, $X -> Y$) $~Y$ $~X$) as H5.
  unfold f_axiomK in H5.
  specialize (mp H5 H4) as H6.
  specialize (contraposition (Γ,, $X -> Y$) $box ~ Y$ $box ~ X$) as H7.
  specialize (mp H7 H6) as H8.
  repeat rewrite <-Possibility in H8.
  exact H8.
Qed.

Instance eqNat: EqDec nat :=
{
  eqb := Nat.eqb;
  eqb_eq := Nat.eqb_eq;
}.

(*
n != 0
Возвращает
*)
Fixpoint replace_subformula_int {atom : Set} `{EqDec atom} (X X' Y : @formula atom) (n : nat) {struct Y} : (@formula atom * nat) :=
  if (eqb X Y) then
    if (eqb n 1) then
      (X', 0)
    else
      (* Формулы равны, n > 1 *)
      (Y, n - 1)
  else
    match Y with
    | f_atom _ => (Y, n)
    | f_not Y' => let (f_res, m) := (replace_subformula_int X X' Y' n) in
                 ((f_not f_res), m)
    | f_conj f1 f2 => let (f1_res, m) := (replace_subformula_int X X' f1 n) in
                    if (eqb m 0) then
                      ((f_conj f1_res f2), m)
                    else
                      let (f2_res, k) := (replace_subformula_int X X' f2 m) in
                      ((f_conj f1_res f2_res), k)
    | f_disj f1 f2 => let (f1_res, m) := (replace_subformula_int X X' f1 n) in
                    if (eqb m 0) then
                      ((f_disj f1_res f2), m)
                    else
                      let (f2_res, k) := (replace_subformula_int X X' f2 m) in
                      ((f_disj f1_res f2_res), k)
    | f_imp f1 f2 => let (f1_res, m) := (replace_subformula_int X X' f1 n) in
                    if (eqb m 0) then
                      ((f_imp f1_res f2), m)
                    else
                      let (f2_res, k) := (replace_subformula_int X X' f2 m) in
                      ((f_imp f1_res f2_res), k)
    | f_box Y' => let (f_res, m) := (replace_subformula_int X X' Y' n) in
                 ((f_box f_res), m)
    | f_diamond Y' => let (f_res, m) := (replace_subformula_int X X' Y' n) in
                 ((f_diamond f_res), m)
    end.

Definition replace_subformula {atom : Set} `{EqDec atom} (X X' Y : @formula atom) (n : nat) : @formula atom := fst (replace_subformula_int X X' Y n).

(* X - подформула Y *)
Fixpoint subformulab {atom : Set} `{EqDec atom} (X Y : @formula atom) : bool :=
  if eqb X Y then
    true
  else
    match Y with
    | f_not Y' => subformulab X Y'
    | f_conj F1 F2 => orb (subformulab X F1) (subformulab X F2)
    | f_disj F1 F2 => orb (subformulab X F1) (subformulab X F2)
    | f_imp F1 F2 => orb (subformulab X F1) (subformulab X F2)
    | f_box Y' => subformulab X Y'
    | f_diamond Y' => subformulab X Y'
    | _ => false
    end.

Inductive subformula {atom : Set} : (@formula atom) -> (@formula atom) -> Prop :=
| s_eq (X Y : @formula atom): (X = Y) -> subformula X Y
| s_not (X Y : @formula atom): subformula X Y -> subformula X $~ Y$ (* унарные конструкторы формулы *)
| s_box (X Y : @formula atom): subformula X Y -> subformula X $box Y$
| s_diamond (X Y : @formula atom): subformula X Y -> subformula X $diamond Y$
| s_conj1 (X F1 F2 : @formula atom): subformula X F1 -> subformula X $F1 /\ F2$ (* бинарные конструкторы формулы *)
| s_conj2 (X F1 F2 : @formula atom): subformula X F2 -> subformula X $F1 /\ F2$
| s_disj1 (X F1 F2 : @formula atom): subformula X F1 -> subformula X $F1 \/ F2$
| s_disj2 (X F1 F2 : @formula atom): subformula X F2 -> subformula X $F1 \/ F2$
| s_imp1 (X F1 F2 : @formula atom): subformula X F1 -> subformula X $F1 -> F2$
| s_imp2 (X F1 F2 : @formula atom): subformula X F2 -> subformula X $F1 -> F2$.


Theorem Replacement {atom : Set} `{EqDec atom} (Γ : @formula atom -> Prop) (X X' Y Y' : @formula atom) : forall n : nat, n <> 0 -> subformula X Y -> Γ |- $X <-> X'$ -> Y' = (replace_subformula X X' Y n) -> Γ |- $Y <-> Y'$.
Admitted.

(* Example 6.1.7 *)
Proposition E6_1_7 {atom : Set} (Γ : @formula atom -> Prop) (X : @formula atom) : Γ |- $diamond diamond ~X -> ~ box box X$.
Proof.
Admitted.


(* Exercize 6.1.3.1 -> *)
Proposition diamond_disj_1 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $diamond (X \/ Y) ->  (diamond X \/ diamond Y)$.
Proof.
  specialize (deMorganDisj_rev Γ X Y) as H1.
  apply reguarity in H1.
  specialize (conj_box Γ $~X$ $~Y$) as H2.
  specialize (meta_transitivity H2 H1) as H3.
  apply meta_contraposition in H3.
  specialize (deMorganConj Γ $box ~X$ $box ~Y$) as H4.
  specialize (meta_transitivity H3 H4) as H5.
  repeat rewrite <-Possibility in H5.
  exact H5.
Qed.

(* Exercize 6.1.3.1 <- *)
Proposition diamond_disj_2 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $(diamond X \/ diamond Y) -> diamond (X \/ Y)$.
Proof.
  specialize (deMorganDisj Γ X Y) as H1.
  apply reguarity in H1.
  specialize (box_conj Γ $~X$ $~Y$) as H2.
  specialize (meta_transitivity H1 H2) as H3.
  apply meta_contraposition in H3.
  specialize (deMorganConj_rev Γ $box ~X$ $box ~Y$) as H4.
  specialize (meta_transitivity H4 H3) as H5.
  repeat rewrite <-Possibility in H5.
  exact H5.
Qed.

(* Exercize 6.1.3.1 <-> *)
Proposition diamond_disj {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $diamond (X \/ Y) <-> (diamond X \/ diamond Y)$.
Proof.
  specialize (diamond_disj_1 Γ X Y) as H1.
  specialize (diamond_disj_2 Γ X Y) as H2.
  specialize (meta_conj_intro H1 H2) as H3.
  unfold equivalence.
  exact H3.
Qed.

(* Exercize 6.1.3.2 *)
Proposition E6_1_3_2 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $box (X -> Y) -> (diamond X -> diamond Y)$.
Proof.
  specialize (contraposition Γ X Y) as H1.
  apply reguarity in H1.
  specialize_axiom (@axiomK _ Γ $~Y$ $~X$) H2.
  specialize (meta_transitivity H1 H2) as H3.
  specialize (contraposition Γ $box ~ Y$ $box ~ X$) as H4.
  specialize (meta_transitivity H3 H4) as H5.
  repeat rewrite <-Possibility in H5.
  exact H5.
Qed.

(* Exercize 6.1.3.3 *)
Proposition E6_1_3_3 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $(box X \/ box Y) -> box(X \/ Y)$.
Proof.
  specialize_axiom (disj_intro1 Γ X Y) H1.
  specialize_axiom (disj_intro2 Γ X Y) H2.
  specialize_axiom (case_analysis Γ $box X$ $box Y$ $box (X \/ Y)$) H3.
  apply reguarity in H1.
  apply reguarity in H2.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Theorem formula_beq_true {atom : Set} `{EqDec atom} (X : @formula atom) :
 formula_beq X X = true.
Proof.
  rewrite formula_beq_eq.
  reflexivity.
Qed.

(* Exercize 6.1.3.4 *)
Proposition E6_1_3_4 {atom : Set} `{EqDec atom} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $box (X \/ Y) -> (box X \/ diamond Y)$.
Proof.
  rewrite Possibility.
  specialize (disj_comm Γ X Y) as Hdisj.
  assert (Hsubformula : subformula $X \/ Y$ $box (X \/ Y) -> box X \/ ~ box (~ Y)$).
  {
    apply s_imp1.
    apply s_box.
    apply s_eq.
    reflexivity.
  }

  assert (H3 : 1 <> 0).
  {
    discriminate.
  }

  specialize (Replacement Γ
                $X \/ Y$
                $Y \/ X$
                $box (X \/ Y) -> box X \/ ~ box (~ Y)$
                $box (Y \/ X) -> box X \/ ~ box (~ Y)$
               1
               H3 Hsubformula) as Hreplace.

  (* specialize (Hreplace Hdisj). *)
  (* assert (Hneq : ~(X = $box (X \/ Y)$)). *)
  (* { *)
  (*   intro H4. *)
  (*   Unset Printing Notations. *)

  (* assert (HY' : (replace_subformula $X \/ Y$ $Y \/ X$ $box (X \/ Y) -> box X \/ ~ box (~ Y)$ 1) = $box (Y \/ X) -> box X \/ ~ box (~ Y)$). *)
  (* { *)
  (*   unfold replace_subformula. *)
  (*   unfold replace_subformula_int. *)
  (*   simpl. *)
  (*   rewrite (formula_beq_true X). *)
  (*   rewrite (formula_beq_true Y). *)
  (*   simpl. *)
  (*   rewrite formula_beq_eq. *)
  (*   reflexivity. *)
  (* } *)

  (* symmetry in HY'. *)
  (* specialize (Hreplace HY'). *)
Admitted.

(* Exercize 6.1.3.5 *)
Proposition E6_1_3_5 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $(box X \/ diamond Y) -> diamond(X /\ Y)$.
Proof.
Admitted.

(* Exercize 6.1.3.6 *)
Proposition E6_1_3_6 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $(diamond X -> box Y) -> box(X \/ Y)$.
Proof.
Admitted.

End Syntactic.

Module Kripke.

Import Formula.

Class Frame :=
{
  worlds : Type;
  worlds_inh : inhabited worlds;
  accessible : worlds -> worlds -> Prop;
}.

Class Model {atom : Type} :=
{
  frame :: Frame;
  valuation : worlds -> atom -> Prop;
}.

Fixpoint valid {atom : Set} `(M : @Model atom) (Γ : worlds) (f : @formula atom) : Prop :=
  match f with
  | f_atom p => valuation Γ p
  | f_not f' => ~(valid M Γ f')
  | f_conj f1 f2 => (valid M Γ f1) /\ (valid M Γ f2)
  | f_disj f1 f2 => (valid M Γ f1) \/ (valid M Γ f2)
  | f_imp f1 f2 => (valid M Γ f1) -> (valid M Γ f2)
  | f_box f' => forall w, (accessible Γ w) -> (valid M w f')
  | f_diamond f' => exists w, (accessible Γ w) /\ (valid M w f')
  end.

Definition valid_in_frame {atom : Set} `(Fr : Frame) (f : @formula atom) : Prop :=
  forall (V : worlds -> atom -> Prop),
    forall w, valid {| frame := Fr;
                  valuation := V |} w f.

Import Relation.

(* Exercize 5.2.1 стр. 81 *)
Proposition Ex5_2_1 {atom : Set} `(M : @Model atom) (Γ : worlds) (X Y : @formula atom) : valid M Γ $X <-> Y$ <-> ((valid M Γ X) <-> (valid M Γ Y)).
Proof.
  split ; intro H.
  - simpl in H.
    destruct H as [H1 H2].
    split.
    + intro HΓx.
      apply H1 in HΓx as HΓy.
      exact HΓy.
    + intro HΓy.
      apply H2 in HΓy as HΓx.
      exact HΓx.
  - simpl.
    split.
    + intro HΓx.
      rewrite H in HΓx.
      exact HΓx.
    + intro HΓy.
      rewrite <-H in HΓy.
      exact HΓy.
Qed.

(* Exercize 5.2.2 стр. 81 *)
Proposition Ex5_2_2 {atom : Set} `(M : @Model atom) (X : @formula atom) : forall Γ : worlds, valid M Γ $box X <-> ~ diamond ~ X$.
Proof.
  hnf.
  split.
  - intro H.
    unfold not.
    intro H1.
    destruct H1 as [Δ [Γ_R_Δ H1]].
    specialize (H Δ Γ_R_Δ).
    apply H1 in H.
    exact H.
  - intro H.
    intros Δ Γ_R_Δ.
    simpl in H.
    specialize (not_ex_all_not _ _ H) as H1.
    simpl in H1.
    specialize (H1 Δ).
    apply not_and_or in H1.
    destruct H1 as [H1 | H1].
    + apply H1 in Γ_R_Δ.
      destruct Γ_R_Δ.
    + apply NNPP in H1.
      exact H1.
Qed.

Proposition meta_Ex5_2_2 {atom : Set} `(M : @Model atom) (X : @formula atom) : forall Γ : worlds, valid M Γ $box X$ <-> valid M Γ $~ diamond ~ X$.
Proof.
  intro Γ.
  split.
  - intro Hbox.
    hnf in Hbox.
    hnf.
    intro Hnd.
    hnf in Hnd.
    destruct Hnd as [Δ [Γ_R_Δ Hnd]].
    hnf in Hnd.
    specialize (Hbox Δ Γ_R_Δ).
    apply Hnd in Hbox.
    exact Hbox.
  - intro Hnd.
    hnf in Hnd.
    hnf.
    intros Δ Γ_R_Δ.
    simpl in Hnd.
    specialize (not_ex_all_not _ _ Hnd) as H1.
    simpl in H1.
    specialize (H1 Δ).
    apply not_and_or in H1.
    destruct H1.
    + apply H in Γ_R_Δ.
      destruct Γ_R_Δ.
    + apply NNPP in H.
      exact H.
Qed.

(* Exercize 5.2.3.1 стр. 81 *)
Proposition Ex5_2_3_1 {atom : Set} `(M : @Model atom) (Γ : worlds) (P : @formula atom) : ~ (exists w, accessible Γ w) -> valid M Γ $box P$.
Proof.
  intro H.
  simpl.
  intros w HΓ_R_w.
  specialize (ex_intro _ w HΓ_R_w) as Hex.
  apply H in Hex.
  destruct Hex.
Qed.

(* Exercize 5.2.3.2 стр. 81 *)
Proposition Ex5_2_3_2 {atom : Set} (M : @Model atom) (Γ : worlds) (P : @formula atom) : ~ (exists w, accessible Γ w) -> ~ (valid M Γ $diamond P$).
Proof.
  intro H.
  simpl.
  intro Hex.
  destruct Hex as [w [HΓ_R_w Hw_p]].
  specialize (ex_intro _ w HΓ_R_w) as Hex.
  apply H in Hex.
  exact Hex.
Qed.

Module Example_5_3_1.

  Inductive atom : Type :=
  | P : atom
  | Q : atom.

  Inductive worlds3 : Type :=
  | Γ : worlds3
  | Δ : worlds3
  | Ω : worlds3.

  Definition R3 (w1 w2 : worlds3) : Prop :=
  match w1, w2 with
  | Γ, Δ  => True
  | Γ, Ω => True
  | _, _ => False
  end.

  Definition V3 (w : worlds3) (a : atom) : Prop :=
    match w, a with
    | Δ, P => True
    | Ω, Q => True
    | _, _ => False
    end.

  Lemma worlds3_inhabited : inhabited worlds3.
  Proof.
    apply (inhabits Γ).
  Qed.

  Definition F1 : Frame :=
  {|
    worlds := worlds3;
    worlds_inh := worlds3_inhabited;
    accessible := R3;
  |}.

  Definition M1 : Model :=
  {|
    frame := F1;
    valuation := V3
  |}.

  Definition f (a: atom) : @formula atom :=
    f_atom a.

  Coercion f: atom >-> formula.

  Proposition Delta_P_or_Q : valid M1 Δ $P \/ Q$.
  Proof.
    simpl.
    left.
    apply I.
  Qed.

  Proposition Omega_P_or_Q : valid M1 Ω $P \/ Q$.
  Proof.
    simpl.
    right.
    apply I.
  Qed.

  Proposition Gamma_box_P_or_Q : valid M1 Γ $box (P \/ Q)$.
  Proof.
    hnf.
    intros w H.
    destruct w ; simpl in H.
    - destruct H.
    - apply Delta_P_or_Q.
    - apply Omega_P_or_Q.
  Qed.

  Proposition Gamma_box_P_invalid : ~ (valid M1 Γ $box P$).
  Proof.
    unfold not.
    intro H.
    simpl in H.
    specialize (H Ω).
    simpl in H.
    specialize (H I).
    apply H.
  Qed.

  Proposition Gamma_box_Q_invalid : ~ (valid M1 Γ $box Q$).
  Proof.
    unfold not.
    intro H.
    simpl in H.
    specialize (H Δ).
    simpl in H.
    specialize (H I).
    apply H.
  Qed.

  Proposition Gamma_box_P_or_box_Q_invalid : ~ (valid M1 Γ $box P \/box Q$).
  Proof.
    intro H.
    simpl in H.
    destruct H.
    - apply Gamma_box_P_invalid in H.
      exact H.
    - apply Gamma_box_Q_invalid in H.
      exact H.
  Qed.

  Proposition Gamma_impl_invalid : ~ (valid M1 Γ $box (P \/ Q) -> (box P \/box Q)$).
  Proof.
    unfold not.
    intro H.
    hnf in H.
    specialize (H Gamma_box_P_or_Q).
    destruct H.
    - apply Gamma_box_P_invalid in H.
      exact H.
    - apply Gamma_box_Q_invalid in H.
      exact H.
  Qed.

  Proposition Gamma_d_P_and_d_Q : valid M1 Γ $diamond P /\ diamond Q$.
  Proof.
    simpl.
    split.
    - exists Δ.
      split.
      + apply I.
      + simpl.
        apply I.
    - exists Ω.
      split.
      + apply I.
      + simpl.
        apply I.
  Qed.

  (* Exercize 5.3.1 *)
  Proposition Gamma_diamond_invalid : ~ (valid M1 Γ $(diamond P /\ diamond Q) -> diamond(P /\ Q)$).
  Proof.
    unfold not.
    intro H.
    hnf in H.
    specialize (H Gamma_d_P_and_d_Q).
    destruct H as [w H].
    destruct w.
    - destruct H as [H _].
      exact H.
    - simpl in H.
      destruct H as [_ [_ H]].
      exact H.
    - simpl in H.
      destruct H as [_ [H _]].
      exact H.
  Qed.
End Example_5_3_1.

Module Example_5_3_2.

  Inductive atom : Set :=
  | P : atom.

  Inductive worlds3 : Type :=
  | Γ : worlds3
  | Δ : worlds3
  | Ω : worlds3.

  Definition R3 (w1 w2 : worlds3) : Prop :=
  match w1, w2 with
  | Γ, Δ  => True
  | Δ, Ω => True
  | _, _ => False
  end.

  Definition V3 (w : worlds3) (a : atom) : Prop :=
    match w, a with
    | Δ, P => True
    | _, _ => False
    end.

  Lemma worlds3_inhabited : inhabited worlds3.
  Proof.
    apply (inhabits Γ).
  Qed.

  Definition F1 : Frame :=
  {|
    worlds := worlds3;
    worlds_inh := worlds3_inhabited;
    accessible := R3;
  |}.

  Definition M1 : Model :=
  {|
    frame := F1;
    valuation := V3
  |}.

  Definition f (a: atom) : @formula atom :=
    f_atom a.

  Coercion f: atom >-> formula.

  Proposition Gamma_box_P : valid M1 Γ $box P$.
  Proof.
    hnf.
    intros w H.
    destruct w ; simpl in H.
    - destruct H.
    - simpl.
      exact I.
    - destruct H.
  Qed.

  Proposition Ex_5_3_2 : ~(valid M1 Γ $box P -> box box P$).
  Proof.
    intro H.
    hnf in H.
    specialize (H Gamma_box_P).
    hnf in H.
    specialize (H Δ).
    assert (H1 : @accessible (@frame atom M1) Γ Δ).
    {
      simpl.
      exact I.
    }

    specialize (H H1).
    hnf in H.
    specialize (H Ω).
    clear H1.
    assert (H1 : @accessible (@frame atom M1) Δ Ω).
    {
      simpl.
      exact I.
    }

    specialize (H H1).
    simpl in H.
    exact H.
  Qed.

End Example_5_3_2.

Module Example_5_3_3.

  Inductive atom : Set :=
  | P : atom.

  Inductive worlds2 : Type :=
  | Γ : worlds2
  | Δ : worlds2.

  Definition R2 (w1 w2 : worlds2) : Prop :=
  match w1, w2 with
  | Γ, Δ  => True
  | _, _ => False
  end.

  Definition V2 (w : worlds2) (a : atom) : Prop :=
    match w, a with
    | Δ, P => True
    | _, _ => False
    end.

  Lemma worlds2_inhabited : inhabited worlds2.
  Proof.
    apply (inhabits Γ).
  Qed.

  Definition F1 : Frame :=
  {|
    worlds := worlds2;
    worlds_inh := worlds2_inhabited;
    accessible := R2;
  |}.

  Definition M1 : Model :=
  {|
    frame := F1;
    valuation := V2
  |}.

  Definition f (a: atom) : @formula atom :=
    f_atom a.

  Coercion f: atom >-> formula.

  Proposition Gamma_diamond_P : valid M1 Γ $diamond P$.
  Proof.
    hnf.
    exists Δ.
    split.
    - simpl.
      exact I.
    - simpl.
      exact I.
  Qed.

  Proposition Delta_not_diamond_P : ~ valid M1 Δ $diamond P$.
  Proof.
    apply Ex5_2_3_2.
    unfold not.
    intro H.
    destruct H as [w Δ_R_w].
    simpl in Δ_R_w.
    exact Δ_R_w.
  Qed.

  (* Example 5.3.3 стр. 82 *)
  Proposition Ex_5_3_3 : ~(valid M1 Γ $diamond P -> box diamond P$).
  Proof.
    unfold not.
    intro H.
    hnf in H.
    specialize (H Gamma_diamond_P).
    hnf in H.
    specialize (H Δ).
    assert (Γ_R_Δ : @accessible (@frame atom M1) Γ Δ).
    {
      simpl.
      exact I.
    }

    specialize (H Γ_R_Δ).
    apply Delta_not_diamond_P in H.
    exact H.
Qed.
End Example_5_3_3.

Module Example_5_3_4.
  Inductive atom : Set :=
  | P : atom
  | Q : atom.

  Inductive worlds5 : Type :=
  | Γ : worlds5
  | Δ : worlds5
  | Ε : worlds5
  | Ζ : worlds5
  | Η : worlds5.

  Definition R5 (w1 w2 : worlds5) : Prop :=
  match w1, w2 with
  | Γ, Δ  => True
  | Γ, Ε  => True
  | Δ, Ζ => True
  | Ε, Η => True
  | _, _ => False
  end.

  Definition V5 (w : worlds5) (a : atom) : Prop :=
    match w, a with
    | Ζ, P => True
    | Η, Q => True
    | _, _ => False
    end.

  Lemma worlds5_inhabited : inhabited worlds5.
  Proof.
    apply (inhabits Γ).
  Qed.

  Definition F1 : Frame :=
  {|
    worlds := worlds5;
    worlds_inh := worlds5_inhabited;
    accessible := R5;
  |}.

  Definition M1 : Model :=
  {|
    frame := F1;
    valuation := V5
  |}.

  Definition f (a: atom) : @formula atom :=
    f_atom a.

  Coercion f: atom >-> formula.

  Proposition diamond_box_Gamma : valid M1 Γ $diamond box P /\ diamond box Q$.
  Proof.
    hnf.
    split.
    - hnf.
      exists Δ.
      split.
      + simpl.
        exact I.
      + hnf.
        intros w Δ_R_w.
        destruct w ; simpl in Δ_R_w ; destruct Δ_R_w.
        simpl.
        exact I.
    - hnf.
      exists Ε.
      split.
      + simpl.
        exact I.
      + hnf.
        intros w Δ_R_w.
        destruct w ; simpl in Δ_R_w ; destruct Δ_R_w.
        simpl.
        exact I.
  Qed.

  Proposition conj_invalid_Δ : ~ (valid M1 Δ $box (P /\ Q)$).
  Proof.
    unfold not.
    intro H.
    hnf in H.
    specialize (H Ζ).
    assert (Δ_R_Ζ : @accessible (@frame atom M1) Δ Ζ).
    {
      simpl.
      exact I.
    }

    specialize (H Δ_R_Ζ).
    hnf in H.
    destruct H as [H1 H2].
    simpl in H2.
    exact H2.
  Qed.

  Proposition conj_invalid_Ε : ~ (valid M1 Ε $box (P /\ Q)$).
  Proof.
    unfold not.
    intro H.
    hnf in H.
    specialize (H Η).
    assert (Ε_R_Η : @accessible (@frame atom M1) Ε Η).
    {
      simpl.
      exact I.
    }

    specialize (H Ε_R_Η).
    hnf in H.
    destruct H as [H1 H2].
    simpl in H1.
    destruct H1.
  Qed.

  (* Example 5.3.4 стр. 82 *)
  Proposition Ex_5_3_4 : ~(valid M1 Γ $(diamond box P /\ diamond box Q) -> diamond box (P /\ Q)$).
  Proof.
    unfold not.
    intro H.
    hnf in H.
    specialize (H diamond_box_Gamma).
    hnf in H.
    destruct H as [w [Γ_R_w Hvalid]].
    destruct w ; simpl in Γ_R_w ; destruct Γ_R_w.
    - specialize (conj_invalid_Δ Hvalid) as Hcontra.
      exact Hcontra.
    - specialize (conj_invalid_Ε Hvalid) as Hcontra.
      exact Hcontra.
  Qed.

End Example_5_3_4.

Module Example_5_3_5.
  Inductive atom : Set :=
  | P : atom.

  Inductive worlds2 : Type :=
  | Γ : worlds2
  | Δ : worlds2.

  Definition R2 (w1 w2 : worlds2) : Prop :=
  match w1, w2 with
  | Γ, Δ  => True
  | Δ, Δ  => True
  | _, _ => False
  end.

  Definition V2 (w : worlds2) (a : atom) : Prop :=
    match w, a with
    | Δ, P => True
    | _, _ => False
    end.

  Lemma worlds2_inhabited : inhabited worlds2.
  Proof.
    apply (inhabits Γ).
  Qed.

  Definition F1 : Frame :=
  {|
    worlds := worlds2;
    worlds_inh := worlds2_inhabited;
    accessible := R2;
  |}.

  Definition M1 : Model :=
  {|
    frame := F1;
    valuation := V2
  |}.

  Definition f (a: atom) : @formula atom :=
    f_atom a.

  Coercion f: atom >-> formula.

  Fixpoint n_box {atom : Set} (f : @formula atom) (n : nat) :=
    match n with
    | 0 => f
    | S n' => f_box (n_box f n')
    end.

  (* Example 5.3.5.1 стр. 82 *)
  Proposition Ex_5_3_5_1 : forall n : nat, valid M1 Δ (n_box P n).
  Proof.
    intro n.
    induction n as [|n' IH].
    - unfold n_box.
      simpl.
      exact I.
    - hnf.
      intros w Δ_R_w.
      destruct w.
      + simpl in Δ_R_w.
        destruct Δ_R_w.
      + apply IH.
  Qed.

  Proposition Ex_5_3_5_2 : forall n : nat, valid M1 Γ (n_box P (S n)).
  Proof.
    intro n.
    destruct n as [|n'].
    - unfold n_box.
      hnf.
      intros w Γ_R_w.
      simpl.
      destruct w.
      + simpl in Γ_R_w.
        destruct Γ_R_w.
      + simpl.
        exact I.
    - hnf.
      intros w Γ_R_w.
      destruct w.
      + simpl in Γ_R_w.
        destruct Γ_R_w.
      + apply Ex_5_3_5_1.
  Qed.

  Proposition Ex_5_3_5_3 : forall n : nat, ~(valid M1 Γ (f_imp (n_box P (S n)) P)).
  Proof.
    unfold not.
    intros n H.
    hnf in H.
    specialize (Ex_5_3_5_2 n) as H1.
    specialize (H H1).
    simpl in H.
    exact H.
  Qed.

End Example_5_3_5.

(* Example 5.3.7 стр. 83 *)
Example Ex5_3_7 {atom : Set} `(M : @Model atom) (w0 : worlds) (P : @formula atom) : (transitive (@accessible frame)) -> valid M w0 $box P -> box box P$.
Proof.
  intro Htrans.
  unfold transitive in Htrans.
  hnf.
  intros Hbox.
  hnf.
  intros w1 Hw0_R_w1.
  hnf.
  intros w2 Hw1_R_w2.
  specialize (Htrans w0 w1 w2).
  specialize (Htrans Hw0_R_w1 Hw1_R_w2) as Hw0_R_w2.
  hnf in Hbox.
  specialize (Hbox w2 Hw0_R_w2).
  exact Hbox.
Qed.

(* Excersize 5.3.4.1 left стр. 84 *)
Proposition E5_3_4_1_left {atom : Set} `(M : @Model atom) (w0 : worlds) (P Q : @formula atom) : valid M w0 $box P /\ box Q -> box (P /\ Q)$.
Proof.
  hnf.
  intros H.
  simpl.
  intros w w0_R_w.
  simpl in H.
  destruct H as [H1 H2].
  specialize (H1 w w0_R_w).
  specialize (H2 w w0_R_w).
  specialize (conj H1 H2) as H3.
  exact H3.
Qed.

(* Excersize 5.3.4.1 right *)
Proposition E5_3_4_1_right {atom : Set} `(M : @Model atom) (w0 : worlds) (P Q : @formula atom) : valid M w0 $box (P /\ Q) -> box P /\ box Q$.
Proof.
  simpl.
  intros Hbox_conj.
  split.
  - intros w w0_R_w.
    specialize (Hbox_conj w w0_R_w).
    destruct Hbox_conj as [Hp _].
    exact Hp.
  - intros w w0_R_w.
    specialize (Hbox_conj w w0_R_w).
    destruct Hbox_conj as [_ Hq].
    exact Hq.
Qed.

(* 5.3.4.2 стр. 84 *)
Proposition E5_3_4_2 {atom : Set} `(M : @Model atom) (w0 : worlds) (P Q : @formula atom) : valid M w0 $box (P -> Q) -> box P -> box Q$.
Proof.
  simpl.
  intros Hbox_impl Hbox_P.
  intros w Hw0_R_w.
  specialize (Hbox_P w Hw0_R_w) as Hp.
  specialize (Hbox_impl w Hw0_R_w Hp) as Hq.
  exact Hq.
Qed.

(* Excersize 5.4.1 стр. 87 *)
Proposition E5_4_1 {atom : Set} `(M : @Model atom) (w0 : worlds) (P : @formula atom) : (serial (@accessible frame)) -> valid M w0 $box P -> diamond P$.
Proof.
  intro Hserial.
  unfold serial in Hserial.
  simpl.
  intro Hbox.
  specialize (Hserial w0).
  destruct Hserial as [w1 w0_R_w1].
  exists w1.
  split.
  - exact w0_R_w1.
  - specialize (Hbox w1 w0_R_w1) as Hw1_p.
    exact Hw1_p.
Qed.

(* Excersize 5.4.2 стр. 87 *)
(* Proposition E5_4_2 {atom : Set} `(M : @Model atom) (w0 : worlds) (P : @formula atom) : valid M w0 P <-> valid M w0 $box P$. *)
(* Proof. *)
(*   split. *)
(*   - intro H. *)
(*     simpl. *)
(*     intros w1 w0_R_w1. *)

(* 5.4.3.1 стр. 87 *)
Proposition boxP_P {atom : Set} `(M : @Model atom) (w0 : worlds) (P : @formula atom) : (reflexive (@accessible frame)) -> valid M w0 $box P -> P$.
Proof.
  intros Hrefl.
  unfold reflexive in Hrefl.
  simpl.
  intro Hbox.
  specialize (Hrefl w0).
  specialize (Hbox w0 Hrefl).
  exact Hbox.
Qed.

(* 5.4.3.2 стр. 87 *)
Theorem E5_4_3_2 {atom : Set} `(M : @Model atom) (w0 : worlds) (P : @formula atom) : (symmetric (@accessible frame)) -> valid M w0 $P -> box diamond P$.
Proof.
  intro Hsym.
  unfold symmetric in Hsym.
  simpl.
  intro H.
  intros w w0_R_w.
  specialize (Hsym w0 w w0_R_w) as w_R_w0.
  exists w0.
  split.
  - exact w_R_w0.
  - exact H.
Qed.

Theorem E5_4_3_3 {atom : Set} `(M : @Model atom) (w0 : worlds) (P : @formula atom) : (symmetric (@accessible frame)) -> (transitive (@accessible frame)) -> valid M w0 $diamond P -> box diamond P$.
Proof.
  intros Hsym Htrans.
  unfold symmetric in Hsym.
  unfold transitive in Htrans.
  simpl.
  intro Hdiamond.
  intros w w0_R_w.
  destruct Hdiamond as [w1 Hdiamond].
  destruct Hdiamond as [w0_R_w1 Hw1_P].
  specialize (Hsym w0 w w0_R_w) as w_R_w0.
  specialize (Htrans w w0 w1 w_R_w0 w0_R_w1) as w_R_w1.
  exists w1.
  split.
  - exact w_R_w1.
  - exact Hw1_P.
Qed.

Theorem E5_4_3_4 {atom : Set} `(M : @Model atom) (w0 : worlds) (P : @formula atom) : (euclidian (@accessible frame)) -> valid M w0 $diamond P -> box diamond P$.
Proof.
  intro Heuc.
  unfold euclidian in Heuc.
  simpl.
  intro Hexists.
  destruct Hexists as [w [w0_R_w HwP]].
  intros w1 w0_R_w1.
  specialize (Heuc w0 w1 w).
  specialize (Heuc w0_R_w1 w0_R_w) as w1_R_w.
  exists w.
  split.
  - exact w1_R_w.
  - exact HwP.
Qed.

Theorem E5_4_5_trans_valid {atom : Set} (F : Frame) : (transitive (@accessible F)) -> (forall φ : @formula atom, valid_in_frame F $box φ -> box box φ$).
Proof.
  intro Htrans.
  unfold transitive in Htrans.
  unfold valid_in_frame.
  intros φ val w1 Hbox.
  simpl.
  intros w2 w1_R_w2 w3 w2_R_w3.
  specialize (Htrans w1 w2 w3).
  specialize (Htrans w1_R_w2 w2_R_w3) as w1_R_w3.
  simpl in Hbox.
  specialize (Hbox w3 w1_R_w3) as Hw3_p.
  exact Hw3_p.
Qed.

Theorem E5_4_5_valid_trans {atom : Set} (Hinh : inhabited atom) (F : Frame) :
  (forall φ : @formula atom, valid_in_frame F $box φ -> box box φ$) -> transitive (@accessible F).
Proof.
  intro H.
  unfold valid_in_frame in H.
  unfold transitive.
  intros w v u w_R_v v_R_u.
  set (V := fun (x : worlds) (_ : atom) => accessible w x).
  destruct Hinh as [P].
  specialize (H (f_atom P) V w).
  simpl in H.
  assert (Hbox : forall x : worlds, accessible w x -> V x P).
  {
    intros x w_R_x.
    unfold V.
    exact w_R_x.
  }

  specialize (H Hbox).
  specialize (H v).
  specialize (H w_R_v).
  specialize (H u).
  specialize (H v_R_u).
  unfold V in H.
  exact H.
Qed.

Theorem E5_4_5 {atom : Set} (Hinh : inhabited atom) (F : Frame) : (transitive accessible) <-> (forall φ : @formula atom, valid_in_frame F $box φ -> box box φ$).
Proof.
  split.
  - apply E5_4_5_trans_valid.
  - apply (E5_4_5_valid_trans Hinh).
Qed.

(* Formalization of logics *)

Class FrameSerial (F : Frame) :=
  serial_accessible : serial (@accessible F).

Class FrameRefl (F : Frame) :=
  refl_accessible : reflexive (@accessible F).

Class FrameSym (F : Frame) :=
  sym_accessible : symmetric (@accessible F).

Class FrameTrans (F : Frame) :=
  trans_accessible : transitive (@accessible F).

Class FrameEucl (F : Frame) :=
  eucl_accessible : euclidian (@accessible F).

Class FrameLinear (F : Frame) :=
  linear_accessible : linear (@accessible F).


(* --- Logic K --- *)
(* No extra conditions: K is just Frame + Model *)

Definition LogicD (F : Frame) := FrameSerial F.
Definition LogicT (F : Frame) := FrameRefl F.
Definition LogicB (F : Frame) := FrameRefl F * FrameSym F.
Definition LogicS4 (F : Frame) := FrameRefl F * FrameTrans F.
Definition LogicS5 (F : Frame) := FrameRefl F * FrameSym F * FrameTrans F.
Definition LogicS5' (F : Frame) := FrameRefl F * FrameEucl F.
Definition LogicS43 (F : Frame) := FrameRefl F * FrameTrans F * FrameLinear F.

Proposition E5_4_7_1 {atom : Set} `(F : Frame) (S43 : LogicS43 F) (P Q : @formula atom) :
  valid_in_frame F $box (box P -> box Q) \/ box(box Q -> box P)$.
Proof.
  simpl.
  destruct S43 as [S43 Hlinear].
  destruct S43 as [Hrefl Htrans].
  unfold FrameLinear in Hlinear.
  unfold linear in Hlinear.
  unfold FrameRefl in Hrefl.
  unfold reflexive in Hrefl.
  unfold FrameTrans in Htrans.
  unfold transitive in Htrans.

  unfold valid_in_frame.
  intros V w.
  specialize (classic ((valid {| frame := F; valuation := V |} w $box (box P -> box Q)$) \/ (valid {| frame := F; valuation := V |} w $box (box Q -> box P)$))) as H.
  destruct H.
  - exact H.
  - apply not_or_and in H.
    destruct H as [H1 H2].
    simpl in H1.
    apply not_all_ex_not in H1.
    destruct H1 as [w1 H1].
    apply imply_to_and in H1.
    destruct H1 as [w_R_w1 H1].
    simpl in H2.
    apply not_all_ex_not in H2.
    destruct H2 as [w2 H2].
    apply imply_to_and in H2.
    destruct H2 as [w_R_w2 H2].
    specialize (Hlinear w w1 w2 w_R_w1 w_R_w2) as H3.
    destruct H3 as [H3 | H3].
    + hnf.
    apply not_all_ex_not in H1.
    destruct H1 as [H5 H6].
Admitted.

Proposition E5_4_7_2 {atom : Set} (M : @Model atom) (S43 : LogicS43 (@frame atom M)) (w0 : worlds) (P : @formula atom) : ~(valid M w0 $P -> box diamond P$).
Proof.
  simpl.
  intro H.
Admitted.

(* Excersize 5.4.7.3 стр. 87, 88 *)
Proposition E5_4_7_3 {atom : Set} (M : @Model atom) (S43 : LogicS43 (@frame atom M)) (w0 : worlds) (P Q : @formula atom) : valid M w0 $diamond box (P -> Q) -> (diamond box P -> diamond box Q)$.
Proof.
  simpl.
  intros H1 H2.
  destruct H1 as [w1 [w0_R_w1 H_w1_pq]].
  destruct H2 as [w2 [w0_R_w2 H_w2_box_P]].
  destruct S43 as [S43 Hlinear].
  destruct S43 as [Hrefl Htrans].
  (* Раскрыли все свойства отношений *)
  unfold FrameLinear in Hlinear.
  unfold linear in Hlinear.
  unfold FrameRefl in Hrefl.
  unfold reflexive in Hrefl.
  unfold FrameTrans in Htrans.
  unfold transitive in Htrans.

  specialize (Hlinear w0 w1 w2) as H.
  specialize (H w0_R_w1 w0_R_w2).
  destruct H as [w1_R_w2 | w2_R_w1].
  - exists w2.
    split.
    + exact w0_R_w2.
    + intros w3 w2_R_w3.
      specialize (Htrans w1 w2 w3).
      specialize (Htrans w1_R_w2 w2_R_w3) as w1_R_w3.
      specialize (H_w1_pq w3 w1_R_w3).
      specialize (H_w2_box_P w3 w2_R_w3) as H_w3_p.
      specialize (H_w1_pq H_w3_p).
      exact H_w1_pq.
  - exists w1.
    split.
    + exact w0_R_w1.
    + intros w3 w1_R_w3.
      specialize (Htrans w2 w1 w3).
      specialize (Htrans w2_R_w1 w1_R_w3) as w2_R_w3.
      specialize (H_w1_pq w3 w1_R_w3).
      specialize (H_w2_box_P w3 w2_R_w3) as H_w3_p.
      specialize (H_w1_pq H_w3_p).
      exact H_w1_pq.
Qed.

(* Worlds - тип для миров *)
(* Record Model {atom : Set} (Worlds : Type) := *)
(* { *)
(*   G : list Worlds; *)
(*   R : Worlds -> Worlds -> bool; *)
(*   values : Worlds -> atom -> bool; *)
(* }. *)

(* Вычисление формулы в мире *)
(* Fixpoint eval {atom : Set} {Worlds : Type} (M : Type) `{M : @Model atom Worlds} (World : Worlds) (f : @formula atom) : bool := *)
(*   match f with *)
(*   | f_atom a => values World a *)
(*   | f_not f' => negb (eval M World f') *)
(*   | f_conj f1 f2 => conjb (eval M World f1) (eval M World f2) *)
(*   | f_disj f1 f2 => disjb (eval M World f1) (eval M World f2) *)
(*   | f_imp f1 f2 => implb (eval M World f1) (eval M World f2) *)
(*   | f_box f1 f2 => formula -> formula *)
(*   | f_diamond f1 f2 => formula -> formula. *)
(*   | _ => true *)
(*   end. *)
End Kripke.

Module Tableaus.
  Record node {atom : Set} := { world : nat; f : @formula atom; sign : bool }.
  (* I - modal indices (agents) *)
  Record edge {I : Type} := { iE : I; src : nat; dst : nat }.
  Record branch {atom : Set} {I : Type} := { nodes : list (@node atom); edges : list (@edge I) }.

  Definition mem_node {atom : Set} {I : Type} (x : @node atom) (Γ : @branch atom I) := In x Γ.(nodes).
  Definition mem_edge {atom : Set} {I : Type} (e : @edge I) (Γ : @branch atom I) := In e Γ.(edges).

  Inductive step {atom : Set} {I : Type} : (@branch atom I) -> list (@branch atom I) -> Prop :=
  | conj_T Γ w φ ψ :
    mem_node {|world := w; f := $φ /\ ψ$; sign := true|} Γ ->
    step Γ [ {| nodes := {|world := w; f := φ; sign := true|} ::
                         {|world := w; f := ψ; sign := true|} :: Γ.(nodes);
               edges := Γ.(edges) |} ]
  | conj_F Γ w φ ψ :
    mem_node {|world := w; f := $φ /\ ψ$; sign := false|} Γ ->
    step Γ [ {| nodes := {|world := w; f := φ; sign := false|} :: Γ.(nodes);
                edges := Γ.(edges) |};
             {| nodes := {|world := w; f := ψ; sign := false|} :: Γ.(nodes);
                edges := Γ.(edges) |}
           ]
  | disj_T Γ w φ ψ :
    mem_node {|world := w; f := $φ \/ ψ$; sign := true|} Γ ->
    step Γ [ {| nodes := {|world := w; f := φ; sign := true|} :: Γ.(nodes);
                edges := Γ.(edges) |};
             {| nodes := {|world := w; f := ψ; sign := true|} :: Γ.(nodes);
                edges := Γ.(edges) |}
           ]
  | disj_F Γ w φ ψ :
    mem_node {|world := w; f := $φ \/ ψ$; sign := false|} Γ ->
    step Γ [ {| nodes := {|world := w; f := φ; sign := false|} ::
                         {|world := w; f := ψ; sign := false|} :: Γ.(nodes);
               edges := Γ.(edges) |} ]
  | impl_T Γ w φ ψ :
    mem_node {|world := w; f := $φ -> ψ$; sign := true|} Γ ->
    step Γ [ {| nodes := {|world := w; f := φ; sign := false|} :: Γ.(nodes);
                edges := Γ.(edges) |};
             {| nodes := {|world := w; f := ψ; sign := true|} :: Γ.(nodes);
                edges := Γ.(edges) |}
           ]
  | impl_F Γ w φ ψ :
    mem_node {|world := w; f := $φ -> ψ$; sign := false|} Γ ->
    step Γ [ {| nodes := {|world := w; f := φ; sign := true|} ::
                         {|world := w; f := ψ; sign := false|} :: Γ.(nodes);
               edges := Γ.(edges) |} ]
  | double_neg Γ w φ :
    mem_node {|world := w; f := $~ ~φ$; sign := true|} Γ ->
    step Γ [ {| nodes := {|world := w; f := φ; sign := true|} :: Γ.(nodes);
               edges := Γ.(edges) |} ]
  (* узел с одним отрицанием *)
  (* или убрать пометки? *)
  | diamond_T Γ w (i : I) φ (w' : nat) :
    mem_node {|world := w; f := $diamond φ$; sign := true|} Γ ->
        (* add fresh world w' *)
    step Γ [ {| nodes := {|world := w'; f := φ; sign := true|} :: Γ.(nodes);
                edges := {|iE:=i; src := w; dst := w'|} :: Γ.(edges) |} ]
  | box_F Γ w (i : I) φ (w' : nat) :
    mem_node {|world := w; f := $box φ$; sign := false|} Γ ->
        (* add fresh world w' *)
    step Γ [ {| nodes := {|world := w'; f := φ; sign := false|} :: Γ.(nodes);
               edges := {|iE:=i; src := w; dst := w'|} :: Γ.(edges) |} ]
  | box_T Γ w (i : I) φ (w' : nat) :
    mem_node {|world := w; f := $box φ$; sign := true|} Γ ->
    mem_edge {|iE :=i; src := w; dst := w'|} Γ ->
    step Γ [ {| nodes := {|world := w'; f := φ; sign := true|} :: Γ.(nodes);
               edges := Γ.(edges) |} ]
  | diamond_F Γ w (i : I) φ (w' : nat) :
    mem_node {|world := w; f := $diamond φ$; sign := false|} Γ ->
    mem_edge {|iE :=i; src := w; dst := w'|} Γ ->
    step Γ [ {| nodes := {|world := w'; f := φ; sign := false|} :: Γ.(nodes);
               edges := Γ.(edges) |} ].

  (* Можно доказать, что atomically closed, а потом по индукции доказать,
    что из атомарной замкнутости следует замкнутость для любых формул
  *)
  (* Branch closes if it has w F and w ~F together *)
  Definition closed {atom : Set} {I : Type} (Γ : @branch atom I) : Prop :=
  exists w (F : @formula atom),
    mem_node {|world:= w; f := F; sign := true|} Γ /\
    mem_node {|world := w; f:= F; sign := false|} Γ.

  Inductive closed_tree {atom : Set} {I : Type} : @branch atom I -> Prop :=
  | ct_closed (Γ : @branch atom I) :
    closed Γ -> closed_tree Γ
  | ct_step Γ Δs :
    step Γ Δs ->
    (forall Δ, In Δ Δs -> closed_tree Δ) ->
    closed_tree Γ.

  Inductive atom2 : Type :=
  | P : atom2
  | Q : atom2.

  Definition conv (a: atom2) : @formula atom2 :=
    f_atom a.

  Coercion conv: atom2 >-> formula.

  (* (p ∧ q) -> p  *)
  Definition Γ0 : @branch atom2 nat :=
  {| nodes := [{| world := 0; f := $P /\ Q -> P$; sign := false |}];
    edges := [] |}.

  Lemma closed_example : closed_tree Γ0.
  Proof.
    unfold Γ0.
    eapply ct_step.
    - apply (impl_F Γ0 0 $P /\ Q$ P).
      unfold mem_node.
      simpl.
      left.
      reflexivity.
    - intros Δ HΔ.
      simpl in HΔ.
      destruct HΔ as [HΔ | []].
      subst Δ.
      eapply ct_step.
      + apply (conj_T _ 0 P Q).
        unfold mem_node.
        simpl.
        auto.
      + intros Δ HΔ.
        simpl in HΔ.
        destruct HΔ as [HΔ | []].
        subst Δ.
        apply ct_closed.
        unfold closed.
        exists 0.
        exists P.
        split ; unfold mem_node ; simpl.
        * auto.
        * auto.
  Qed.
End Tableaus.

Module Goldblatt.
Import Kripke.

(* Стр. 12 Задача № 5 -> *)
Proposition Ex_R_5 {atom : Set} `(F : Frame) : (euclidian (@accessible F)) -> (forall φ : @formula atom, valid_in_frame F $diamond φ -> box diamond φ$).
  intro Heucl.
  unfold euclidian in Heucl.
  intros φ.
  hnf.
  intros V Γ Hdiamond.
  simpl in Hdiamond.
  destruct Hdiamond as [Δ [Γ_R_Δ Δ_φ]].
  hnf.
  intros Ω Γ_R_Ω.
  hnf.
  specialize (Heucl Γ Ω Δ).
  specialize (Heucl Γ_R_Ω Γ_R_Δ) as Ω_R_Δ.
  exists Δ.
  split.
  - exact Ω_R_Δ.
  - exact Δ_φ.
Qed.

(* Стр. 12 Задача № 5 <- *)
Theorem E5_4_5_valid_eucl {atom : Set} (Hinh : inhabited atom) (F : Frame) `{Heq_dec: EqDec F.(worlds)} :
  (forall φ : @formula atom, valid_in_frame F $diamond φ -> box diamond φ$) -> euclidian (@accessible F).
Proof.
  intro H.
  unfold valid_in_frame in H.
  unfold euclidian.
  intros w v u w_R_v w_R_u.
  set (V := fun (x : worlds) (_ : atom) =>
              if eqb x u then True else False
      ).

  destruct Hinh as [P].
  assert (Hu_P : valid {| frame := F; valuation := V |} u (f_atom P)).
  {
    simpl.
    unfold V.
    rewrite eqb_reflexive.
    exact I.
  }

  specialize (H (f_atom P) V w) as H1.
  unfold implication in H1.
  hnf in H1.
  assert (Hdiamond : valid {| frame := F; valuation := V |} w (f_diamond (f_atom P))).
  {
    hnf.
    exists u.
    split.
    - exact w_R_u.
    - exact Hu_P.
  }

  specialize (H1 Hdiamond).
  hnf in H1.
  specialize (H1 v w_R_v).
  simpl in H1.
  destruct H1 as [w1 [w_R_w1 Hw1_P]].
  unfold V in Hw1_P.
  destruct (eqb w1 u) eqn:Heq.
  - rewrite eqb_eq in Heq.
    rewrite Heq in w_R_w1.
    exact w_R_w1.
  - destruct Hw1_P.
Qed.

(* Стр. 12 Задача № 6 *)
Proposition Ex_R_6 {atom : Set} `(F : Frame) : (partially_functional (@accessible F)) -> (forall φ : @formula atom, valid_in_frame F $diamond φ -> box φ$).
Proof.
  intro H_par_fun.
  unfold partially_functional in H_par_fun.
  intros φ.
  hnf.
  intros V Γ Hdiamond.
  destruct Hdiamond as [Δ [Γ_R_Δ Δ_φ]].
  hnf.
  intros Ω Γ_R_Ω.
  specialize (H_par_fun Γ Ω Δ).
  specialize (H_par_fun Γ_R_Ω Γ_R_Δ) as Heq.
  rewrite Heq.
  exact Δ_φ.
Qed.

(* Стр. 12 Задача № 7 *)
Proposition Ex_R_7 {atom : Set} `(F : Frame) : (functional (@accessible F)) -> (forall φ : @formula atom, valid_in_frame F $diamond φ <-> box φ$).
Proof.
  intro Hfun.
  unfold functional in Hfun.
  intro φ.
  hnf.
  intros V Γ.
  hnf.
  split.
  - hnf.
    intro Hdiamond.
    simpl in Hdiamond.
    destruct Hdiamond as [Δ [Γ_R_Δ Δ_φ]].
    hnf.
    intros Ω Γ_R_Ω.
    specialize (Hfun Γ).
    destruct Hfun as [w [Γ_R_w Hfun]].
    specialize (Hfun Δ Γ_R_Δ) as Heq1.
    specialize (Hfun Ω Γ_R_Ω) as Heq2.
    rewrite <-Heq1 in Heq2.
    rewrite Heq2.
    exact Δ_φ.
  - hnf.
    intro Hbox.
    simpl in Hbox.
    simpl.
    specialize (Hfun Γ).
    destruct Hfun as [Δ [Γ_R_Δ Hfun]].
    exists Δ.
    split.
    + exact Γ_R_Δ.
    + specialize (Hbox Δ Γ_R_Δ) as Δ_φ.
      exact Δ_φ.
Qed.

(* Стр. 12 Задача № 8 *)
Proposition Ex_R_8 {atom : Set} `(F : Frame) : (weakly_dense (@accessible F)) -> (forall φ : @formula atom, valid_in_frame F $box box φ -> box φ$).
Proof.
  intro Hw_dense.
  unfold weakly_dense in Hw_dense.
  intro φ.
  hnf.
  intros V Γ.
  hnf.
  intro H2box.
  hnf.
  intros Δ Γ_R_Δ.
  specialize (Hw_dense Γ Δ Γ_R_Δ).
  destruct Hw_dense as [Ω [Γ_R_Ω Ω_R_Δ]].
  hnf in H2box.
  specialize (H2box Ω Γ_R_Ω).
  hnf in H2box.
  specialize (H2box Δ Ω_R_Δ) as HΔ_φ.
  exact HΔ_φ.
Qed.

(* Стр. 12 Задача № 9 *)
Proposition Ex_R_9 {atom : Set} `(F : Frame) : (weakly_connected (@accessible F)) -> (forall φ ψ : @formula atom, valid_in_frame F $box((φ /\ box φ) -> ψ) \/ box((ψ /\ box ψ) -> φ)$).
Proof.
  intro Hw_connected.
  unfold weakly_connected in Hw_connected.
  intros φ ψ.
  hnf.
  intros V Γ.
  hnf.
  apply NNPP.
  unfold not.
  intro H.
  apply not_or_and in H.
  destruct H as [H1 H2].
  unfold not in H1, H2.
  rewrite meta_Ex5_2_2 in H1, H2.
  cbn in H1, H2.
  apply NNPP in H1, H2.
  destruct H1 as [Δ [Γ_R_Δ HΔ]].
  destruct H2 as [Ω [Γ_R_Ω HΩ]].
  specialize (not_imply_elim _ _ HΔ) as H1.
  specialize (not_imply_elim2 _ _ HΔ) as Δ_n_ψ.
  specialize (not_imply_elim _ _ HΩ) as H3.
  specialize (not_imply_elim2 _ _ HΩ) as Ω_n_φ.
  clear HΔ HΩ.
  specialize (Hw_connected Γ Δ Ω).
  specialize (Hw_connected Γ_R_Δ Γ_R_Ω).
  destruct H1 as [Δ_φ Δ_box_φ].
  destruct H3 as [Ω_ψ Ω_box_ψ].
  destruct Hw_connected as [Δ_R_Ω | [Heq | Ω_R_Δ]].
  - specialize (Δ_box_φ Ω Δ_R_Ω) as Ω_φ.
    apply Ω_n_φ in Ω_φ.
    exact Ω_φ.
  - rewrite Heq in Δ_φ.
    apply Ω_n_φ in Δ_φ.
    exact Δ_φ.
  - specialize (Ω_box_ψ Δ Ω_R_Δ) as Δ_ψ.
    apply Δ_n_ψ in Δ_ψ.
    exact Δ_ψ.
Qed.

(* Стр. 12 Задача № 10 *)
Proposition Ex_R_10 {atom : Set} `(F : Frame) : (weakly_directed (@accessible F)) -> (forall φ : @formula atom, valid_in_frame F $diamond box φ -> box diamond φ$).
Proof.
  intro Hw_directed.
  unfold weakly_directed in Hw_directed.
  intro φ.
  hnf.
  intros V Γ.
  hnf.
  intro Hd_box.
  hnf in Hd_box.
  destruct Hd_box as [Δ [Γ_R_Δ Hbox]].
  hnf in Hbox.
  hnf.
  intros Ω Γ_R_Ω.
  hnf.
  specialize (Hw_directed Γ Ω Δ).
  specialize (Hw_directed Γ_R_Ω Γ_R_Δ).
  destruct Hw_directed as [Ε [Ω_R_Ε Δ_R_Ε]].
  exists Ε.
  split.
  - exact Ω_R_Ε.
  - specialize (Hbox Ε Δ_R_Ε) as HΕ_φ.
    exact HΕ_φ.
Qed.
End Goldblatt.
