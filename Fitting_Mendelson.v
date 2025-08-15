Require Import Setoid.
From Mendelson Require Import Sets.
From Mendelson Require Import FSignature.
From Mendelson Require Import EqDec.
Require Import Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Module Formula1 <: TFormula.
  (* Синтаксис модальной формулы *)
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula
  | f_imp  : formula -> formula -> formula
  | f_box  : formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} := @f_imp atom.
  Definition disjunction {atom : Type} := @f_imp atom.
  Definition implication {atom : Type} := @f_imp atom.
  Definition equivalence {atom : Type} (A B: @formula atom) : formula := conjunction (implication A B) (implication B A).
  Definition f_diamond {atom : Type} (A: @formula atom) : formula := f_not (f_box (f_not A)).

  #[global] Notation "'box' p" := (f_box p) (in custom formula_view at level 1) : formula_scope.
End Formula1.
Export Formula1.

Module Formula.

  Module F1:= Make_Formula(Formula1).
  Import F1.
  Export F1.

  Definition f_diamond {atom : Type} (A: @formula atom) : formula := $~ (box ~A)$.
  #[global] Notation "'diamond' p" := (f_diamond p) (p custom formula_view at level 1, in custom formula_view at level 1).
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
  Qed.

  #[export] Instance eqFormula {atom : Set} `{EqDec atom} : EqDec (@formula atom)  :=
    {
      eqb := formula_beq;
      eqb_eq := formula_beq_eq;
    }.

End Formula.
Export Formula.

Module Syntactic.

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

Definition f_axiom8 {atom : Set} (A B C : @formula atom) : formula :=
  $(A -> C) -> (B -> C) -> (A \/ B -> C)$.

Definition f_ex_falso {atom : Set} (A B : @formula atom) : formula :=
  $~A -> (A -> B)$.

Definition f_tertium_non_datur {atom : Set} (A : @formula atom) : formula :=
  $A \/ ~A$.

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
  | axiom8 : forall A B C, Γ |- f_axiom8 A B C
  | ex_falso : forall A B, Γ |- f_ex_falso A B
  | tertium_non_datur : forall A, Γ |- f_tertium_non_datur A
  | axiomK : forall A B, Γ |- f_axiomK A B
  | mp : forall A B, Γ |- $A -> B$ -> Γ |- A -> Γ |- B (* modus ponens *)
  | nec : forall A, Γ |- A -> Γ |- $box A$            (* necessitation *)
where "Γ |- A" := (entails Γ A).

(* It is convenient to make some parameters implicit. *)
Arguments hypo {_} {_} _.
Arguments axiom1 {_} {_} _ _.
Arguments axiom2 {_} {_} _ _ _.
Arguments conj_elim1 {_} (_) _ _.
Arguments conj_elim2 {_} (_) _ _.
Arguments conj_intro {_} (_) _ _.
Arguments disj_intro1 {_} (_) _ _.
Arguments disj_intro2 {_} (_) _ _.
Arguments axiom8 {_} (_) _ _ _.
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
  | (_ |- f_axiom8 _ _ _) => unfold f_axiom8 in H
  | (_ |- f_ex_falso _ _) => unfold f_ex_falso in H
  | (_ |- f_tertium_non_datur _) => unfold f_tertium_non_datur in H
  | (_ |- f_axiomK _ _) => unfold f_axiomK in H
  end.

Lemma meta_conj_elim1 {atom : Set} {Γ : @formula atom -> Prop} {A B : @formula atom} : Γ |- $(A /\ B)$ -> Γ |- A.
Proof.
  intro H1.
  pose proof (conj_elim1 Γ A B) as H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Lemma meta_conj_elim2 {atom : Set} {Γ : @formula atom -> Prop} {A B : @formula atom} : Γ |- $(A /\ B)$ -> Γ |- B.
Proof.
  intro H1.
  pose proof (conj_elim2 Γ A B) as H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Lemma meta_conj_intro {atom : Set} {Γ : @formula atom -> Prop} {A B : @formula atom} : Γ |- A -> Γ |- B -> Γ |- $A /\ B$.
Proof.
  intros H1 H2.
  pose proof (conj_intro Γ A B) as H3.
  unfold f_conj_intro in H3.
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
Lemma drop_antecedent {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- B -> Γ |- $A -> B$.
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
  specialize (drop_antecedent Γ $A -> X$ $(A -> Y) -> (A -> Y)$ H2) as H3.
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

Lemma disj_impl {atom : Set} (Γ : @formula atom -> Prop) (X Y: @formula atom) :
  Γ |- $(X \/ Y) -> (Y \/ X)$.
Proof.
  specialize_axiom (disj_intro2 Γ Y X) H1.
  specialize_axiom (disj_intro1 Γ Y X) H2.
  specialize_axiom (axiom8 Γ X Y $Y \/ X$) H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Lemma disj_comm {atom : Set} (Γ : @formula atom -> Prop) (X Y: @formula atom) :
  Γ |- $(X \/ Y) <-> (Y \/ X)$.
Proof.
  unfold equivalence.
  specialize (disj_impl Γ X Y) as H1.
  specialize (disj_impl Γ Y X) as H2.
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
    apply hypo.
    unfold extend.
    unfold elem.
    right.
    reflexivity.
  }

  specialize (contraposition (Γ,, $X -> Y$) X Y) as H2.
  specialize (mp H2 H1) as H3.
  specialize (nec H3) as H4.
  pose proof (@axiomK _ (Γ,, $X -> Y$) $~Y$ $~X$) as H5.
  unfold f_axiomK in H5.
  specialize (mp H5 H4) as H6.
  specialize (contraposition (Γ,, $X -> Y$) $box ~ Y$ $box ~ X$) as H7.
  specialize (mp H7 H6) as H8.
  unfold f_diamond.
  exact H8.
Qed.

Instance eqNat: EqDec nat :=
{
  eqb := Nat.eqb;
  eqb_eq := Nat.eqb_eq;
}.

(*
n > 0
Возвращает
*)
Fixpoint replace_subformula_int {atom : Set} `{EqDec atom} `{EqDec (@formula atom)} (X X' Y : @formula atom) (n : nat) {struct Y} : (@formula atom * nat) :=
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
    end.

Definition replace_subformula {atom : Set} `{EqDec atom} `{EqDec (@formula atom)} (X X' Y : @formula atom) (n : nat) : @formula atom := fst (replace_subformula_int X X' Y n).

(* X - подформула Y *)
Fixpoint subformula {atom : Set} `{EqDec atom} `{EqDec (@formula atom)} (X Y : @formula atom) : bool :=
  if eqb X Y then
    true
  else
    match Y with
    | f_not Y' => subformula X Y'
    | f_conj F1 F2 => orb (subformula X F1) (subformula X F2)
    | f_disj F1 F2 => orb (subformula X F1) (subformula X F2)
    | f_imp F1 F2 => orb (subformula X F1) (subformula X F2)
    | f_box Y' => subformula X Y'
    | _ => false
    end.

Theorem Replacement {atom : Set} `{EqDec atom} `{EqDec (@formula atom)} (Γ : @formula atom -> Prop) (X X' Y Y' : @formula atom) : forall n : nat, n > 0 -> (subformula X Y = true) -> Γ |- $X <-> X'$ -> Y' = (replace_subformula X X' Y n) -> Γ |- $Y <-> Y'$.
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
  unfold f_diamond.
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
  unfold f_diamond.
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
  unfold f_diamond.
  exact H5.
Qed.

(* Exercize 6.1.3.3 *)
Proposition E6_1_3_3 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $(box X \/ box Y) -> box(X \/ Y)$.
Proof.
Admitted.

(* Exercize 6.1.3.4 *)
Proposition E6_1_3_4 {atom : Set} (Γ : @formula atom -> Prop) (X Y : @formula atom) : Γ |- $box (X \/ Y) -> (box X \/ diamond Y)$.
Proof.
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

(* Worlds - тип для миров *)
Record Model {atom : Set} (Worlds : Type) :=
{
  G : Worlds;
  R : Worlds -> Worlds -> Prop;
  values : Worlds -> atom -> Prop;
}.


(* Worlds - тип для миров *)
(* Class Model {atom : Set} (Worlds : Type) := *)
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
