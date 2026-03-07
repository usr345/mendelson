From Basis Require Import FSignature.
From Relevant_B Require Import Formula.
Import FormulaDef.
Import Relevant_B_Formula.
Local Open Scope formula_scope.

Module Syntactic.
  Definition f_identity {atom : Type} (A : @formula atom) : formula :=
    $A -> A$.

  Definition f_disj_intro_left {atom : Type} (A B: @formula atom) : formula :=
    $A -> A \/ B$.

  Definition f_disj_intro_right {atom : Type} (A B: @formula atom) : formula :=
    $B -> A \/ B$.

  Definition f_conj_elim_left {atom : Type} (A B: @formula atom) : formula :=
    $A /\ B -> A$.

  Definition f_conj_elim_right {atom : Type} (A B: @formula atom) : formula :=
    $A /\ B -> B$.

  Definition f_conj_distrib {atom : Type} (A B C: @formula atom) : formula :=
    $A /\ (B \/ C) -> (A /\ B) \/ (A /\ C)$.

  Definition f_case_analysis {atom : Type} (A B C: @formula atom) : formula :=
    $(A -> C) /\ (B -> C) -> (A \/ B) -> C$.

  Definition f_neg_elim {atom : Type} (A: @formula atom) : formula :=
    $~~A -> A$.

  #[global] Reserved Notation "A |- B" (at level 98).
  Inductive entails {atom : Type} (Γ : @formula atom -> Prop) : @formula atom -> Type :=
    | hypo : forall A, Γ A -> Γ |- A (* every hypothesis is provable *)
    | identity : forall A , Γ |- f_identity A
    | disj_intro_left : forall A B, Γ |- f_disj_intro_left A B
    | disj_intro_right : forall A B, Γ |- f_disj_intro_right A B
    | conj_elim_left : forall A B, Γ |- f_conj_elim_left A B
    | conj_elim_right : forall A B, Γ |- f_conj_elim_right A B
    | conj_distrib : forall A B C, Γ |- f_conj_distrib A B C
    | case_analysis : forall A B C, Γ |- f_case_analysis A B C
    | neg_elim : forall A, Γ |- f_neg_elim A
    | mp : forall A B, Γ |- $A -> B$ -> Γ |- A -> Γ |- B (* modus ponens *)
    | conj_intro : forall A B, Γ |- A -> Γ |- B -> Γ |- $A /\ B$
    | trans_prefix : forall A B C, Γ |- $A -> B$ -> Γ |- $(C -> A) -> (C -> B)$
    | trans_suffix : forall A B C, Γ |- $A -> B$ -> Γ |- $(B -> C) -> (A -> C)$
    | contrapos : forall A B, Γ |- $A -> ~B$ -> Γ |- $B -> ~A$
  where "Γ |- A" := (entails Γ A).

Arguments hypo {atom} {Γ} A.
Arguments identity {atom} {Γ} A.
Arguments disj_intro_left {atom} {Γ} A B.
Arguments disj_intro_right {atom} {Γ} A B.
Arguments conj_elim_left {atom} {Γ} A B.
Arguments conj_elim_right {atom} {Γ} A B.
Arguments conj_distrib {atom} {Γ} A B C.
Arguments case_analysis {atom} {Γ} A B C.
Arguments neg_elim {atom} {Γ} A.
Arguments mp {atom} {Γ} {A} {B} _ _.
Arguments conj_intro {atom} {Γ} {A} {B} _ _.
Arguments trans_prefix {atom} {Γ} {A} {B} C _.
Arguments trans_suffix {atom} {Γ} {A} {B} C _.
Arguments contrapos {atom} {Γ} {A} {B} _.

Ltac specialize_axiom A H :=
  pose proof A as H;
  try match type of H with
  | (_ |- f_identity _) => unfold f_identity in H
  | (_ |- f_disj_intro_left _ _) => unfold f_disj_intro_left in H
  | (_ |- f_disj_intro_right _ _) => unfold f_disj_intro_right in H
  | (_ |- f_conj_elim_left _ _) => unfold f_conj_elim_left in H
  | (_ |- f_conj_elim_right _ _) => unfold f_conj_elim_right in H
  | (_ |- f_conj_distrib _ _ _) => unfold f_conj_distrib in H
  | (_ |- f_case_analysis _ _ _) => unfold f_case_analysis in H
  | (_ |- f_neg_elim _) => unfold f_neg_elim in H
  end.

Lemma A_nnA {atom : Type} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A -> ~~A$.
Proof.
  specialize_axiom (identity (Γ:=Γ) $~A$) H1.
  specialize_axiom (contrapos (Γ:=Γ) H1) H2.
  exact H2.
Qed.


End Syntactic.
