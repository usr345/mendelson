From Relevant_B Require Import Formula.
Import FormulaDef.
Import Relevant_B_Formula.
Local Open Scope formula_scope.

Module Functions.
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

  Definition f_impl_conj_right {atom : Type} (A B C: @formula atom) : formula :=
    $(A -> B) /\ (A -> C) -> (A -> (B /\ C))$.

  Definition f_neg_elim {atom : Type} (A: @formula atom) : formula :=
    $~~A -> A$.

  Definition f_contrapos {atom : Type} (A B: @formula atom) : formula :=
    $(A -> ~B) -> (B -> ~A)$.

  Definition f_trans_suffix {atom : Type} (A B C: @formula atom) : formula :=
    $(A -> B) -> (B -> C) -> (A -> C)$.

  Definition f_trans_prefix {atom : Type} (A B C: @formula atom) : formula :=
    $(A -> B) -> (C -> A) -> (C -> B)$.

  Definition f_mp_surreal {atom : Type} (A B: @formula atom) : formula :=
    $(A -> (A -> B)) -> (A -> B)$.

  Definition f_mp {atom : Type} (A B: @formula atom) : formula :=
    $A -> ((A -> B) -> B)$.

End Functions.

Module Syntactic.
  Import Functions.

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
    | impl_conj_right : forall A B C, Γ |- f_impl_conj_right A B C
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
Arguments impl_conj_right {atom} {Γ} A B C.
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
  | (_ |- f_impl_conj_right _ _ _) => unfold f_impl_conj_right in H
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

Module Syntactic_R.
  Import Functions.

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
    | impl_conj_right : forall A B C, Γ |- f_impl_conj_right A B C
    | neg_elim : forall A, Γ |- f_neg_elim A
    | contrapos : forall A B, Γ |- f_contrapos A B
    | trans_suffix : forall A B C, Γ |- f_trans_suffix A B C
    | trans_prefix : forall A B C, Γ |- f_trans_prefix A B C
    | mp_surreal : forall A B, Γ |- f_mp_surreal A B
    | A_mp : forall A B, Γ |- f_mp A B
    | mp : forall A B, Γ |- $A -> B$ -> Γ |- A -> Γ |- B (* modus ponens *)
    | conj_intro : forall A B, Γ |- A -> Γ |- B -> Γ |- $A /\ B$
    | permutation : forall A B C, Γ |- $A -> (B -> C)$ -> Γ |- $B -> (A -> C)$
  where "Γ |- A" := (entails Γ A).

Arguments hypo {atom} {Γ} A.
Arguments identity {atom} {Γ} A.
Arguments disj_intro_left {atom} {Γ} A B.
Arguments disj_intro_right {atom} {Γ} A B.
Arguments conj_elim_left {atom} {Γ} A B.
Arguments conj_elim_right {atom} {Γ} A B.
Arguments conj_distrib {atom} {Γ} A B C.
Arguments impl_conj_right {atom} {Γ} A B C.
Arguments case_analysis {atom} {Γ} A B C.
Arguments neg_elim {atom} {Γ} A.
Arguments contrapos {atom} {Γ} A B.
Arguments trans_suffix {atom} {Γ} A B C.
Arguments trans_prefix {atom} {Γ} A B C.
Arguments mp_surreal {atom} {Γ} A B.
Arguments A_mp {atom} {Γ} A B.
Arguments mp {atom} {Γ} {A} {B} _ _.
Arguments conj_intro {atom} {Γ} {A} {B} _ _.
Arguments permutation {atom} {Γ} {A} {B} {C} _.

Ltac specialize_axiom A H :=
  pose proof A as H;
  try match type of H with
  | (_ |- f_identity _) => unfold f_identity in H
  | (_ |- f_disj_intro_left _ _) => unfold f_disj_intro_left in H
  | (_ |- f_disj_intro_right _ _) => unfold f_disj_intro_right in H
  | (_ |- f_conj_elim_left _ _) => unfold f_conj_elim_left in H
  | (_ |- f_conj_elim_right _ _) => unfold f_conj_elim_right in H
  | (_ |- f_conj_distrib _ _ _) => unfold f_conj_distrib in H
  | (_ |- f_impl_conj_right _ _ _) => unfold f_impl_conj_right in H
  | (_ |- f_case_analysis _ _ _) => unfold f_case_analysis in H
  | (_ |- f_neg_elim _) => unfold f_neg_elim in H
  | (_ |- f_contrapos _ _) => unfold f_contrapos in H
  | (_ |- f_trans_suffix _ _ _) => unfold f_trans_suffix in H
  | (_ |- f_trans_prefix _ _ _) => unfold f_trans_prefix in H
  | (_ |- f_mp_surreal _ _) => unfold f_mp_surreal in H
  | (_ |- f_mp _ _) => unfold f_mp in H
  end.

Theorem trans_prefix_rule {atom : Type} {Γ : @formula atom -> Prop} {A B C : @formula atom} : 
  Γ |- $A -> B$ -> Γ |- $C -> A$ -> Γ |- $C -> B$.
Proof.
  intros H1 H2.
  specialize_axiom (trans_prefix (Γ:=Γ) A B C) H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Theorem trans_suffix_rule {atom : Type} {Γ : @formula atom -> Prop} {A B C : @formula atom} : 
  Γ |- $A -> B$ -> Γ |- $B -> C$ -> Γ |- $A -> C$.
Proof.
  intros H1 H2.
  specialize_axiom (trans_suffix (Γ:=Γ) A B C) H3.
  specialize (mp H3 H1) as H4.
  specialize (mp H4 H2) as H5.
  exact H5.
Qed.

Theorem contrapos_rule {atom : Type} {Γ : @formula atom -> Prop} {A B : @formula atom} : 
  Γ |- $A -> ~B$ -> Γ |- $B -> ~A$.
Proof.
  intro H1.
  specialize_axiom (contrapos (Γ:=Γ) A B) H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Theorem neg_elim_rule {atom : Type} {Γ : @formula atom -> Prop} {A : @formula atom} : 
  Γ |- $~~A$ -> Γ |- A.
Proof.
  intro H1.
  specialize_axiom (neg_elim (Γ:=Γ) A) H2.
  specialize (mp H2 H1) as H3.
  exact H3.
Qed.

Theorem A_nnA {atom : Type} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A -> ~~A$.
Proof.
  specialize_axiom (identity (Γ:=Γ) $~A$) H1.
  specialize (contrapos_rule H1) as H2.
  exact H2.
Qed.

End Syntactic_R.