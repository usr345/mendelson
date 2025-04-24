From Mendelson Require Import Sets.
From Mendelson Require Import FSignature.

Module L1_Hilbert_Accerman <: TFormula.
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_disj  : formula -> formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition disjunction {atom : Type} := @f_disj atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition implication {atom : Type} (A B: @formula atom) : formula := disjunction (negation A) B.
  Definition conjunction {atom : Type} (A B: @formula atom) : formula := negation (implication A (negation B)).
  Definition equivalence {atom : Type} (A B: @formula atom) : formula := conjunction (implication A B) (implication B A).
End L1_Hilbert_Accerman.

Module Formula.

  Module F1 := Make_Formula(L1_Hilbert_Accerman).
  Import L1_Hilbert_Accerman.
  Import F1.

  (* We assume atomic propositions form a set with decidable equality. *)
  Parameter atom_eq : forall {atom : Set} (a b : atom), {a = b} + {a <> b}.

  Definition f_axiom1 {atom : Set} (A B : @formula atom) : formula :=
    $(A \/ A) -> A$.

  Definition f_axiom2 {atom : Set} (A B : @formula atom) : formula :=
    $A -> A \/ B$.

  Definition f_axiom3 {atom : Set} (A B : @formula atom) : formula :=
    $A \/ B -> B \/ A$.

  Definition f_axiom4 {atom : Set} (A B C: @formula atom) : formula :=
    $(B -> C) -> (A \/ B -> A \/ C)$.

  Reserved Notation "Γ |- A" (at level 32).
  Inductive entails {atom : Set} (Γ : @formula atom -> Prop) : @formula atom -> Type :=
  | hypo : forall A, A ∈ Γ -> Γ |- A (* every hypothesis is provable *)
  | axiom1 : forall A B , Γ |- f_axiom1 A B
  | axiom2 : forall A B, Γ |- f_axiom2 A B
  | axiom3 : forall A B, Γ |- f_axiom3 A B
  | axiom4 : forall A B C, Γ |- f_axiom4 A B C
  | mp {A B : formula} : Γ |- $B -> A$ -> Γ |- B -> Γ |- A (* modus ponens *)
  where "Γ |- A" := (entails Γ A).

  (* It is convenient to make some parameters implicit. *)
  Arguments hypo {_} {_} _.
  Arguments axiom1 {_} {_} _ _.
  Arguments axiom2 {_} {_} _ _.
  Arguments axiom3 {_} {_} _ _.
  Arguments axiom4 {_} {_} _ _ _.
  Arguments mp {_} {_} {_} {_} (_) (_).

  (* Equality of formulas is decidable. *)
  Lemma formula_eq {atom : Set} (A B : @formula atom) : {A = B} + {A <> B}.
  Proof.
    decide equality.
    now apply atom_eq.
  Qed.

  Ltac hypo := (apply hypo ; cbv in * ; auto 6).

  Ltac specialize_axiom A H :=
    pose proof A as H;
    try match type of H with
      | (_ |- f_axiom1 _ _) => unfold f_axiom1 in H
      | (_ |- f_axiom2 _ _) => unfold f_axiom2 in H
      | (_ |- f_axiom3 _ _) => unfold f_axiom3 in H
      | (_ |- f_axiom4 _ _ _) => unfold f_axiom4 in H
      end.

  Theorem weaken {atom : Set} (Γ : @formula atom -> Prop) Δ A : Γ ⊆ Δ -> Γ |- A -> Δ |- A.
  Proof.
    intros S H.
    induction H as [A H|A B|A B|A B|A B C|A B H1 H2 IH1 IH2].
    (* Пусть A ∈ Γ *)
    - unfold subset in S.
      specialize (S A H).
      apply hypo.
      exact S.
    - apply (axiom1 A B).
    - apply (axiom2 A B).
    - apply (axiom3 A B).
    - apply (axiom4 A B C).
    - pose proof (mp H2 IH2) as H3.
      exact H3.
  Qed.

  Lemma imply_self {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A -> A$.
  Proof.
    unfold implication.
    (* (1) $(A \supset ((A \supset A) \supset A)) \supset ((A \supset (A \supset A)) \supset (A \supset A))$ --- подстановка в схему аксиом A4 *)
    specialize_axiom (@axiom4 _ Γ $~A$ $A \/ A$ A) H1.
    (* (2) $A \or A \supset A$ --- схема аксиом A1 *)
    specialize_axiom (@axiom1 _ Γ A A) H2.
    (* (3) $((A \supset (A \supset A)) \supset (A \supset A))$ --- из (1) и (2) по MP *)
    specialize (mp H1 H2) as H3.
    (* (4) $A \supset (A \supset A)$ --- схема аксиом A1 *)
    specialize_axiom (@axiom2 _ Γ A A) H4.
    unfold implication in H4.
    (* (5) $A \supset A$ --- из (3) и (4) по MP *)
    specialize (mp H3 H4) as H5.
    exact H5.
  Qed.

  (* We need this lemma in the deduction theorem. *)
  Lemma drop_antecedent {atom : Set} (Γ : @formula atom -> Prop) A B : Γ |- B -> Γ |- $A -> B$.
  Proof.
    intro H1.
    unfold implication.
    (* 1. $B \supset (A \supset B)$ --- схема аксиом A1 *)
    specialize_axiom (@axiom2 _ Γ B $~A$) H2.
    (* 2. $A \supset B$ --- из H и H1 по MP *)
    specialize (mp H2 H1) as H3.
    specialize_axiom (@axiom3 _ Γ B $~A$) H4.
    specialize (mp H4 H3) as H5.
    exact H5.
  Qed.

  (* We conclude with the proof of the deduction theorem, just to show
   that it is quite painless to formalize. *)
  (* Theorem deduction {atom : Set} {Γ : @formula atom -> Prop} {A B} : Γ,, A |- B -> Γ |- $A -> B$. *)
  (* Proof. *)
  (*   intro H. *)
  (*   induction H as [B H|?|?|?|?|B C H1 IH1 H2 IH2]. *)
  (*   (* Пусть B является элементом Γ,, A *) *)
  (*   - unfold elem in H. *)
  (*     unfold extend in H. *)
  (*     destruct (formula_eq A B) as [Heq|Hneq]. *)
  (*     (* Если B = A, применяем лемму imply_self *) *)
  (*     + rewrite Heq. *)
  (*       apply imply_self. *)
  (*     (* Если B != A, по аксиоме 1 получаем формулу *) *)
  (*     (* $B \supset (A \supset B)$ *) *)
  (*     + (* Поскольку B != A, B содержится в Γ *) *)
  (*       assert (H1: Γ |- B). *)
  (*       { *)
  (*         apply hypo. *)
  (*         unfold elem in H. *)
  (*         destruct H as [Hin|Heq]. *)
  (*         - unfold elem. *)
  (*           exact Hin. *)
  (*         - apply Hneq in Heq. *)
  (*           contradiction Heq. *)
  (*       } *)

  (*       specialize (drop_antecedent Γ A B H1) as H2. *)
  (*       exact H2. *)
  (*   - (* Пусть B является аксиомой *) *)
  (*     apply drop_antecedent. *)
  (*     apply axiom1. *)
  (*   - apply drop_antecedent. *)
  (*     apply axiom2. *)
  (*   - apply drop_antecedent. *)
  (*     apply axiom3. *)
  (*   - apply drop_antecedent. *)
  (*     apply axiom4. *)
  (*   - *)
  (*     (* Modus Ponens: *)
   (*        Пусть B получена по MP из 2-х формул C и $C -> B$ по Modus Ponens, и пусть они доказуемы в контексте (Γ,, A): *)
   (*        H1 : Γ,, A |- C *)
   (*        H2 : Γ,, A |- $C -> B$ *)

   (*        Пусть истинны индуктивные гипотезы: *)
   (*        IH1 : Γ |- $A -> С$ *)
   (*        IH2 : Γ |- $A -> С -> B$ *)
   (*     *) *)

  (*     (* По аксиоме 2: $(A -> (C -> B)) -> ((A -> C) -> (A -> B))$ *) *)
  (*     specialize_axiom (@axiom2 _ Γ A C B) H3. *)

  (*     (* По MP из IH2 : Γ |- $A -> C -> B$ *) *)
  (*     (* и H3 : Γ |- $(A -> C -> B) -> (A -> C) -> A -> B$ *) *)
  (*     specialize (mp $A -> C -> B$ IH2 H3) as H4. *)

  (*     (* MP *) *)
  (*     (* IH1 : Γ |- $A -> C$ *) *)
  (*     (*  H4 : Γ |- $(A -> C) -> A -> B$ *) *)
  (*     specialize (mp $A -> C$ IH1 H4) as H5. *)
  (*     exact H5. *)
  (* Qed. *)

  Lemma T1 {atom : Set} (Γ : @formula atom -> Prop) (A B C : @formula atom) : Γ,, $A -> B$ |- $C \/ A -> C \/ B$.
  Proof.
    specialize_axiom (@axiom4 _ (Γ,, $A -> B$) C A B) H1.
    assert (H2: Γ,, $A -> B$ |- $A -> B$).
    {
      hypo.
    }

    specialize (mp H1 H2) as H3.
    exact H3.
  Qed.

  Lemma T2 {atom : Set} (Γ : @formula atom -> Prop) (A B C : @formula atom) : Γ |- $(A -> B) -> ((C -> A) -> (C -> B))$.
  Proof.
    specialize_axiom (@axiom4 _ Γ $~C$ A B) H1.
    exact H1.
  Qed.

  Lemma T3 {atom : Set} (Γ : @formula atom -> Prop) (A B C : @formula atom) : Γ,, $C -> A$,, $A -> B$ |- $C -> B$.
  Proof.

    assert (H1: Γ,, $C -> A$,, $A -> B$ |- $C -> A$).
    {
      hypo.
    }

    assert (H2: Γ,, $C -> A$,, $A -> B$ |- $A -> B$).
    {
      hypo.
    }

    specialize (T2 (Γ,, $C -> A$,, $A -> B$) A B C) as H3.
    specialize (mp H3 H2) as H4.
    specialize (mp H4 H1) as H5.
    exact H5.
  Qed.

  Lemma T5 {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A \/ ~A$.
  Proof.
    specialize (imply_self Γ A) as H1.
    unfold implication in *.
    specialize_axiom (@axiom3 _ Γ $~A$ A) H2.
    specialize (mp H2 H1) as H3.
    exact H3.
  Qed.

  Lemma T6 {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) : Γ |- $A -> ~~A$.
  Proof.
    unfold implication.
    specialize (T5 Γ $~A$) as H1.
    exact H1.
  Qed.

  Lemma T7 {atom : Set} (Γ : @formula atom -> Prop) (B C : @formula atom) : Γ |- $~B -> (B -> C)$.
  Proof.
  Admitted.

  Lemma T2 {atom : Set} (Γ : @formula atom -> Prop) (A B C : @formula atom) : Γ,, $A -> (B -> C)$,, $A -> B$ |- $A -> C$.
  Proof.

    assert (H1: Γ,, $A -> B$ |- $A -> B$).
    {
      hypo.
    }


    (* Lemma T2 {atom : Set} (Γ : @formula atom -> Prop) (A B C : @formula atom) : Γ |- $(A -> B) -> ((C -> A) -> (C -> B))$. *)
    (* Proof. *)
    Check formula.
End L1_Hilbert_Accerman.
