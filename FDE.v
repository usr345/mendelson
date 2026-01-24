From Mendelson Require Import FSignature.
From Mendelson Require Import Sets.
Require Import Lists.List.
Import ListNotations.

Module Formula1 <: TFormula.
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} := @f_conj atom.
  Definition disjunction {atom : Type} := @f_disj atom.
  Definition implication {atom : Type} (A B: @formula atom) :=
    disjunction (negation A) B.
  Definition equivalence {atom : Type} (A B: @formula atom) : formula := conjunction (implication A B) (implication B A).
End Formula1.

Module FDE.
  Import Formula1.
  Module F1:= Make_Formula(Formula1).

  Record Model (atom : Type) :=
  {
    ρ : atom -> bool -> Prop;
  }.

  Fixpoint FormulaTruth {atom : Type} (M: Model atom) (f : formula) (b : bool) : Prop :=
    match f with
    | f_atom A => ρ atom M A b
    | f_not f' => FormulaTruth M f' (negb b)
    | f_conj f g =>
        match b with
        | true => FormulaTruth M f true /\ FormulaTruth M g true
        | false => FormulaTruth M f false \/ FormulaTruth M g false
        end
    | f_disj f g =>
        match b with
        | true => FormulaTruth M f true \/ FormulaTruth M g true
        | false => FormulaTruth M f false /\ FormulaTruth M g false
        end
  end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : Model atom), FormulaTruth M f true.

  Declare Scope FDE_scope.
  Delimit Scope FDE_scope with FDE.
  Notation "|= f" := (valid f) (at level 90) : FDE_scope.

  Definition holds_all {atom : Type} (M : Model atom) (Γ : list formula) : Prop :=
   forall f : @formula atom, In f Γ -> FormulaTruth M f true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : Model atom),
      holds_all M Γ -> FormulaTruth M f true.

  Notation "Γ |= f" := (consequence Γ f) (at level 90) : FDE_scope.
End FDE.

Module FDE_excersizes.
  Import Formula1.
  Import FDE.
  Import FDE.F1.
  Open Scope FDE_scope.

  Theorem T_836 {atom : Type} : forall A B C D : @formula atom, [$~(B /\ ~C) /\ A$] |= $(~B \/ C) \/ D$.
  Proof.
    intros A B C D.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    hnf.
    left.

    assert (H1 : In $~ (B /\ ~ C) /\ A$
               [$~ (B /\ ~ C) /\ A$]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H $~ (B /\ ~ C) /\ A$).
    specialize (H H1).
    clear H1.
    hnf in H.
    destruct H as [H _].
    hnf in H.
    hnf.
    destruct H as [H | H].
    - left.
      hnf.
      cbn [negb].
      exact H.
    - right.
      hnf in H.
      cbn [negb] in H.
      exact H.
  Qed.

  Theorem T_3 {atom : Type} : forall A B C : @formula atom, [$A /\ (B \/ C)$] |= $(A /\ B) \/ (A /\ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    assert (H1 : In $A /\ (B \/ C)$
               [$A /\ (B \/ C)$]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H $A /\ (B \/ C)$).
    specialize (H H1).
    clear H1.
    hnf in H.
    destruct H as [H1 H2].
    hnf in H2.
    hnf.
    destruct H2 as [H2 | H2].
    - left.
      hnf.
      exact (conj H1 H2).
    - right.
      hnf.
      exact (conj H1 H2).
  Qed.

  Theorem T_4 {atom : Type} : forall A B C : @formula atom, [$A \/ (B /\ C)$] |= $(A \/ B) /\ (A \/ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    assert (H1 : In $A \/ B /\ C$
               [$A \/ B /\ C$]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H $A \/ B /\ C$).
    specialize (H H1).
    clear H1.
    hnf in H.
    hnf.
    split.
    - destruct H as [H | H].
      + hnf.
        left.
        exact H.
      + hnf in H.
        destruct H as [H1 H2].
        hnf.
        right.
        exact H1.
    - destruct H as [H | H].
      + hnf.
        left.
        exact H.
      + hnf in H.
        destruct H as [H1 H2].
        hnf.
        right.
        exact H2.
  Qed.

  Theorem T_5 {atom : Type} : forall A : @formula atom, [A] |= $~ ~A$.
  Proof.
    intro A.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    assert (H1 : In A
               [A]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H A).
    specialize (H H1).
    clear H1.

    hnf.
    rewrite Bool.negb_involutive.
    exact H.
  Qed.

  Theorem T_7 {atom : Type} : forall A B C : @formula atom, [$(A /\ B) -> C$] |= $(A /\ ~C) -> ~B$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    assert (H1 : In $A /\ B -> C$
               [$A /\ B -> C$]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H $A /\ B -> C$).
    specialize (H H1).
    clear H1.

    unfold implication in H.
    unfold implication.

    hnf in H.
    hnf.
    destruct H as [H | H].
    - hnf in H.
      destruct H as [H | H].
      + left.
        hnf.
        left.
        exact H.
      + right.
        hnf.
        cbn [negb].
        exact H.
    - left.
      hnf.
      right.
      hnf.
      cbn [negb].
      exact H.
  Qed.

  Theorem T_12 {atom : Type} : forall A B C : @formula atom, [$(A /\ B) -> C$] |= $A -> (~B \/ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    assert (H1 : In $A /\ B -> C$
               [$A /\ B -> C$]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H $A /\ B -> C$).
    specialize (H H1).
    clear H1.

    unfold implication in H.
    unfold implication.

    hnf in H.
    hnf.
    destruct H as [H | H].
    - hnf in H.
      destruct H as [H | H].
      + left.
        hnf.
        cbn [negb].
        exact H.
      + right.
        hnf.
        left.
        hnf.
        cbn [negb].
        exact H.
    - right.
      hnf.
      right.
      exact H.
  Qed.

  Theorem FDE_5 {atom : Type} : forall A B C : @formula atom, [$A /\ (B \/ C)$] |= $(A /\ B) \/ C$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    assert (H1 : In $A /\ (B \/ C)$
               [$A /\ (B \/ C)$]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H $A /\ (B \/ C)$).
    specialize (H H1).
    clear H1.

    hnf.
    hnf in H.
    destruct H as [H1 H2].
    destruct H2 as [H2 | H2].
    - left.
      hnf.
      exact (conj H1 H2).
    - right.
      exact H2.
  Qed.


  Variant atom3 : Set := P | Q | R.

  Definition f (a: atom3) : @formula atom3 :=
    f_atom a.

  Coercion f: atom3 >-> formula.

  Theorem T11_neg : ~ forall P Q : @formula atom3, [P; $~(P /\ ~Q)$] |= Q.
  Proof.
    unfold not.
    intro H.
    specialize (H P Q).
    unfold consequence in H.
    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (val : bool) =>
            match a with
            | P => True
            | _ => False
            end
      ).

    pose (M1 := {|
                ρ := ρ1;
               |}).

    specialize (H M1).
    hnf in H.

    assert (H1 : holds_all M1 [(f_atom P); $~ (P /\ ~ Q)$]).
    {
      unfold holds_all.
      intros f Hin.
      unfold In in Hin.
      destruct Hin as [Hin | [Hin | []]].
      - rewrite <-Hin.
        cbn [FormulaTruth].
        hnf.
        exact I.
      - rewrite <-Hin.
        hnf.
        left.
        cbn [FormulaTruth].
        hnf.
        exact I.
    }

    specialize (H H1).
    clear H1.
    change (FormulaTruth M1 (f_atom Q) true) in H.
    cbn [FormulaTruth] in H.
    hnf in H.
    exact H.
  Qed.

End FDE_excersizes.

Module Syntactic.
  Import Formula1.
  Module F1 := Make_Formula(Formula1).
  Import F1.

  Reserved Notation "A ~> B" (at level 98).
  Inductive entails {atom : Set} : @formula atom -> @formula atom -> Type :=
    | axiom1 : forall A B , $A /\ B$ ~> A
    | axiom2 : forall A B , $A /\ B$ ~> B
    | axiom3 : forall A B , A ~> $A \/ B$
    | axiom4 : forall A B , B ~> $A \/ B$
    | axiom5 : forall A B C, (f_conj A (f_disj B C)) ~> (f_disj (f_conj A B) C)
    | axiom6 : forall A, A ~> $~ ~A$
    | axiom7 : forall A, $~ ~A$ ~> A
    | trans : forall {A B C}, A ~> B -> B ~> C -> A ~> C
    | conj_intro : forall {A B C}, A ~> B -> A ~> C -> A ~> $B /\ C$
    | disj_elim : forall {A B C}, A ~> C -> B ~> C -> $A \/ B$ ~> C
    | contrapos : forall {A B}, A ~> B -> $~ B$ ~> $~ A$
  where "A ~> B" := (entails A B).

Lemma imply_self {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) :
  A ~> A.
Proof.
  specialize (axiom6 A) as H1.
  specialize (axiom7 A) as H2.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

Lemma DeMorganConj {atom : Set} (Γ : @formula atom -> Prop) (A B : @formula atom) :
  (f_not (f_conj A B)) ~> (f_disj (f_not A) (f_not B)).
Proof.
  assert (H1 : f_not A ~> f_not (f_conj A B)).
  {
    apply contrapos.
    apply axiom1.
  }

  assert (H2 : f_not B ~> f_not (f_conj A B)).
  {
    apply contrapos.
    apply axiom2.
  }

  pose proof (disj_elim H1 H2) as H3.
  pose proof (contrapos H3) as H4.
  pose proof (axiom6 (f_conj A B)) as H5.
  pose proof (trans H5 H4) as H6.

  eapply trans.
  -
 with (B := (f_not (f_not (f_disj (f_not A) (f_not B))))).

  (* теперь H_disj_to_notC : X ~> f_not C *)
