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

Module Semantic.
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
  #[global] Notation "|= f" := (valid f) (at level 90) : FDE_scope.

  Definition holds_all {atom : Type} (M : Model atom) (Γ : list formula) : Prop :=
   forall f : @formula atom, In f Γ -> FormulaTruth M f true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : Model atom),
      holds_all M Γ -> FormulaTruth M f true.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : FDE_scope.
End Semantic.

Module FDE_excersizes.
  Import Formula1.
  Import Semantic.
  Import Semantic.F1.
  Open Scope FDE_scope.

  Theorem T_836 {atom : Type} : forall A B C D : @formula atom, [$~(B /\ ~C) /\ A$] |= $(~B \/ C) \/ D$.
  Proof.
    intros A B C D.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    hnf.
    left.

    specialize (in_eq $~ (B /\ ~ C) /\ A$ nil) as H1.
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

    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
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

    specialize (in_eq $A \/ B /\ C$ nil) as H1.
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

    specialize (in_eq A nil) as H1.
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

    specialize (in_eq $A /\ B -> C$ nil) as H1.
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

    specialize (in_eq $A /\ B -> C$ nil) as H1.
    specialize (H $A /\ B -> C$).
    specialize (H H1).
    clear H1.

    unfold implication in *.

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

  Lemma conj_dist : forall P Q R : Prop, P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
  Proof.
  intros P Q R.
  split.
  -
    intros [HP [HQ | HR]].
    + left.
      exact (conj HP HQ).
    + right.
      exact (conj HP HR).
  -
    intros [[HP HQ] | [HP HR]].
    + split.
      * apply HP.
      * left.
        apply HQ.
    + split.
      * apply HP.
      * right.
        apply HR.
  Qed.

  Lemma disj_dist : forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
  Proof.
    intros P Q R. split.
    - (* Forward direction: P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R) *)
      intros [HP | [HQ HR]].
      + split. left. apply HP. left. apply HP.
      + split. right. apply HQ. right. apply HR.
    - (* Backward direction: (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R) *)
      intros [[HP | HQ] [HP' | HR]].
      + left. apply HP. (* P holds *)
      + left. apply HP. (* P holds *)
      + left. apply HP'. (* P holds *)
      + right. split. apply HQ. apply HR. (* P is false, so Q and R must hold *)
  Qed.

(*
  Theorem DeMorganConj {atom : Type} : forall A B : @formula atom, |= $~(A /\ B) <-> ~A \/ ~B$.
  Proof.
    intros A B.
    unfold valid.
    intro M.
    hnf.
    split.
    - simpl.
      rewrite or_comm.
      rewrite disj_dist.
*)


  Theorem FDE_5 {atom : Type} : forall A B C : @formula atom, [$A /\ (B \/ C)$] |= $(A /\ B) \/ C$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
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

  Theorem T11_neg : ~ forall (atom : Type) (P Q : @formula atom), [P; $~(P /\ ~Q)$] |= Q.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 P Q).
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

  Reserved Notation "A |- B" (at level 98).
  Inductive entails {atom : Set} : @formula atom -> @formula atom -> Type :=
    | axiom1 : forall A B , $A /\ B$ |- A
    | axiom2 : forall A B , $A /\ B$ |- B
    | axiom3 : forall A B , A |- $A \/ B$
    | axiom4 : forall A B , B |- $A \/ B$
    | axiom5 : forall A B C, $A /\ (B \/ C)$ |- $(A /\ B) \/ C$
    | axiom6 : forall A, A |- $~ ~A$
    | axiom7 : forall A, $~ ~A$ |- A
    | trans : forall {A B C}, A |- B -> B |- C -> A |- C
    | conj_intro : forall {A B C}, A |- B -> A |- C -> A |- $B /\ C$
    | case_nalysis : forall {A B C}, A |- C -> B |- C -> $A \/ B$ |- C
    | contrapos : forall {A B}, A |- B -> $~ B$ |- $~ A$
  where "A |- B" := (entails A B).

(* метатеоремы *)

Lemma neg_neg_add {atom : Set} (A B : @formula atom) :
  A |- B -> $~ ~ A$ |- B.
Proof.
  intro H1.
  specialize (axiom7 A) as H2.
  specialize (trans H2 H1) as H3.
  exact H3.
Qed.

Lemma neg_neg_del {atom : Set} (A B : @formula atom) :
  $~~ A$ |- B -> A |- B.
Proof.
  intro H1.
  specialize (axiom6 A) as H2.
  specialize (trans H2 H1) as H3.
  exact H3.
Qed.

Lemma neg_neg_add2 {atom : Set} (A B : @formula atom) :
  A |- B -> A |- $~~B$.
Proof.
  intro H1.
  specialize (axiom6 B) as H2.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

Lemma neg_neg_del2 {atom : Set} (A B : @formula atom) :
  A |- $~~B$ -> A |- B.
Proof.
  intro H1.
  specialize (axiom7 B) as H2.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

Lemma contrapos_rev {atom : Set} (A B : @formula atom) :
  $~B$ |- $~A$ -> A |- B.
Proof.
  intro H.
  apply contrapos in H.
  apply neg_neg_del in H.
  apply neg_neg_del2 in H.
  exact H.
Qed.

(* объектные теоремы *)

Lemma imply_self {atom : Set} (Γ : @formula atom -> Prop) (A : @formula atom) :
  A |- A.
Proof.
  specialize (axiom6 A) as H1.
  specialize (axiom7 A) as H2.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

Lemma DeMorganConjRev {atom : Set} (A B : @formula atom) :
  $~A \/ ~B$ |- $~(A /\ B)$.
Proof.
  specialize (axiom1 A B) as H1.
  specialize (contrapos H1) as H2.
  specialize (axiom2 A B) as H3.
  specialize (contrapos H3) as H4.
  specialize (case_nalysis H2 H4) as H5.
  exact H5.
Qed.

Lemma DeMorganDisj {atom : Set} (A B : @formula atom) :
  $~(A \/ B)$ |- $~A /\ ~B$.
Proof.
  specialize (axiom3 A B) as H1.
  specialize (contrapos H1) as H2.
  specialize (axiom4 A B) as H3.
  specialize (contrapos H3) as H4.
  specialize (conj_intro H2 H4) as H5.
  exact H5.
Qed.

Lemma DeMorganDisjRev {atom : Set} (A B : @formula atom) :
  $~A /\ ~B$ |- $~(A \/ B)$.
Proof.
  specialize (axiom1 $~A$ $~B$) as H1.
  specialize (contrapos H1) as H2.
  apply neg_neg_del in H2.
  specialize (axiom2 $~A$ $~B$) as H3.
  specialize (contrapos H3) as H4.
  apply neg_neg_del in H4.
  specialize (case_nalysis H2 H4) as H5.
  specialize (contrapos H5) as H6.
  apply neg_neg_del in H6.
  exact H6.
Qed.

Lemma DeMorganConj {atom : Set} (A B : @formula atom) :
  $~(A /\ B)$ |- $~A \/ ~B$.
Proof.
  assert (H1 : $~~A /\ ~~B$ |- $A /\ B$).
  {
    specialize (axiom1 $~~A$ $~~B$) as H1.
    apply neg_neg_del2 in H1.
    specialize (axiom2 $~~A$ $~~B$) as H2.
    apply neg_neg_del2 in H2.
    specialize (conj_intro H1 H2) as H3.
    exact H3.
  }

  specialize (DeMorganDisj $~A$ $~B$) as H2.
  apply contrapos in H2.
  apply neg_neg_del2 in H2.
  apply contrapos in H1.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

End Syntactic.

Module Meta.
  Import Formula1.
  Import Semantic.
  Import Syntactic.
  Import Syntactic.F1.

  Open Scope FDE_scope.
  Proposition axiom1_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= A.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq $A /\ B$ nil) as H1.
    specialize (H $A /\ B$).
    specialize (H H1).
    clear H1.

    hnf in H.
    destruct H as [H _].
    exact H.
  Qed.

  Proposition axiom2_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= B.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq $A /\ B$ nil) as H1.
    specialize (H $A /\ B$).
    specialize (H H1).
    clear H1.

    hnf in H.
    destruct H as [_ H].
    exact H.
  Qed.

  Proposition axiom3_tautology {atom : Set} (A B: @formula atom) : [A] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq A nil) as H1.
    specialize (H A).
    specialize (H H1).
    clear H1.

    hnf.
    left.
    exact H.
  Qed.

  Proposition axiom4_tautology {atom : Set} (A B: @formula atom) : [B] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq B nil) as H1.
    specialize (H B).
    specialize (H H1).
    clear H1.

    hnf.
    right.
    exact H.
  Qed.

  Proposition axiom5_tautology {atom : Set} (A B C: @formula atom) : [$A /\ (B \/ C)$] |= $(A /\ B) \/ C$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
    specialize (H $A /\ (B \/ C)$).
    specialize (H H1).
    clear H1.

    hnf.
    hnf in H.
    destruct H as [H1 H2].
    hnf in H2.
    destruct H2 as [H2 | H2].
    - left.
      hnf.
      exact (conj H1 H2).
    - right.
      exact H2.
  Qed.

  Proposition axiom6_tautology {atom : Set} (A B C: @formula atom) : [A] |= $~~A$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq A nil) as H1.
    specialize (H A).
    specialize (H H1).
    clear H1.

    hnf.
    rewrite Bool.negb_involutive.
    exact H.
  Qed.

  Proposition axiom7_tautology {atom : Set} (A B C: @formula atom) : [$~~A$] |= A.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (in_eq $~~A$ nil) as H1.
    specialize (H $~~A$).
    specialize (H H1).
    clear H1.

    hnf in H.
    rewrite Bool.negb_involutive in H.
    exact H.
  Qed.

  Proposition trans_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= B -> [B] |= C -> [A] |= C.
  Proof.
    intros H1 H2.
    unfold consequence.
    intros M H3.
    unfold holds_all in H3.

    specialize (in_eq A nil) as H4.
    specialize (H3 A).
    specialize (H3 H4).
    clear H4.

    unfold consequence in H1.
    specialize (H1 M).

    assert (H4 : holds_all M [A]).
    {
      unfold holds_all.
      intros f H.
      unfold In in H.
      destruct H as [H | []].
      rewrite <-H.
      exact H3.
    }

    specialize (H1 H4).
    clear H4.

    unfold consequence in H2.
    specialize (H2 M).

    assert (H4 : holds_all M [B]).
    {
      unfold holds_all.
      intros f H.
      unfold In in H.
      destruct H as [H | []].
      rewrite <-H.
      exact H1.
    }

    specialize (H2 H4).
    clear H4.
    exact H2.
  Qed.

  Proposition conj_intro_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= B -> [A] |= C -> [A] |= $B /\ C$.
  Proof.
    intros H1 H2.
    unfold consequence.
    intros M H3.
    unfold holds_all in H3.

    specialize (H3 A).
    specialize (in_eq A nil) as H4.
    specialize (H3 H4).
    clear H4.

    unfold consequence in H1.
    specialize (H1 M).
    unfold consequence in H2.
    specialize (H2 M).

    assert (H4 : holds_all M [A]).
    {
      unfold holds_all.
      intros f H.
      unfold In in H.
      destruct H as [H | []].
      rewrite <-H.
      exact H3.
    }

    specialize (H1 H4).
    specialize (H2 H4).
    clear H4.

    hnf.
    exact (conj H1 H2).
  Qed.

  Proposition case_analysis_tautology {atom : Set} (A B C: @formula atom) :
    [A] |= C -> [B] |= C -> [$A \/ B$] |= C.
  Proof.
    intros H1 H2.
    unfold consequence.
    intros M H3.
    unfold holds_all in H3.

    specialize (H3 $A \/ B$).
    specialize (in_eq $A \/ B$ nil) as H4.
    specialize (H3 H4).
    clear H4.

    hnf in H3.
    destruct H3 as [H3 | H3].
    - unfold consequence in H1.
      specialize (H1 M).

      assert (H4 : holds_all M [A]).
      {
        unfold holds_all.
        intros f H.
        unfold In in H.
        destruct H as [H | []].
        rewrite <-H.
        exact H3.
      }

      specialize (H1 H4).
      exact H1.
    - unfold consequence in H2.
      specialize (H2 M).

      assert (H4 : holds_all M [B]).
      {
        unfold holds_all.
        intros f H.
        unfold In in H.
        destruct H as [H | []].
        rewrite <-H.
        exact H3.
      }

      specialize (H2 H4).
      exact H2.
  Qed.

(*
  Proposition neg_contrapos_tautology {atom : Set} (A B: @formula atom) :
    ([A] |= B -> [$~B$] |= $~A$) -> False.
  Proof.
    intro H.
    unfold consequence in H.

*)

  Proposition contrapos_tautology {atom : Set} (A B: @formula atom) :
    [A] |= B -> [$~B$] |= $~A$.
  Proof.
    intro H1.
    unfold consequence.
    intros M H2.
    unfold holds_all in H2.
    specialize (H2 $~B$).
    specialize (in_eq $~B$ nil) as H3.
    specialize (H2 H3).
    clear H3.

    hnf in H2.
    cbn [negb] in H2.
    unfold consequence in H1.
    specialize (H1 M).

    hnf.
    cbn [negb].
    unfold holds_all in H1.

    | contrapos : forall {A B}, A |- B -> $~ B$ |- $~ A$

  Theorem soundness {atom : Set} : forall (f : )

End Meta.
