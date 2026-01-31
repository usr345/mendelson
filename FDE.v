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

Module RelSemantic.
  Import Formula1.
  Module F1:= Make_Formula(Formula1).

  (*
    Возвращает true, если данное булево значение привязано к атому
  *)
  Record Model (atom : Type) :=
  {
    ρ : atom -> bool -> bool;
  }.

  Fixpoint eval {atom : Type} (M: Model atom) (f : formula) (b : bool) : bool :=
    match f with
    | f_atom A => ρ atom M A b
    | f_not f' => negb (eval M f' b)
    | f_conj f g =>
        match b with
        | true => (eval M f true) && (eval M g true)
        | false => (eval M f false) || (eval M g false)
        end
    | f_disj f g =>
        match b with
        | true => (eval M f true) || (eval M g true)
        | false => (eval M f false) && (eval M g false)
        end
  end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : Model atom), eval M f true = true.

  Declare Scope rel_scope.
  #[global] Notation "|= f" := (valid f) (at level 90) : rel_scope.

  Definition holds_all {atom : Type} (M : Model atom) (Γ : list formula) : Prop := forall f : @formula atom, In f Γ -> eval M f true = true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : Model atom), holds_all M Γ -> eval M f true = true.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : rel_scope.

  Lemma HoldsAll1 {atom : Set} (M : @Model atom) (f : @formula atom) : holds_all M [f] <-> eval M f true = true.
  Proof.
    split.
    - intro H.
      unfold holds_all in H.
      specialize (H f).
      specialize (in_eq f nil) as H1.
      specialize (H H1).
      exact H.
    - intro H.
      unfold holds_all.
      intros f1 H1.
      unfold In in H1.
      destruct H1 as [H1 | []].
      rewrite <-H1.
      exact H.
  Qed.

End RelSemantic.

Module StarSemantic.
  Import Formula1.
  Module F1:= Make_Formula(Formula1).
  Import F1.

  Record Model {atom : Type} :=
  {
    worlds : Type;
    w0 : worlds;
    star : worlds -> worlds;
    star_involutive : forall w : worlds, star (star w) = w;
    v : atom -> worlds -> bool;
  }.

  Fixpoint eval {atom : Type} (M: @Model atom) (f : formula) (w : worlds M) : bool :=
    match f with
    | f_atom A => M.(v) A w
    | f_not f' => negb (eval M f' (M.(star) w))
    | f_conj f g => andb (eval M f w) (eval M g w)
    | f_disj f g => orb (eval M f w) (eval M g w)
  end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : @Model atom) (w : M.(worlds)), eval M f w = true.

  Declare Scope star_scope.
  #[global] Notation "|= f" := (valid f) (at level 90) : star_scope.

  Definition holds_all {atom : Type} (M : @Model atom) (Γ : list formula) (w : M.(worlds)) : Prop := forall f : @formula atom, In f Γ -> eval M f w = true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : @Model atom) (w : M.(worlds)),
      holds_all M Γ w -> eval M f w = true.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : star_scope.

  Lemma HoldsAll1 {atom : Set} (M : @Model atom) (w : M.(worlds)) (f : @formula atom) : holds_all M [f] w <-> eval M f w = true.
  Proof.
    split.
    - intro H.
      unfold holds_all in H.
      specialize (H f).
      specialize (in_eq f nil) as H1.
      specialize (H H1).
      exact H.
    - intro H.
      unfold holds_all.
      intros f1 H1.
      unfold In in H1.
      destruct H1 as [H1 | []].
      rewrite <-H1.
      exact H.
  Qed.

  Definition convert1 {atom : Set} (M : @StarSemantic.Model atom) : RelSemantic.Model atom :=
      let ρ1 :=
            fun (a : atom) (val : bool) =>
              match val with
              | true => (M.(v) a M.(w0))
              | false => negb (M.(v) a (M.(star) M.(w0)))
              end
      in
        RelSemantic.Build_Model atom ρ1.

  (*
  Definition convert2 {atom : Set} (M : Semantic.Model atom) : @StarSemantic.Model atom :=
      let ρ1 :=
            fun (a : atom) (val : bool) =>
              match val with
              | true => (M.(v) a M.(w0)) = true
              | false => (M.(v) a (M.(star) M.(w0))) = false
              end
      in
        Semantic.Build_Model atom ρ1.


  Record Model (atom : Type) :=
  {
    ρ : atom -> bool -> Prop;
  }.

  Record Model {atom : Type} :=
  {
    worlds : Type;
    w0 : worlds;
    star : worlds -> worlds;
    star_involutive : forall w : worlds, star (star w) = w;
    v : atom -> worlds -> bool;
  }.


  Theorem convert_rel_star {atom : Set} (A: @formula atom) (Gamma : list (@formula atom)) :
    StarSemantic.consequence Gamma A -> Semantic.consequence Gamma A.
  Proof.
    intro H.
    unfold StarSemantic.consequence in H.
    unfold Semantic.consequence.
    intros M H1.
    unfold Semantic.holds_all in H1.

    pose (convert :

*)

End StarSemantic.

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
  Import RelSemantic.
  Import Syntactic.
  Import Syntactic.F1.

  Open Scope rel_scope.
  Proposition axiom1_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= A.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ B$).
    specialize (in_eq $A /\ B$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H _].
    exact H.
  Qed.

  Proposition axiom2_tautology {atom : Set} (A B: @formula atom) : [$A /\ B$] |= B.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ B$).
    specialize (in_eq $A /\ B$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [_ H].
    exact H.
  Qed.

  Proposition axiom3_tautology {atom : Set} (A B: @formula atom) : [A] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H A).
    specialize (in_eq A nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    rewrite Bool.orb_true_iff.
    left.
    exact H.
  Qed.

  Proposition axiom4_tautology {atom : Set} (A B: @formula atom) : [B] |= $A \/ B$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H B).
    specialize (in_eq B nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    rewrite Bool.orb_true_iff.
    right.
    exact H.
  Qed.

  Proposition axiom5_tautology {atom : Set} (A B C: @formula atom) : [$A /\ (B \/ C)$] |= $(A /\ B) \/ C$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ (B \/ C)$).
    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    rewrite Bool.orb_true_iff.
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite Bool.orb_true_iff in H2.
    destruct H2 as [H2 | H2].
    - left.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
    - right.
      exact H2.
  Qed.

  Proposition axiom6_tautology {atom : Set} (A B C: @formula atom) : [A] |= $~~A$.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H A).
    specialize (in_eq A nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    rewrite Bool.negb_involutive.
    exact H.
  Qed.

  Proposition axiom7_tautology {atom : Set} (A B C: @formula atom) : [$~~A$] |= A.
  Proof.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $~~A$).
    specialize (in_eq $~~A$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
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

    specialize (H3 A).
    specialize (in_eq A nil) as H4.
    specialize (H3 H4).
    clear H4.

    unfold consequence in H1.
    specialize (H1 M).

    rewrite HoldsAll1 in H1.
    specialize (H1 H3).

    unfold consequence in H2.
    specialize (H2 M).
    rewrite HoldsAll1 in H2.

    specialize (H2 H1).
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

    rewrite HoldsAll1 in H1.
    specialize (H1 H3).

    rewrite HoldsAll1 in H2.
    specialize (H2 H3).

    simpl.
    rewrite Bool.andb_true_iff.
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

    simpl in H3.
    rewrite Bool.orb_true_iff in H3.
    destruct H3 as [H3 | H3].
    - unfold consequence in H1.
      specialize (H1 M).
      rewrite HoldsAll1 in H1.
      specialize (H1 H3).
      exact H1.
    - unfold consequence in H2.
      specialize (H2 M).
      rewrite HoldsAll1 in H2.
      specialize (H2 H3).
      exact H2.
  Qed.

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

    simpl.
    rewrite Bool.negb_true_iff.
    simpl in H2.
    rewrite Bool.negb_true_iff in H2.
    destruct (eval M A true) eqn:Heq.
    - assert (H3 : holds_all M [A]).
      {
        unfold holds_all.
        intros f H3.
        unfold In in H3.
        destruct H3 as [H3 | []].
        rewrite <-H3.
        exact Heq.
      }

      specialize (H1 H3).
      rewrite H1 in H2.
      exact H2.
    - reflexivity.
  Qed.

  (* Theorem soundness {atom : Set} : forall (f : ) *)

End Meta.
