From Mendelson Require Import FSignature.
From Mendelson Require Import MSets.
Require Import Lists.List.
Import ListNotations.
Set Implicit Arguments.
Generalizable All Variables.

Module Formula1 <: TFormula.
  Inductive formula {atom : Type} : Type :=
  | f_atom : atom -> formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula
  | f_imp  : formula -> formula -> formula.

  Definition t {atom : Type} := @formula atom.
  Definition negation {atom : Type} := @f_not atom.
  Definition conjunction {atom : Type} := @f_conj atom.
  Definition disjunction {atom : Type} := @f_disj atom.
  Definition implication {atom : Type} := @f_imp atom.
  Definition equivalence {atom : Type} (A B: @formula atom) : formula := conjunction (implication A B) (implication B A).
End Formula1.

Module K4.
  Import Formula1.
  Module F1:= Make_Formula(Formula1).

  Record Model (atom : Type) :=
  {
    worlds : Type;
    worlds_inh : inhabited worlds;
    ρ : atom -> worlds -> bool -> Prop;
  }.

  Fixpoint FormulaTruth {atom : Type} (M: Model atom) (f : formula)
    (w : worlds M) (b : bool) : Prop :=
    match f with
    | f_atom A => ρ M A w b
    | f_not f' => FormulaTruth M f' w (negb b)
    | f_conj f g =>
        match b with
        | true => FormulaTruth M f w true /\ FormulaTruth M g w true
        | false => FormulaTruth M f w false \/ FormulaTruth M g w false
        end
    | f_disj f g =>
        match b with
        | true => FormulaTruth M f w true \/ FormulaTruth M g w true
        | false => FormulaTruth M f w false /\ FormulaTruth M g w false
        end
    | f_imp f g =>
        match b with
        (* Implication is evaluated globally over all worlds *)
        | true =>
            forall w' : (worlds M),
              FormulaTruth M f w' true -> FormulaTruth M g w' true
        | false =>
            exists w' : (worlds M),
              FormulaTruth M f w' true /\ FormulaTruth M g w' false
        end
  end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : Model atom) (w : worlds M), FormulaTruth M f w true.

  Declare Scope K4_scope.
  Delimit Scope K4_scope with K4.
  Notation "|= f" := (valid f) (at level 90) : K4_scope.

  Definition holds_all {atom : Type} (M : Model atom) (w : worlds M)
    (Γ : list formula) : Prop := forall f : @formula atom, In f Γ -> FormulaTruth M f w true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : Model atom) (w : worlds M),
      holds_all M w Γ -> FormulaTruth M f w true.

  Notation "Γ |= f" := (consequence Γ f) (at level 90) : K4_scope.

  Lemma valid_as_consequence {atom : Type} (f : @formula atom) :
    valid f <-> consequence [] f.
  Proof.
    split.
    - unfold valid.
      intro H.
      unfold consequence.
      intros M w _.
      specialize (H M w).
      exact H.
    - unfold consequence.
      intro H.
      unfold valid.
      intros M w.
      specialize (H M w).
      apply H.
      unfold holds_all.
      intros f1 H1.
      unfold In in H1.
      destruct H1.
  Qed.
End K4.

Module N4.
  Import Formula1.
  Module F1:= Make_Formula(Formula1).

  Record Model (atom : Type) :=
  {
    worlds : Type;
    worlds_inh : inhabited worlds;
    is_normal : worlds -> bool;
    ρ : atom -> worlds -> bool -> Prop;
    (* Implication valuation at non-normal worlds *)
    ρ_imp : (@formula atom) -> (@formula atom) -> worlds -> bool -> Prop;
  }.

  Fixpoint FormulaTruth {atom : Type} (M: N4.Model atom) (f : formula)
    (w : worlds M) (b : bool) : Prop :=
    match f with
    | f_atom A => ρ M A w b
    | f_not f' => FormulaTruth M f' w (negb b)
    | f_conj f g =>
        match b with
        | true => FormulaTruth M f w true /\ FormulaTruth M g w true
        | false => FormulaTruth M f w false \/ FormulaTruth M g w false
        end
    | f_disj f g =>
        match b with
        | true => FormulaTruth M f w true \/ FormulaTruth M g w true
        | false => FormulaTruth M f w false /\ FormulaTruth M g w false
        end
    | f_imp f g =>
      match is_normal M w with
      | true =>
          (* K4-style global implication *)
          match b with
          | true =>
              forall w' : (worlds M),
                FormulaTruth M f w' true ->
                FormulaTruth M g w' true
          | false =>
              exists w' : (worlds M),
                FormulaTruth M f w' true /\
                FormulaTruth M g w' false
          end
      | false =>
          (* Non-normal: implication is atomic *)
          ρ_imp M f g w b
      end
    end.

  Definition valid {atom : Type} (f : formula) : Prop := forall (M : Model atom) (w : worlds M), (is_normal M w = true) -> FormulaTruth M f w true.

  Declare Scope N4_scope.
  Delimit Scope N4_scope with N4.

  Notation "|= f" := (valid f) (at level 90) : N4_scope.

  Definition holds_all {atom : Type} (M : Model atom) (w : worlds M)
    (Γ : list formula) : Prop := forall f : @formula atom, In f Γ -> FormulaTruth M f w true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : Model atom) (w : worlds M),
      (is_normal M w = true) -> holds_all M w Γ -> FormulaTruth M f w true.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90) : N4_scope.

  Definition K4_to_N4
    {atom : Type}
    (M : K4.Model atom)
    : N4.Model atom :=
    {|
      N4.worlds := K4.worlds M;
      N4.worlds_inh := K4.worlds_inh M;
      N4.is_normal := fun _ => true;
      N4.ρ := K4.ρ M;
      N4.ρ_imp := fun _ _ _ _ => False;
    |}.

Lemma K4_to_N4_preserves_truth :
  forall (atom : Type) (M : K4.Model atom) f w b,
    K4.FormulaTruth M f w b <->
    N4.FormulaTruth (K4_to_N4 M) f w b.
Proof.
  intros atom M f w b.
  revert b.
  revert w.
  induction f ; intros w b ; split ; intro H.
  (* atom -> *)
  - cbn [FormulaTruth].
    cbn [K4.FormulaTruth] in H.
    unfold K4_to_N4.
    cbn [ρ].
    exact H.
  (* atom <- *)
  - cbn [FormulaTruth] in H.
    cbn [K4.FormulaTruth].
    unfold K4_to_N4 in H.
    cbn [ρ] in H.
    exact H.
  (* not -> *)
  - cbn [K4.FormulaTruth] in H.
    cbn [N4.FormulaTruth].
    specialize (IHf w (negb b)).
    apply IHf.
    exact H.
  (* not <- *)
  - cbn [K4.FormulaTruth].
    cbn [N4.FormulaTruth] in H.
    specialize (IHf w (negb b)).
    apply IHf.
    exact H.
  (* conj -> *)
  - cbn [FormulaTruth].
    cbn [K4.FormulaTruth] in H.
    specialize (IHf1 w b).
    specialize (IHf2 w b).
    destruct b.
    + destruct H as [H1 H2].
      rewrite IHf1 in H1.
      rewrite IHf2 in H2.
      exact (conj H1 H2).
    + destruct H as [H | H].
      * rewrite IHf1 in H.
         left.
         exact H.
      * rewrite IHf2 in H.
         right.
         exact H.
  (* conj <- *)
  - cbn [FormulaTruth] in H.
    cbn [K4.FormulaTruth].
    specialize (IHf1 w b).
    specialize (IHf2 w b).
    destruct b.
    + destruct H as [H1 H2].
      rewrite <-IHf1 in H1.
      rewrite <-IHf2 in H2.
      exact (conj H1 H2).
    + destruct H as [H | H].
      * rewrite <-IHf1 in H.
         left.
         exact H.
      * rewrite <-IHf2 in H.
         right.
         exact H.
  (* disj -> *)
  - cbn [FormulaTruth].
    cbn [K4.FormulaTruth] in H.
    specialize (IHf1 w b).
    specialize (IHf2 w b).
    destruct b.
    + destruct H as [H | H].
      * rewrite IHf1 in H.
        left.
        exact H.
      * rewrite IHf2 in H.
        right.
        exact H.
    + destruct H as [H1 H2].
      rewrite IHf1 in H1.
      rewrite IHf2 in H2.
      exact (conj H1 H2).
  (* disj <- *)
  - cbn [FormulaTruth] in H.
    cbn [K4.FormulaTruth].
    specialize (IHf1 w b).
    specialize (IHf2 w b).
    destruct b.
    + destruct H as [H | H].
      * rewrite <-IHf1 in H.
        left.
        exact H.
      * rewrite <-IHf2 in H.
        right.
        exact H.
    + destruct H as [H1 H2].
      rewrite <-IHf1 in H1.
      rewrite <-IHf2 in H2.
      exact (conj H1 H2).
  (* impl -> *)
  - cbn [FormulaTruth].
    cbn [K4.FormulaTruth] in H.
    destruct (is_normal (K4_to_N4 M) w) eqn:HNormal.
    + destruct b.
      * intros w' H1.
        unfold K4_to_N4 in w'.
        cbn [worlds] in w'.
        specialize (IHf2 w' true).
        specialize (H w').
        apply IHf2.
        apply H.
        specialize (IHf1 w' true).
        rewrite <-IHf1 in H1.
        exact H1.
      * destruct H as [w' H].
        exists w'.
        destruct H as [H1 H2].
        specialize (IHf1 w' true).
        specialize (IHf2 w' false).
        rewrite IHf1 in H1.
        rewrite IHf2 in H2.
        exact (conj H1 H2).
    + unfold K4_to_N4 in HNormal.
      cbn [is_normal] in HNormal.
      discriminate HNormal.
  (* impl <- *)
  - cbn [FormulaTruth] in H.
    cbn [K4.FormulaTruth].
    destruct (is_normal (K4_to_N4 M)) eqn:HNormal.
    + destruct b.
      * intros w' H1.
        specialize (IHf2 w' true).
        rewrite IHf2.
        specialize (H w').
        apply H.
        specialize (IHf1 w' true).
        rewrite IHf1 in H1.
        exact H1.
      * destruct H as [w' H].
        exists w'.
        destruct H as [H1 H2].
        specialize (IHf1 w' true).
        specialize (IHf2 w' false).
        rewrite <-IHf1 in H1.
        rewrite <-IHf2 in H2.
        exact (conj H1 H2).
    + unfold K4_to_N4 in HNormal.
      cbn [is_normal] in HNormal.
      discriminate HNormal.
Qed.
End N4.
