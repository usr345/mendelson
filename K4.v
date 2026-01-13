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

  #[global] Notation "|= f" := (valid f) (at level 90).

  Definition holds_all {atom : Type} (M : Model atom) (w : worlds M)
    (Γ : list formula) : Prop := forall f : @formula atom, In f Γ -> FormulaTruth M f w true.

  Definition consequence {atom : Type} (Γ : list (@formula atom))
    (f : @formula atom) : Prop :=
    forall (M : Model atom) (w : worlds M),
      holds_all M w Γ -> FormulaTruth M f w true.

  #[global] Notation "Γ |= f" := (consequence Γ f) (at level 90).

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
  forall atom (M : K4.Model atom) f w b,
    K4.FormulaTruth M f w b <->
    N4.FormulaTruth (K4_to_N4 M) f w b.

End N4.
