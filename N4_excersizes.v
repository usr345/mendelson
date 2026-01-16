From Mendelson Require Import FSignature.
From Mendelson Require Import K4.
Require Import Lists.List.
Import ListNotations.
Import Formula1.      (* To use the formula type *)
Import K4.F1.
Import N4.

Module N4_excersizes.
  Open Scope N4_scope.
  Variant atom3 : Set := P | Q | R.

  Definition f (a: atom3) : @formula atom3 :=
    f_atom a.

  Coercion f: atom3 >-> formula.

  Variant worlds2 : Set := Γ | Δ.

  Lemma worlds2_inhabited : inhabited worlds2.
  Proof.
    apply (inhabits Γ).
  Qed.

  Theorem T1_imply_self {atom : Type} : forall A : @formula atom, |= $A -> A$.
  Proof.
    intro A.
    unfold valid.
    intros M w Hnormal.
    hnf.
    destruct (is_normal M w) eqn:Heq.
    - intros w' H1.
      exact H1.
    - discriminate Hnormal.
  Qed.

  Theorem T2 {atom : Type} : forall A : @formula atom, |= $A <-> ~~ A$.
  Proof.
    intro A.
    unfold valid.
    intros M w Hnormal.
    hnf.
    split.
    - hnf.
      destruct (is_normal M w) eqn:Heq.
      + intros w' H1.
        hnf.
        rewrite Bool.negb_involutive.
        exact H1.
      + discriminate Hnormal.
    - hnf.
      destruct (is_normal M w) eqn:Heq.
      + intros w' H1.
        hnf in H1.
        rewrite Bool.negb_involutive in H1.
        exact H1.
      + discriminate Hnormal.
  Qed.

  Theorem T3 {atom : Type} : forall A B : @formula atom, |= $(A /\ B) -> A$.
  Proof.
    intros A B.
    unfold valid.
    intros M w Hnormal.
    hnf.
    destruct (is_normal M w) eqn:Heq.
    + intros w' H1.
      hnf in H1.
      destruct H1 as [H1 _].
      exact H1.
    + discriminate Hnormal.
  Qed.

  Theorem T4 {atom : Type} : forall A B : @formula atom, |= $A -> (A \/ B)$.
  Proof.
    intros A B.
    unfold valid.
    intros M w Hnormal.
    hnf.
    destruct (is_normal M w) eqn:Heq.
    + intros w' H1.
      hnf.
      left.
      exact H1.
    + discriminate Hnormal.
  Qed.

  Theorem T5 {atom : Type} : forall A B C : @formula atom, |= $A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C)$.
  Proof.
    intros A B C.
    unfold valid.
    intros M w Hnormal.
    hnf.
    split.
    - hnf.
      destruct (is_normal M w) eqn:Heq.
      + intros w' H1.
        hnf in H1.
        destruct H1 as [H1 H2].
        hnf in H2.
        hnf.
        destruct H2 as [H2 | H2].
        * left.
          hnf.
          exact (conj H1 H2).
        * right.
          hnf.
          exact (conj H1 H2).
      + discriminate Hnormal.
    - hnf.
      destruct (is_normal M w) eqn:Heq.
      + intros w' H1.
        hnf in H1.
        hnf.
        destruct H1 as [H1 | H1].
        * hnf in H1.
          destruct H1 as [H1 H2].
          split.
          ** exact H1.
          ** hnf.
             left.
             exact H2.
        * hnf in H1.
          destruct H1 as [H1 H2].
          split.
          ** exact H1.
          ** hnf.
             right.
             exact H2.
      + discriminate Hnormal.
  Qed.

  Theorem T6 {atom : Type} : ~ forall A B C : @formula atom3, [$A -> B$; $A -> C$] |= $A -> (B /\ C)$.
  Proof.
    unfold not.
    intro H.
    specialize (H P Q R).
    unfold consequence in H.
    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (w: worlds2) (val : bool) =>
            match w, a, val with
            | Δ, P, true => True
            | _, _, _ => False
            end
      ).

    pose (M := {|
                 worlds := worlds2;
                 worlds_inh := worlds2_inhabited;
                 ρ := ρ1;
                 is_normal := fun (w : worlds2) =>
                                match w with
                                | Γ => true
                                | Δ => false
                                end;

                 ρ_imp := fun (f1 f2 : @formula atom3) (w: worlds2) (val : bool) =>
                            match f1, f2, w, val with
                            | _, _, _, _ => False
                            end
               |}).

    specialize (H M Γ) as H_Γ.
    unfold M at 1 in H_Γ.
    cbn [is_normal] in H_Γ.
    assert (Htrue : true = true).
    {
      reflexivity.
    }

    specialize (H_Γ Htrue).
    clear Htrue.

    assert (H1 : holds_all M Γ [$P -> Q$; $P -> R$]).
    {
      unfold holds_all.
      intros Hnormal f H1.
      unfold In in H1.
      destruct H1 as [H1 | [H1 | []]].
      - rewrite <-H1.
        hnf.
        intros w' H2.
        change (FormulaTruth M (f_atom P) w' true) in H2.
        cbn [FormulaTruth] in H2.
        change (FormulaTruth M (f_atom Q) w' true).
        cbn [FormulaTruth].
        destruct w'.
        + hnf in H2.
          destruct H2.
        + hnf.
          exact I.
      - rewrite <-H1.
        hnf.
        intros w' H2.
        change (FormulaTruth M (f_atom P) w' true) in H2.
        cbn [FormulaTruth] in H2.
        change (FormulaTruth M (f_atom Q) w' true).
        cbn [FormulaTruth].
        destruct w'.
        + hnf.
          exact I.
        + hnf.
          exact I.
    }

    specialize (H_Γ H1).
    hnf in H_Γ.
    specialize (H_Γ Δ).
    clear H1.
    assert (H1 : FormulaTruth M P Δ true).
    {
      change (FormulaTruth M (f_atom P) Δ true).
      cbn [FormulaTruth].
      hnf.
      exact I.
    }

    specialize (H_Γ H1).
    change (FormulaTruth M (f_conj (f_atom Q) (f_atom R)) Δ true) in H_Γ.
    cbn [FormulaTruth] in H_Γ.
    destruct H_Γ as [H2 H3].



End N4_excersizes.
