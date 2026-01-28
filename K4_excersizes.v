From Mendelson Require Import FSignature.
From Mendelson Require Import K4.
Require Import Lists.List.
Import ListNotations.
Import Formula1.      (* To use the formula type *)
Import K4.
Import K4.F1.

(* A set of worlds is divided into 2 subsets: a set of normal and non-normal worlds.
Нам нужно 2 $\ro$: одно для связи пропозициональных переменных с мирами и значениями истинности.
\ro_{impl} --- для связи между ненормальными мирами и истинностью импликативных формул.
*)

Module K4_excersizes.
  Open Scope K4_scope.
  Theorem T0_trans {atom : Type} : forall A B C : @formula atom, [$A -> B$; $B -> C$] |= $A -> C$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    simpl.
    intros w' H1.
    specialize (H $A -> B$) as H2.

    assert (H3 : In $A -> B$
                   [$A -> B$; $B -> C$]).
    {
      unfold In.
      left.
      reflexivity.
    }

    specialize (H2 H3).
    clear H3.
    cbn in H2.
    specialize (H2 w' H1).
    (* Получаем B -> C *)
    clear H1.
    specialize (H $B -> C$).
    assert (H1 : In $B -> C$
                   [$A -> B$; $B -> C$]).
    {
      unfold In.
      right.
      left.
      reflexivity.
    }

    specialize (H H1).
    cbn in H.
    specialize (H w' H2).
    exact H.
  Qed.

  Theorem T1_imply_self {atom : Type} : forall A : @formula atom, |= $A -> A$.
  Proof.
    intro A.
    unfold valid.
    intros M w.
    simpl.
    intros w' H.
    exact H.
  Qed.

  Theorem T2_A_nnA {atom : Type} : forall A : @formula atom, |= $A <-> ~ ~A$.
  Proof.
    intro A.
    unfold valid.
    intros M w.
    unfold equivalence.
    cbn.
    split.
    - intros w' H.
      exact H.
    - intros w' H.
      exact H.
  Qed.

  Theorem T3_conj1 {atom : Type} : forall A B : @formula atom, |= $(A /\ B) -> A$.
  Proof.
    intros A B.
    unfold valid.
    intros M w.
    cbn.
    intros w' H.
    destruct H as [H _].
    exact H.
  Qed.

  Theorem T4_disj1 {atom : Type} : forall A B : @formula atom, |= $A -> (A \/ B)$.
  Proof.
    intros A B.
    unfold valid.
    intros M w.
    cbn.
    intros w' H.
    left.
    exact H.
  Qed.

  Theorem T5_distr {atom : Type} : forall A B C : @formula atom, |= $(A /\ (B \/ C)) <-> ((A /\ B) \/ (A /\ C))$.
  Proof.
    intros A B C.
    unfold valid.
    intros M w.
    unfold equivalence.
    cbn.
    split ; intros w' H.
    - destruct H as [H1 H2].
      destruct H2 as [H2 | H2].
      + left.
        exact (conj H1 H2).
      + right.
        exact (conj H1 H2).
    - destruct H.
      + destruct H as [H1 H2].
        split.
        * exact H1.
        * left.
          exact H2.
      + destruct H as [H1 H2].
        split.
        * exact H1.
        * right.
          exact H2.
  Qed.

  Theorem T6 {atom : Type} : forall A B C : @formula atom, [$A -> B$; $A -> C$] |= $A -> (B /\ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    assert (H1 : In $A -> B$
                   [$A -> B$; $A -> C$]).
    {
      unfold In.
      auto.
    }

    specialize (H $A -> B$ H1) as H_AB.
    cbn in H_AB.

    clear H1.
    assert (H1 : In $A -> C$
                   [$A -> B$; $A -> C$]).
    {
      unfold In.
      auto.
    }

    specialize (H $A -> C$ H1) as H_AC.
    clear H1.
    cbn in H_AC.

    cbn.
    intros w' H_A.
    specialize (H_AB w' H_A).
    rename H_AB into H_B.
    specialize (H_AC w' H_A).
    rename H_AC into H_C.
    exact (conj H_B H_C).
  Qed.

  Theorem T7 {atom : Type} : forall A B C : @formula atom, [$A -> C$; $B -> C$] |= $(A \/ B) -> C$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    assert (H1 : In $A -> C$
                   [$A -> C$; $B -> C$]).
    {
      unfold In.
      auto.
    }

    specialize (H $A -> C$ H1) as H_AC.
    cbn in H_AC.
    clear H1.

    assert (H1 : In $B -> C$
                   [$A -> C$; $B -> C$]).
    {
      unfold In.
      auto.
    }

    specialize (H $B -> C$ H1) as H_BC.
    clear H1.
    cbn in H_BC.

    cbn.
    intros w' H1.
    destruct H1 as [H1 | H1].
    - specialize (H_AC w' H1).
      exact H_AC.
    - specialize (H_BC w' H1).
      exact H_BC.
  Qed.

  Theorem T8_weaken {atom : Type} : forall A B C : @formula atom, [$A -> C$] |= $(A /\ B) -> C$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    assert (H1 : In $A -> C$
                   [$A -> C$]).
    {
      unfold In.
      auto.
    }

    specialize (H $A -> C$ H1) as H_AC.
    cbn in H_AC.
    clear H1.

    cbn.
    intros w' H1.
    destruct H1 as [H1 _].
    specialize (H_AC w' H1).
    exact H_AC.
  Qed.

  Theorem T9 {atom : Type} : forall A B C : @formula atom, |= $((A -> B) /\ (A -> C)) -> (A -> (B /\ C))$.
  Proof.
    intros A B C.
    unfold valid.
    intros M w.
    cbn.
    intros _ H.
    destruct H as [H_AB H_AC].
    intros w0 H_A.
    specialize (H_AB w0 H_A).
    specialize (H_AC w0 H_A).
    exact (conj H_AB H_AC).
  Qed.

  Theorem T10 {atom : Type} : forall A B C : @formula atom, |= $((A -> C) /\ (B -> C)) -> ((A \/ B) -> C)$.
  Proof.
    intros A B C.
    unfold valid.
    intros M w.
    cbn.
    intros _ H.
    destruct H as [H_AC H_BC].
    intros w0 H1.
    destruct H1 as [H_A | H_B].
    - specialize (H_AC w0 H_A).
      exact H_AC.
    - specialize (H_BC w0 H_B).
      exact H_BC.
  Qed.

  Theorem T11 {atom : Type} : forall A B C : @formula atom, [$A -> B$] |= $(B -> C) -> (A -> C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    assert (H1 : In $A -> B$
                   [$A -> B$]).
    {
      unfold In.
      auto.
    }

    specialize (H $A -> B$ H1) as H_AB.
    clear H H1.
    cbn in H_AB.
    cbn.
    intros _ H_BC.
    intros w' H_A.
    specialize (H_AB w' H_A).
    specialize (H_BC w' H_AB).
    exact H_BC.
  Qed.

  Theorem T12 {atom : Type} : forall A B C : @formula atom, [$A -> B$] |= $(C -> A) -> (C -> B)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    assert (H1 : In $A -> B$
                   [$A -> B$]).
    {
      unfold In.
      auto.
    }

    specialize (H $A -> B$ H1) as H_AB.
    clear H1.
    cbn in H_AB.
    cbn.
    intros _ H_CA.
    intros w' H_C.
    specialize (H_CA w' H_C).
    specialize (H_AB w' H_CA).
    exact H_AB.
  Qed.

  Theorem T13 {atom : Type} : forall A B C : @formula atom, [$A -> B$; $B -> C$] |= $A -> C$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    assert (H1 : In $A -> B$
                   [$A -> B$; $B -> C$]).
    {
      unfold In.
      auto.
    }

    specialize (H $A -> B$ H1) as H_AB.
    clear H1.
    cbn.
    intros w' H_A.
    cbn in H_AB.
    specialize (H_AB w' H_A).
    rename H_AB into H_B.

    assert (H1 : In $B -> C$
                   [$A -> B$; $B -> C$]).
    {
      unfold In.
      auto.
    }

    specialize (H $B -> C$ H1) as H_BC.
    clear H1.
    cbn in H_BC.
    specialize (H_BC w' H_B).
    exact H_BC.
  Qed.

  Theorem TA1 {atom : Type} : forall A B : @formula atom, |= $A -> (B -> B)$.
  Proof.
    intros A B.
    unfold valid.
    intros M w.
    hnf.
    intros w1 _.
    apply T1_imply_self.
  Qed.

  Theorem TA2 {atom : Type} : forall A B : @formula atom, |= B -> |= $A -> B$.
  Proof.
    intros A B H.
    unfold valid.
    intros M w.
    unfold valid in H.
    hnf.
    intros w' _.
    specialize (H M w').
    exact H.
  Qed.

  Variant atom3 : Set := P | Q | R.

  Definition f (a: atom3) : @formula atom3 :=
    f_atom a.

  Coercion f: atom3 >-> formula.

  Variant worlds1 : Set := Γ.

  Lemma worlds1_inhabited : inhabited worlds1.
  Proof.
    apply (inhabits Γ).
  Qed.

  Theorem T1_neg : ~ forall (atom : Type) (P Q : @formula atom), |= $P /\ (~ P \/ Q) -> Q$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 (f_atom P) (f_atom Q)).
    change (|= $P /\ (~ P \/ Q) -> Q$) in H.
    unfold valid in H.
    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (w: worlds1) (val : bool) =>
            match w, a, val with
            | Γ, P, _ => True
            | _, _, _ => False
            end
      ).

    pose (M1 := {|
                 worlds := worlds1;
                 worlds_inh := worlds1_inhabited;
                 ρ := ρ1;
               |}).

    specialize (H M1 Γ).
    hnf in H.
    specialize (H Γ).
    assert (H1 : FormulaTruth M1 $P /\ (~ P \/ Q)$ Γ true).
    {
      hnf.
      split.
      - change (FormulaTruth M1 (f_atom P) Γ true).
        cbn [FormulaTruth].
        hnf.
        exact I.
      - hnf.
        left.
        change (FormulaTruth M1 (f_not (f_atom P)) Γ true).
        cbn [FormulaTruth].
        cbn [negb].
        hnf.
        exact I.
    }

    specialize (H H1).
    cbn in H.
    exact H.
  Qed.

  Theorem T2_neg : ~ forall (atom : Type) (P Q R : @formula atom), [$(P /\ Q) -> R$] |= $P -> (~Q \/ R)$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 (f_atom P) (f_atom Q) (f_atom R)).
    change ([$(P /\ Q) -> R$] |= $P -> (~Q \/ R)$) in H.
    unfold consequence in H.
    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (w: worlds1) (val : bool) =>
            match w, a, val with
            | Γ, P, true => True
            | _, _, _ => False
            end
      ).

    pose (M1 := {|
                worlds := worlds1;
                worlds_inh := worlds1_inhabited;
                ρ := ρ1;
               |}).

    specialize (H M1 Γ).
    assert (H1 : holds_all M1 Γ [$P /\ Q -> R$]).
    {
      unfold holds_all.
      intros f H1.
      unfold In in H1.
      destruct H1 as [H1 | []].
      rewrite <-H1.
      hnf.
      intros w' H2.
      change (FormulaTruth M1 (f_atom R) w' true).
      destruct w' eqn:Heq.
      cbn [FormulaTruth].
      hnf.
      destruct H2 as [_ H_Q].
      change (FormulaTruth M1 (f_atom Q) Γ true) in H_Q.
      cbn [FormulaTruth] in H_Q.
      hnf in H_Q.
      exact H_Q.
    }

    specialize (H H1).
    clear H1.
    hnf in H.
    specialize (H Γ).
    assert (H1 : FormulaTruth M1 P Γ true).
    {
      simpl.
      exact I.
    }

    specialize (H H1).
    hnf in H.
    destruct H as [H | H].
    - simpl in H.
      exact H.
    - simpl in H.
      exact H.
  Qed.

  Theorem T3_neg : ~ forall (atom : Type) (P Q : @formula atom3), |= $P -> (Q \/ ~ Q)$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 (f_atom P) (f_atom Q)).
    change (|= $P -> (Q \/ ~ Q)$) in H.
    unfold valid in H.
    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (w: worlds1) (val : bool) =>
            match w, a, val with
            | Γ, P, true => True
            | _, _, _ => False
            end
      ).

    pose (M1 := {|
                worlds := worlds1;
                worlds_inh := worlds1_inhabited;
                ρ := ρ1;
               |}).

    specialize (H M1 Γ).
    hnf in H.
    specialize (H Γ).
    assert (H1 : FormulaTruth M1 P Γ true).
    {
      simpl.
      exact I.
    }

    specialize (H H1).
    hnf in H.
    destruct H.
    - simpl in H.
      exact H.
    - simpl in H.
      exact H.
  Qed.

  Theorem T4_neg : ~ forall (atom : Type) (P Q : @formula atom), |= $(P /\ ~P) -> Q$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 (f_atom P) (f_atom Q)).
    change (|= $(P /\ ~P) -> Q$) in H.
    unfold valid in H.
    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (w: worlds1) (val : bool) =>
            match w, a, val with
            | Γ, P, true => True
            | Γ, P, false => True
            | _, _, _ => False
            end
      ).

    pose (M1 := {|
                worlds := worlds1;
                worlds_inh := worlds1_inhabited;
                ρ := ρ1;
               |}).

    specialize (H M1 Γ).
    hnf in H.
    specialize (H Γ).
    assert (H1 : FormulaTruth M1 $P /\ ~ P$ Γ true).
    {
      hnf.
      change (FormulaTruth M1 (f_atom P) Γ true /\ FormulaTruth M1 (f_not (f_atom P)) Γ true).
      cbn [FormulaTruth].
      cbn [negb].
      simpl.
      exact (conj I I).
    }

    specialize (H H1).
    clear H1.
    change (FormulaTruth M1 (f_atom Q) Γ true) in H.
    cbn [FormulaTruth] in H.
    hnf in H.
    exact H.
  Qed.

  Theorem T5_neg : ~ forall (atom : Type) (P Q : @formula atom), |= $(P -> Q) -> (~Q -> ~P)$.
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 (f_atom P) (f_atom Q)).
    change (|= $(P -> Q) -> (~Q -> ~P)$) in H.
    unfold valid in H.
    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (w: worlds1) (val : bool) =>
            match w, a, val with
            | Γ, Q, false => True
            | _, _, _ => False
            end
      ).

    pose (M1 := {|
                worlds := worlds1;
                worlds_inh := worlds1_inhabited;
                ρ := ρ1;
               |}).

    specialize (H M1 Γ).
    hnf in H.
    specialize (H Γ).
    assert (H1 : FormulaTruth M1 $P -> Q$ Γ true).
    {
      hnf.
      intro w.
      destruct w eqn:Heq.
      change (FormulaTruth M1 (f_atom P) Γ true -> FormulaTruth M1 (f_atom Q) Γ true).
      cbn [FormulaTruth].
      intro H1.
      cbn in H1.
      cbn.
      apply H1.
    }

    specialize (H H1).
    clear H1.
    hnf in H.
    specialize (H Γ).
    assert (H1 : FormulaTruth M1 $~ Q$ Γ true).
    {
      change (FormulaTruth M1 (f_not (f_atom Q)) Γ true).
      cbn [FormulaTruth].
      cbn [negb].
      hnf.
      exact I.
    }

    specialize (H H1).
    change (FormulaTruth M1 (f_not (f_atom P)) Γ true) in H.
    cbn [FormulaTruth] in H.
    cbn [negb] in H.
    hnf in H.
    exact H.
  Qed.

End K4_excersizes.
