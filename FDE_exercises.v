From Mendelson Require Import FSignature.
From Mendelson Require Import FDE_formula.
From Mendelson Require Import FDE_semantics.
From Coq Require Import Lists.List.
Import ListNotations.
Import FDE_FormulaDef.
Import FDE_Formula.
Import RelSemantic.
Local Open Scope formula_scope.

(* A set of worlds is divided into 2 subsets: a set of normal and non-normal worlds.
Нам нужно 2 $\ro$: одно для связи пропозициональных переменных с мирами и значениями истинности.
\ro_{impl} --- для связи между ненормальными мирами и истинностью импликативных формул.
*)

Module RelExcersizes.
  Open Scope rel_scope.

  Theorem T_836 {atom : Type} : forall A B C D : @formula atom, [$~(B /\ ~C) /\ A$] |= $(~B \/ C) \/ D$.
  Proof.
    intros A B C D.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    simpl.
    rewrite Bool.orb_true_iff.
    left.

    specialize (in_eq $~ (B /\ ~ C) /\ A$ nil) as H1.
    specialize (H $~ (B /\ ~ C) /\ A$).
    specialize (H H1).
    clear H1.
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H _].

    rewrite Bool.orb_true_iff in H.
    rewrite Bool.orb_true_iff.
    destruct H as [H | H].
    - left.
      exact H.
    - right.
      exact H.
  Qed.

  Theorem T_3 {atom : Type} : forall A B C : @formula atom, [$A /\ (B \/ C)$] |= $(A /\ B) \/ (A /\ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ (B \/ C)$).
    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite Bool.orb_true_iff in H2.
    simpl.
    rewrite Bool.orb_true_iff.
    destruct H2 as [H2 | H2].
    - left.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
    - right.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
  Qed.

  Theorem T_4 {atom : Type} : forall A B C : @formula atom, [$A \/ (B /\ C)$] |= $(A \/ B) /\ (A \/ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A \/ B /\ C$).
    specialize (in_eq $A \/ B /\ C$ nil) as H1.
    specialize (H H1).
    clear H1.
    simpl in H.
    rewrite Bool.orb_true_iff in H.
    simpl.
    rewrite Bool.andb_true_iff.
    split.
    -  destruct H as [H | H].
      + rewrite Bool.orb_true_iff.
        left.
        exact H.
      + rewrite Bool.andb_true_iff in H.
        destruct H as [H1 H2].
        rewrite Bool.orb_true_iff.
        right.
        exact H1.
    - destruct H as [H | H].
      + rewrite Bool.orb_true_iff.
        left.
        exact H.
      + rewrite Bool.andb_true_iff in H.
        destruct H as [H1 H2].
        rewrite Bool.orb_true_iff.
        right.
        exact H2.
  Qed.

  Theorem T_5 {atom : Type} : forall A : @formula atom, [A] |= $~ ~A$.
  Proof.
    intro A.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H A).
    specialize (in_eq A nil) as H1.
    specialize (H H1).
    clear H1.

    simpl.
    exact H.
  Qed.

  Theorem T_7 {atom : Type} : forall A B C : @formula atom, [$(A /\ B) -> C$] |= $(A /\ ~C) -> ~B$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ B -> C$).
    specialize (in_eq $A /\ B -> C$ nil) as H1.
    specialize (H H1).
    clear H1.

    unfold implication in H.
    unfold implication.

    simpl in H.
    rewrite Bool.orb_true_iff in H.
    simpl.
    rewrite Bool.orb_true_iff.
    destruct H as [H | H].
    - rewrite Bool.orb_true_iff in H.
      destruct H as [H | H].
      + left.
        rewrite Bool.orb_true_iff.
        left.
        exact H.
      + right.
        exact H.
    - left.
      rewrite Bool.orb_true_iff.
      right.
      exact H.
  Qed.

  Theorem T_12 {atom : Type} : forall A B C : @formula atom, [$(A /\ B) -> C$] |= $A -> (~B \/ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ B -> C$).
    specialize (in_eq $A /\ B -> C$ nil) as H1.
    specialize (H H1).
    clear H1.

    unfold implication in *.

    simpl in H.
    simpl.
    rewrite Bool.orb_true_iff in H.
    rewrite Bool.orb_true_iff.

    destruct H as [H | H].
    - rewrite Bool.orb_true_iff in H.
      destruct H as [H | H].
      + left.
        exact H.
      + right.
        rewrite Bool.orb_true_iff.
        left.
        exact H.
    - right.
      rewrite Bool.orb_true_iff.
      right.
      exact H.
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
            match a, val with
            | P, _ => true
            | _, _ => false
            end
      ).

    pose (M1 := {|
                ρ := ρ1;
               |}).

    specialize (H M1).

    assert (H1 : holds_all M1 [(f_atom P); $~ (P /\ ~ Q)$]).
    {
      unfold holds_all.
      intros f Hin.
      unfold In in Hin.
      destruct Hin as [Hin | [Hin | []]].
      - rewrite <-Hin.
        cbn [eval].
        unfold M1.
        cbn [ρ].
        cbn [ρ1].
        reflexivity.
      - rewrite <-Hin.
        change (eval M1 (f_not (f_conj (f_atom P) (f_not (f_atom Q)))) true = true).
        cbn [eval].
        cbn [negb].
        rewrite Bool.orb_true_iff.
        left.
        unfold M1.
        cbn [ρ].
        cbn [ρ1].
        reflexivity.
    }

    specialize (H H1).
    clear H1.
    change (eval M1 (f_atom Q) true = true) in H.
    cbn [eval] in H.
    unfold M1 in H.
    cbn [ρ] in H.
    cbn [ρ1] in H.
    discriminate H.
  Qed.

  Proposition exfalso_false : ~ (forall {atom : Type} (A B: @formula atom), [$A /\ ~A$] |= B).
  Proof.
    unfold not.
    intro H.
    specialize (H atom3 P Q).

    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (val : bool) =>
            match a, val with
            | P, _ => true
            | _, _ => false
            end
      ).

    pose (M1 := {|
                ρ := ρ1;
               |}).

    specialize (H M1).
    rewrite HoldsAll1 in H.
    assert (H1 : eval M1 $P /\ ~ P$ true = true).
    {
      simpl.
      reflexivity.
    }

    specialize (H H1).
    simpl in H.
    discriminate H.
Qed.
End RelExcersizes.

Import StarSemantic.
Module StarExcersizes.
  Open Scope star_scope.

  Variant atom4 : Set := S | P | Q | R.

  Definition f (a: atom4) : @formula atom4 :=
    f_atom a.

  Coercion f: atom4 >-> formula.

  Variant worlds1 : Set := Γ | Γ'.

  Definition star1 (w : worlds1) : worlds1 :=
  match w with
  | Γ => Γ'
  | Γ' => Γ
  end.

  Lemma star1_involutive : forall w : worlds1, star1 (star1 w) = w.
  Proof.
    intro w.
    destruct w.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Lemma T8_5_5_1 {atom : Type} : forall A B C D : @formula atom,
    [$~(B /\ ~C) /\ A$] |= $(~B \/ C) \/ D$.
  Proof.
    intros A B C D.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.
    specialize (in_eq $~ (B /\ ~ C) /\ A$ nil) as H1.
    specialize (H $~ (B /\ ~ C) /\ A$).
    specialize (H H1).
    clear H1.

    simpl in H.
    rewrite star_involutive in H.
    simpl.

    rewrite Bool.orb_true_iff.
    left.
    rewrite Bool.orb_true_iff.
    rewrite Bool.negb_true_iff.

    rewrite Bool.andb_true_iff in H.
    destruct H as [H _].
    rewrite Bool.negb_true_iff in H.
    rewrite Bool.andb_false_iff in H.
    destruct H as [H | H].
    - left.
      exact H.
    - right.
      rewrite Bool.negb_false_iff in H.
      exact H.
  Qed.

  Theorem T8_5_5_2 : ~ forall (atom : Type) (P Q R : @formula atom), [$P /\ (Q \/ ~Q)$] |= R.
  Proof.
    intro H.
    specialize (H atom4 P Q R).
    unfold consequence in H.
    pose (
        v1 :=
          fun (a : atom4) (w : worlds1) =>
            match a, w with
            | P, Γ => true
            | _, _ => false
            end
      ).

    pose (M1 := {|
      worlds := worlds1;
      w0 := Γ;
      star := star1;
      star_involutive := star1_involutive;
      v := v1;
    |}).

    specialize (H M1 Γ).
    simpl in H.

    assert (H1 : holds_all M1 [$P /\ (Q \/ ~ Q)$] Γ).
    {
      unfold holds_all.
      intros f H1.
      unfold In in H1.
      destruct H1 as [H1 | []].
      rewrite <-H1.
      change (eval M1 (f_conj (f_atom P) (f_disj (f_atom Q) (f_not (f_atom Q)))) Γ = true).
      cbn [eval].
      unfold M1 at 1.
      cbn [v].
      cbn [v1].
      rewrite Bool.andb_true_l.

      unfold M1 at 1.
      cbn [v].
      cbn [v1].
      rewrite Bool.orb_false_l.

      unfold M1 at 1.
      cbn [v].
      unfold M1.
      cbn [star].
      cbn [star1].
      cbn [v1].
      cbn [negb].

      reflexivity.
    }

    specialize (H H1).
    discriminate H.
  Qed.

  Theorem T_3 {atom : Type} : forall A B C : @formula atom, [$A /\ (B \/ C)$] |= $(A /\ B) \/ (A /\ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.

    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
    specialize (H $A /\ (B \/ C)$).
    specialize (H H1).
    clear H1.

    simpl.
    simpl in H.
    rewrite Bool.orb_true_iff.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite Bool.orb_true_iff in H2.
    destruct H2 as [H2 | H2].
    - left.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
    - right.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
  Qed.

  Theorem T_5 {atom : Type} : forall A : @formula atom, [A] |= $~ ~A$.
  Proof.
    intro A.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.

    specialize (in_eq A nil) as H1.
    specialize (H A).
    specialize (H H1).
    clear H1.

    change (eval M (f_not (f_not A)) w = true).
    cbn [eval].

    rewrite Bool.negb_involutive.
    rewrite star_involutive.
    exact H.
  Qed.

  Theorem T_5' {atom : Type} : forall A : @formula atom, [$~ ~A$] |= A.
  Proof.
    intro A.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.

    specialize (in_eq $~ ~A$ nil) as H1.
    specialize (H $~ ~A$).
    specialize (H H1).
    clear H1.

    change (eval M (f_not (f_not A)) w = true) in H.
    cbn [eval] in H.

    rewrite Bool.negb_involutive in H.
    rewrite star_involutive in H.
    exact H.
  Qed.

  Theorem T_12 {atom : Type} : forall A B C : @formula atom, [$(A /\ B) -> C$] |= $A -> (~B \/ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M w H.
    unfold holds_all in H.

    specialize (in_eq $A /\ B -> C$ nil) as H1.
    specialize (H $A /\ B -> C$).
    specialize (H H1).
    clear H1.

    simpl in H.
    simpl.

    rewrite Bool.orb_true_iff.
    rewrite Bool.negb_true_iff.
    rewrite Bool.orb_true_iff.
    rewrite Bool.negb_true_iff.

    rewrite Bool.orb_true_iff in H.
    rewrite Bool.negb_true_iff in H.
    rewrite Bool.andb_false_iff in H.
    destruct H as [H | H].
    - destruct H as [H | H].
      + left.
        exact H.
      + auto.
    - right.
      auto.
  Qed.

  Theorem T11_neg : ~ forall (atom : Type) (P Q : @formula atom), [P; $~(P /\ ~Q)$] |= Q.
  Proof.
    unfold not.
    intro H.
    specialize (H atom4 P Q).
    unfold consequence in H.
    Abort.
End StarExcersizes.

Import FourValuedSemantic.
Module V4Excersizes.
  Open Scope V4_scope.
(*
  Theorem T_836 {atom : Type} : forall A B C D : @formula atom, [$~(B /\ ~C) /\ A$] |= $(~B \/ C) \/ D$.
  Proof.
    intros A B C D.
    unfold consequence.
    intros M H.
    unfold holds_all in H.
    simpl.
    rewrite Bool.orb_true_iff.
    left.

    specialize (in_eq $~ (B /\ ~ C) /\ A$ nil) as H1.
    specialize (H $~ (B /\ ~ C) /\ A$).
    specialize (H H1).
    clear H1.
    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H _].

    rewrite Bool.orb_true_iff in H.
    rewrite Bool.orb_true_iff.
    destruct H as [H | H].
    - left.
      exact H.
    - right.
      exact H.
  Qed.

  Theorem T_3 {atom : Type} : forall A B C : @formula atom, [$A /\ (B \/ C)$] |= $(A /\ B) \/ (A /\ C)$.
  Proof.
    intros A B C.
    unfold consequence.
    intros M H.
    unfold holds_all in H.

    specialize (H $A /\ (B \/ C)$).
    specialize (in_eq $A /\ (B \/ C)$ nil) as H1.
    specialize (H H1).
    clear H1.

    simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    rewrite Bool.orb_true_iff in H2.
    simpl.
    rewrite Bool.orb_true_iff.
    destruct H2 as [H2 | H2].
    - left.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
    - right.
      rewrite Bool.andb_true_iff.
      exact (conj H1 H2).
  Qed.
*)

End V4Excersizes.
