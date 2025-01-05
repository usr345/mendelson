Require Import Coq.Lists.List.
From Mendelson Require Import Formula.
From Mendelson Require Import Syntactic.
From Mendelson Require Import Semantic.

Theorem axiom1_tautology {atom : Set} (A B: @formula atom) : tautology (f_axiom1 A B).
Proof.
  unfold f_axiom1, tautology.
  intro v.
  unfold is_true.
  simpl.
  destruct (eval v A), (eval v B) ; reflexivity.
Qed.

Theorem axiom2_tautology {atom : Set} (A B C: @formula atom) : tautology (f_axiom2 A B C).
Proof.
  unfold f_axiom2, tautology.
  intro v.
  unfold is_true.
  simpl.
  destruct (eval v A), (eval v B), (eval v C) ; reflexivity.
Qed.

Theorem axiom3_tautology {atom : Set} (A B: @formula atom) : tautology (f_axiom3 A B).
Proof.
  unfold f_axiom3, tautology.
  intro v.
  unfold is_true.
  simpl.
  destruct (eval v A), (eval v B) ; reflexivity.
Qed.

Proposition mp_tautology {atom : Set} (A B: @formula atom) : tautology A -> tautology $A -> B$ -> tautology B.
  intros H_A H_AB.
  unfold tautology.
  intro v.
  unfold tautology in H_A, H_AB.
  specialize (H_A v).
  specialize (H_AB v).
  unfold is_true in H_A.
  unfold is_true in H_AB.
  simpl in H_AB.
  destruct (eval v A), (eval v B).
  - reflexivity.
  - simpl in H_AB.
    discriminate H_AB.
  - simpl in H_A.
    discriminate H_A.
  - simpl in H_A.
    discriminate H_A.
Qed.

Definition theorem {atom : Set} (A : @formula atom) :=
  forall Γ : (formula -> Prop), Γ |- A.

Theorem semantic_non_contradictionness {atom : Set} (A : @formula atom) : theorem A -> tautology A.
Proof.
  unfold theorem.
  intro H.
  specialize H with empty.
  induction H as [A H|A B|A B C|A B|A B H1 H2 IH1 IH2].
  - unfold elem in H.
    unfold empty in H.
    contradiction H.
  - apply axiom1_tautology.
  - apply axiom2_tautology.
  - apply axiom3_tautology.
  - apply (mp_tautology B A H2 IH2).
Qed.

Definition fromList {A : Type} (xs : list A) : A -> Prop :=
  fun x => In x xs.

Fixpoint occurs {atom : Set} (i : atom) (p : formula) {struct p} : Prop :=
  match p with
  | f_atom i' => i = i'
  | f_not p1 => occurs i p1
  | f_imp p1 p2 => occurs i p1 \/ occurs i p2
  end.

Definition rewriter {atom : Set} (v : atom -> bool) (l : list atom) : list formula :=
  map (fun i => if v i then f_atom i else f_not (f_atom i)) l.

(* Lemma rewriter_neg_pos {atom : Set} (Γ : @formula atom -> Prop) (f : @formula atom) (v : atom -> bool) (l : list atom) : (Γ |- rewriter v l $~f$) -> (Γ |- rewriter v l f). *)
(* Proof. *)
(*   unfold rewriter. *)
(*   intro H. *)
(*   rewrite eval_neg in H. *)
(*   destruct (eval v f). *)
(*   - simpl in H. *)
(*     apply meta_neg_neg_pos in H. *)
(*     exact H. *)
(*   - simpl in H. *)
(*     exact H. *)
(* Qed. *)

(* Lemma rewriter_pos_neg {atom : Set} (Γ : @formula atom -> Prop) (f : @formula atom) (v : atom -> bool) : (Γ |- rewriter v f) -> (Γ |- rewriter v $~f$). *)
(* Proof. *)
(*   unfold rewriter. *)
(*   intro H. *)
(*   rewrite eval_neg. *)
(*   destruct (eval v f). *)
(*   - simpl in H. *)
(*     apply meta_pos_neg_neg. *)
(*     exact H. *)
(*   - simpl. *)
(*     exact H. *)
(* Qed. *)

Lemma infers_dec {atom : Set} (F : formula) (literals : list atom) (v : atom -> bool) (H: forall i : atom, In i literals <-> occurs i F):
    let Γ := fromList (rewriter v literals) in
    match eval v F with
    | true => Γ |- F
    | false => Γ |- f_not F
    end.
Proof.
  induction literals as [l | b l IH].
  - set (a := get_atom F).
    specialize H with a.
    simpl in H.
    destruct H.
    assert (H1 : occurs a F).
    induction F as [b | G IH | F1 IH1 F2 IH2].
    + simpl.
      simpl in a.
      reflexivity.
    + simpl.
      apply IH.
      * simpl in H.
        simpl in a.
        exact H.
      * simpl in H0.
        simpl in a.
        unfold a in H0.
        exact H0.
    + simpl.
      simpl in a.
      left.
      simpl in H0.
      simpl in H.
      unfold a in H, H0.
      apply IH1.
      apply False_ind.
      intro H1.
      assert (Hor : occurs (get_atom F1) F1 \/ occurs (get_atom F1) F2).
      left.
      exact H1.
      apply H0 in Hor.
      exact Hor.
    + apply H0 in H1.
      destruct H1.
  - simpl in H.
    simpl.
    induction F as [a | G IHF | F1 F2 IH1 IH2].
    + specialize H with a.
      assert(H1 : occurs a (f_atom a)).
      simpl.
      reflexivity.
      apply H in H1 as H2.
      destruct H2 as [name1 | name2].

      destruct (eval v (f_atom a)).
      *
      + specialize (IH H).
      simpl.
      simpl in IH.

  - unfold fromList.
    unfold rewriter.
    destruct (eval v (f_atom a)).

    +
    +

Fixpoint get_letters_rec {atom : Set} (f : @formula atom) (v : atom -> bool) (Γ : formula -> Prop) : formula -> Prop :=
  match f with
  | f_atom f' => extend Γ (rewriter v (f_atom f'))
  | f_not f' => get_letters_rec f' v Γ
  | f_imp f1 f2 => (get_letters_rec f1 v Γ) ∪ (get_letters_rec f2 v Γ)
  end.

Definition get_letters_rewrite {atom : Set} (f : @formula atom) (v : atom -> bool) : formula -> Prop :=
  get_letters_rec f v empty.

Lemma rewriter_true {atom : Set} (f : @formula atom) (v : atom -> bool) : get_letters_rewrite f v |- rewriter v f.
Proof.
  induction f.
  - unfold get_letters_rewrite.
    unfold get_letters_rec.
    unfold rewriter.
    destruct (eval v (f_atom a)).
    + hypo.
    + hypo.
  - unfold get_letters_rewrite.
    simpl.
    apply rewriter_pos_neg.
    unfold get_letters_rewrite in IHf.
    assumption.
  - unfold get_letters_rewrite.
    unfold get_letters_rewrite in IHf1.
    unfold get_letters_rewrite in IHf2.
    unfold rewriter.
    unfold rewriter in IHf1.
    unfold rewriter in IHf2.
    rewrite eval_implication.
    destruct (eval v f1), (eval v f2) ; simpl.
    + apply (weaken (get_letters_rec f2 v empty)).
      * unfold union.
        unfold subset.
        intros A H.
        unfold elem.
        unfold elem in H.
        right.
        exact H.
      * apply drop_antecedent.
        exact IHf2.
    + apply conj_not_not_impl.
      apply meta_conj_intro.
      * apply (weaken (get_letters_rec f1 v empty)).
        ** unfold subset.
           intros A H.
           unfold elem.
           unfold union.
           left.
           exact H.
        ** exact IHf1.
      * apply (weaken (get_letters_rec f2 v empty)).
        ** unfold subset.
           intros A H.
           unfold elem.
           unfold union.
           right.
           exact H.
        ** exact IHf2.
    + apply drop_antecedent.
      apply (weaken (get_letters_rec f2 v empty)).
      * unfold subset.
        intros A H.
        unfold elem.
        unfold union.
        right.
        exact H.
      * exact IHf2.
    + apply meta_neg_a_impl_a_b with (B := f2) in IHf1.
      apply (weaken (get_letters_rec f1 v empty)).
      * unfold subset.
        intros A H.
        unfold elem.
        unfold union.
        left.
        exact H.
      * exact IHf1.
Qed.

Theorem semantic_completeness {atom : Set} (A : @formula atom) (v : atom -> bool) : tautology A -> theorem A.
Proof.
  unfold tautology, theorem.
  intro H.
  specialize (H v) as Hv.
  unfold is_true in Hv.
  intro Γ.
  (* 1 *)
  assert (H1 : get_letters_rewrite A v |- rewriter v A).
  apply rewriter_true.
  unfold rewriter in H1.
  rewrite Hv in H1.
  unfold get_letters_rewrite in H1.
  (* 2 *)
  set (F := (fun _ : atom => false) : atom -> bool).
  assert (H2 : get_letters_rewrite A F |- rewriter F A).
  apply rewriter_true.
  specialize (H F) as Hfalse.
  unfold is_true in Hfalse.
  unfold rewriter in H2.
  rewrite Hfalse in H2.
  unfold get_letters_rewrite in H2.
  (* 3 *)
  induction A as [| A IH | IH1 IH2].
  - simpl in H1.
    simpl in H2.
    unfold rewriter in H1.
    rewrite H in H1.
    apply deduction in H1.
    unfold rewriter in H2.
    simpl in H2.
    apply deduction in H2.
    apply (weaken empty).
    + unfold subset.
      intros A Hempty.
      unfold elem in Hempty.
      unfold empty in Hempty.
      destruct Hempty.
    + apply meta_T_1_10_7 with (A := f_atom a).
      exact H1.
      exact H2.
  - simpl in H2.
    rewrite eval_neg in Hfalse.
    rewrite Bool.negb_true_iff in Hfalse.
    unfold get_letters_rec in H2.
