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

Lemma rewriter_append {atom : Set } (v : atom -> bool) (F : formula) (l1 l2 : list atom) : In F (rewriter v (l1 ++ l2)) <-> In F (rewriter v l1) \/ In F (rewriter v l2).
Proof.
  unfold rewriter.
  rewrite map_app.
  apply in_app_iff.
Qed.

(* Lemma rewriter_neg_pos {atom : Set} (Γ : @formula atom -> Prop) (f : @formula atom) (v : atom -> bool) (l : list atom) : (fromList (rewriter v l) |- $~f$) -> (fromList (rewriter v l) |- f). *)
(* Proof. *)
(*   unfold fromList. *)
(*   intro H. *)

(*   unfold rewriter. *)
(*   unfold rewriter in H. *)
(*   rewrite eval_neg in H. *)

Lemma rewriter_subset_left {atom : Set } (v : atom -> bool) (l1 l2 : list atom) : fromList (rewriter v l1) ⊆ fromList (rewriter v (l1 ++ l2)).
Proof.
  unfold subset.
  unfold elem.
  intros A H.
  apply rewriter_append.
  left.
  exact H.
Qed.

Lemma rewriter_subset_right {atom : Set } (v : atom -> bool) (l1 l2 : list atom) : fromList (rewriter v l2) ⊆ fromList (rewriter v (l1 ++ l2)).
Proof.
  unfold subset.
  unfold elem.
  intros A H.
  apply rewriter_append.
  right.
  exact H.
Qed.

Create HintDb Kalmar.
Hint Resolve rewriter_subset_left : Kalmar.
Hint Resolve rewriter_subset_right : Kalmar.

Lemma rewriter_true {atom : Set} (p : formula) :
  { literals : list atom
  | ( forall i, In i literals <-> occurs i p ) /\
    ( forall e,
      let Γ := fromList (rewriter e literals) in
      if eval e p then Γ |- p else Γ |- f_not p
    )
  }.
Proof.
  induction p as [a | G IH | F1 IH1 F2 IH2].
  (* F = f_atom a *)
  - exists (cons a nil).
    split.
    + intro b.
      destruct (atom_eq a b) as [YES | NO].
      rewrite <-YES.
      simpl.
      split.
      * intros _.
        reflexivity.
      * intros _.
        auto.
      * simpl.
        split.
        ** intro H.
           destruct H.
           contradiction.
           destruct H.
        ** intro H.
           symmetry in H.
           contradiction.
    + intros.
      simpl in Γ.
      unfold eval.
      destruct (e a).
      * unfold Γ.
        hypo.
      * unfold Γ.
        hypo.
  (* F = f_not F' *)
  - destruct IH as [l IH].
    exists l.
    destruct IH as [HIn IH].
    simpl.
    split.
    + exact HIn.
    + intro v.
      specialize IH with v.
      destruct (eval v G).
      * simpl.
        simpl in IH.
        apply meta_pos_neg_neg.
        exact IH.
      * simpl.
        exact IH.
  (* F = f_impl F1 F2 *)
  - destruct IH1 as [l1 IH1].
    destruct IH1 as [HIn1 IH1].
    destruct IH2 as [l2 IH2].
    destruct IH2 as [HIn2 IH2].
    exists (l1 ++ l2).
    split.
    + intro b.
      split.
      * simpl.
        rewrite in_app_iff.
        intro H.
        destruct H.
        ** left.
           specialize HIn1 with b.
           apply HIn1 in H.
           exact H.
        ** right.
           specialize HIn2 with b.
           apply HIn2 in H.
           exact H.
      * simpl.
        intro H.
        rewrite in_app_iff.
        destruct H.
        ** specialize HIn1 with b.
           left.
           apply HIn1 in H.
           exact H.
        ** specialize HIn2 with b.
           right.
           apply HIn2 in H.
           exact H.
    + intro v.
      specialize (IH1 v).
      specialize (IH2 v).
      rewrite eval_implication.
      destruct (eval v F1), (eval v F2) ; simpl.
      (* F1 = T, F2 = T *)
      * apply drop_antecedent.
        apply (weaken (fromList (rewriter v l2))).
        ** auto with Kalmar.
        ** exact IH2.
      (* F1 = T, F2 = F *)
      * apply conj_not_not_impl.
        apply meta_conj_intro.
        ** apply (weaken (fromList (rewriter v l1))).
           auto with Kalmar.
           apply IH1.
        ** apply (weaken (fromList (rewriter v l2))).
           auto with Kalmar.
           apply IH2.
      (* F1 = F, F2 = T *)
      *
        apply drop_antecedent.
        apply (weaken (fromList (rewriter v l2))).
        ** auto with Kalmar.
        ** apply IH2.
      (* F1 = F, F2 = F *)
      * apply meta_neg_a_impl_a_b with (B := F2) in IH1.
        apply (weaken (fromList (rewriter v l1))).
        ** auto with Kalmar.
        ** exact IH1.
Qed.

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
