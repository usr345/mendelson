From Mendelson Require Import Formula.
From Mendelson Require Import Syntactic.
From Mendelson Require Import Semantic.
Require Import Coq.Lists.List.
Import ListNotations.

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

Definition rewriter {atom : Set} (v : atom -> bool) (F : @formula atom) : formula :=
  match eval v F with
  | false => $~F$
  | true => F
  end.

Lemma rewriter_neg_pos {atom : Set} (Γ : @formula atom -> Prop) (f : @formula atom) (v : atom -> bool) : (Γ |- rewriter v $~f$) -> (Γ |- rewriter v f).
Proof.
  unfold rewriter.
  intro H.
  rewrite eval_neg in H.
  destruct (eval v f).
  - simpl in H.
    apply meta_neg_neg_pos in H.
    exact H.
  - simpl in H.
    exact H.
Qed.

Lemma rewriter_pos_neg {atom : Set} (Γ : @formula atom -> Prop) (f : @formula atom) (v : atom -> bool) : (Γ |- rewriter v f) -> (Γ |- rewriter v $~f$).
Proof.
  unfold rewriter.
  intro H.
  rewrite eval_neg.
  destruct (eval v f).
  - simpl in H.
    apply meta_pos_neg_neg.
    exact H.
  - simpl.
    exact H.
Qed.

Fixpoint occurs {atom : Set} (i : atom) (p : formula) {struct p} : Prop :=
  match p with
  | f_atom i' => i = i'
  | f_not p1 => occurs i p1
  | f_imp p1 p2 => occurs i p1 \/ occurs i p2
  end.

Fixpoint get_letters_rec {atom : Set} (f : @formula atom) (accum : list atom) {struct f} : list atom :=
  match f with
  | f_atom f' => f' :: accum
  | f_not f' => get_letters_rec f' accum
  | f_imp f1 f2 => (get_letters_rec f1 accum) ++ (get_letters_rec f2 accum)
  end.

Definition get_letters {atom : Set} (f : @formula atom) : list atom :=
  get_letters_rec f nil.

Lemma all_letters_exist_in_get_letters {atom : Set} (f : @formula atom) :
  forall x : atom, In x (get_letters f) <-> occurs x f.
Proof.
  intro x.
  split.
  - intro H.
    unfold get_letters in H.
    induction f as [| A IH | f1 IH1 f2 IH2] ; simpl ; simpl in H.
    + destruct H.
      * symmetry in H.
        exact H.
      * contradiction H.
    + apply IH in H.
      exact H.
    + apply in_app_or in H.
      destruct H.
      * apply IH1 in H.
        left.
        exact H.
      * apply IH2 in H.
        auto.
  - intro H.
    induction f as [| A IH | f1 IH1 f2 IH2] ; simpl ; simpl in H.
    + left.
      symmetry in H.
      exact H.
    + unfold get_letters.
      simpl.
      unfold get_letters in IH.
      apply IH in H.
      exact H.
    + unfold get_letters.
      simpl.
      rewrite in_app_iff.
      destruct H.
      * apply IH1 in H.
        unfold get_letters in H.
        left.
        exact H.
      * apply IH2 in H.
        unfold get_letters in H.
        right.
        exact H.
Qed.

Definition LettersList {atom : Set} (f : @formula atom) : Type := { ls : list atom | forall x : atom, In x ls <-> occurs x f }.

Definition get_letters_from_formula {atom : Set} (f : @formula atom) : LettersList f :=
  let lst := get_letters f in
  exist _ lst (all_letters_exist_in_get_letters f).

Definition get_list {atom : Set} {f : @formula atom} (lst : LettersList f) : list atom :=
  match lst with
  | exist _ res p => res
  end.

Definition In_flip {A : Type} (xs : list A) : A -> Prop :=
  fun x => In x xs.

Definition map_rewriter {atom : Set } (v : atom -> bool) {f : @formula atom} (lst : LettersList f) : list (@formula atom) :=
  map (fun a => rewriter v (f_atom a)) (get_list lst).

Lemma rewriter_subset_left {atom : Set } (v : atom -> bool) (f1 f2 : @formula atom) :
  In_flip
    (map (fun a : atom => rewriter v (f_atom a))
       (get_list (get_letters_from_formula f1)))
  ⊆ In_flip
      (map (fun a : atom => if v a then f_atom a else f_not (f_atom a))
         (get_letters $f1 -> f2$)).
Proof.
  unfold subset.
  unfold elem.
  unfold In_flip.
  intros.
  unfold get_letters.
  unfold rewriter in H.
  rewrite in_map_iff in *.
  destruct H as [x H].
  exists x.
  simpl in H.
  destruct H as [H1 H2].
  split.
  ** exact H1.
  ** unfold get_letters_rec.
     rewrite in_app_iff.
     left.
     unfold get_letters in H2.
     unfold get_letters_rec in H2.
     exact H2.
Qed.

Lemma rewriter_subset_right {atom : Set } (v : atom -> bool) (f1 f2 : @formula atom) :
  In_flip
    (map (fun a : atom => rewriter v (f_atom a))
       (get_list (get_letters_from_formula f2)))
  ⊆ In_flip
      (map (fun a : atom => if v a then f_atom a else f_not (f_atom a))
         (get_letters $f1 -> f2$)).
Proof.
  unfold subset.
  unfold elem.
  unfold In_flip.
  intros.
  unfold get_letters.
  unfold rewriter in H.
  rewrite in_map_iff in *.
  destruct H as [x H].
  exists x.
  simpl in H.
  destruct H as [H1 H2].
  split.
  ** exact H1.
  ** unfold get_letters_rec.
     rewrite in_app_iff.
     right.
     unfold get_letters in H2.
     unfold get_letters_rec in H2.
     exact H2.
Qed.

Create HintDb Kalmar.
Hint Resolve rewriter_subset_left : Kalmar.
Hint Resolve rewriter_subset_right : Kalmar.

Lemma rewriter_true {atom : Set} (f : @formula atom) (v : atom -> bool) :
  In_flip (map (fun a => rewriter v (f_atom a)) (get_list (get_letters_from_formula f))) |- rewriter v f.
Proof.
  induction f as [a | f IH | f1 IH1 f2 IH2].
  (* F = f_atom a *)
  - unfold In_flip.
    simpl.
    unfold rewriter.
    destruct (eval v (f_atom a)).
    + hypo.
    + hypo.
  (* F = f_not F' *)
  - apply rewriter_pos_neg.
    apply IH.
  - (* F = f_impl F1 F2 *)
    unfold rewriter.
    rewrite eval_implication.
    unfold get_letters_from_formula.
    unfold get_list.
    unfold rewriter in IH1.
    simpl in IH1.
    unfold rewriter in IH2.
    simpl in IH2.
    destruct (eval v f1), (eval v f2) ; simpl.
    (* f1 = T, f2 = T *)
    + apply drop_antecedent.
      apply (weaken (In_flip
      (map (fun a : atom => rewriter v (f_atom a))
         (get_list (get_letters_from_formula f2))))).
      * auto with Kalmar.
      * unfold get_letters_from_formula.
        unfold get_list.
        unfold rewriter.
        unfold eval.
        exact IH2.
    (* f1 = T, f2 = F *)
    + apply conj_not_not_impl.
      apply meta_conj_intro.
      * apply (weaken (In_flip
      (map (fun a : atom => if v a then f_atom a else f_not (f_atom a))
         (get_letters f1)))).
         ** apply rewriter_subset_left.
         ** apply IH1.
      * apply (weaken (In_flip (map (fun a : atom => if v a then f_atom a else f_not (f_atom a)) (get_letters f2)))).
         ** apply rewriter_subset_right.
         ** apply IH2.
    (* f1 = F, f2 = T *)
    + apply drop_antecedent.
      apply (weaken (In_flip (map (fun a : atom => rewriter v (f_atom a)) (get_list (get_letters_from_formula f2))))).
      * auto with Kalmar.
      * unfold get_letters_from_formula.
        unfold get_list.
        unfold rewriter.
        unfold eval.
        exact IH2.
    (* f1 = F, f2 = F *)
    + apply meta_neg_a_impl_a_b with (B := f2) in IH1.
      apply (weaken (In_flip (map (fun a : atom => if v a then f_atom a else f_not (f_atom a)) (get_letters f1)))).
      * apply rewriter_subset_left.
      * exact IH1.
Qed.

Lemma or_idempotent (A : Prop) : A \/ A <-> A.
Proof.
  split.
  - intro H.
    destruct H ; exact H.
  - intro.
    apply (or_introl H).
Qed.

Lemma or_identity (A : Prop) : A \/ False <-> A.
Proof.
  split.
  - intro H.
    destruct H.
    + exact H.
    + contradiction H.
  - intro.
    left.
    exact H.
Qed.

Theorem semantic_completeness {atom : Set} (F : @formula atom) (v : atom -> bool) : tautology F -> theorem F.
Proof.
  unfold tautology, theorem.
  intro Htauto.
  specialize (Htauto v) as Hv.
  unfold is_true in Hv.
  intro Γ.
  (* 1 *)
  pose proof (rewriter_true F v) as Hletters.
  unfold rewriter in Hletters.
  rewrite Hv in Hletters.
  (* 2 *)
  set (FalseFun := (fun _ : atom => false) : atom -> bool).
  set (TrueFun := (fun _ : atom => true) : atom -> bool).
  (* 3 *)
  specialize (Htauto FalseFun) as F_true_in_false.
  unfold is_true in F_true_in_false.
  specialize (Htauto TrueFun) as F_true_in_truth.
  unfold is_true in F_true_in_truth.
  (* 3 *)
  induction F as [| F IH | F1 IH1 F2 IH2].
  - simpl in Htauto.
    unfold is_true in Htauto.
    simpl in Hletters.
    pose proof (rewriter_true (f_atom a) FalseFun) as HFalse.
    unfold rewriter in HFalse.
    unfold In_flip in HFalse.
    rewrite F_true_in_false in HFalse.
    cbn in HFalse.

    apply deduction in HFalse.

    pose proof (rewriter_true (f_atom a) TrueFun) as HTrue.
    unfold rewriter in HTrue.
    unfold In_flip in HTrue.
    rewrite F_true_in_truth in HTrue.
    cbn in HTrue.

    rewrite or_identity in HFalse.
    Search (?a \/ False).

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
