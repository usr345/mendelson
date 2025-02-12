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
Proof.
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

(* Если формула F --- тавтология, то ~F --- не тавтология *)
Lemma tautology_F_not_F_not_tautology {atom : Set} (A : @formula atom) : tautology A -> ~ tautology $~A$.
Proof.
  intro H.
  intro HNot.
  unfold tautology in H.
  unfold tautology in HNot.
  simpl in HNot.
  set (v := fun _ : atom => true).
  specialize (H v).
  specialize (HNot v).
  destruct (eval v A).
  - simpl in HNot.
    unfold is_true in HNot.
    discriminate HNot.
  - unfold is_true in H.
    discriminate H.
Qed.

(* Система L непротиворечива, т.е. не существует формулы A, такой, чтобы A и ~A были теоремами в L *)
Theorem consistency {atom : Set} (A : @formula atom) : theorem A -> theorem $~A$ -> False.
Proof.
  intros H1 H2.
  apply semantic_non_contradictionness in H1.
  apply semantic_non_contradictionness in H2.
  apply tautology_F_not_F_not_tautology in H1.
  apply H1 in H2.
  exact H2.
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

Lemma length_concat_zero {A : Type} (l1 l2 : list A) : length (l1 ++ l2) = 0 <-> length l1 = 0 /\ length l2 = 0.
Proof.
  split.
  - intro H.
    induction l1 as [| l' IH].
    + simpl.
      simpl in H.
      split.
      * reflexivity.
      * exact H.
    + simpl in H.
      discriminate H.
  - intro H.
    destruct H as [H1 H2].
    induction l1 as [| h t IH].
    + simpl.
      exact H2.
    + simpl in H1.
      discriminate H1.
Qed.

Lemma letters_list_not_empty {atom : Set} (f : @formula atom) :
  ~ (length (get_letters f) = 0).
Proof.
  induction f as [| A IH | f1 IH1 f2 IH2].
  - simpl. intro H. discriminate H.
  - intro H.
    unfold get_letters in H.
    cbn in H.
    unfold get_letters in IH.
    apply IH in H.
    exact H.
  - intro H.
    unfold get_letters in H.
    unfold get_letters in IH1.
    cbn in H.
    rewrite length_concat_zero in H.
    destruct H as [H1 H2].
    apply IH1 in H1.
    exact H1.
Qed.

Definition LettersList {atom : Set} (f : @formula atom) : Type := { ls : list atom | (forall x : atom, In x ls <-> occurs x f) /\ ~ (length ls = 0) }.

Definition get_letters_from_formula {atom : Set} (f : @formula atom) : LettersList f :=
  let lst := get_letters f in
  exist _ lst (conj (all_letters_exist_in_get_letters f) (letters_list_not_empty f)).

Definition get_list {atom : Set} {f : @formula atom} (lst : LettersList f) : list atom :=
  match lst with
  | exist _ res p => res
  end.

Definition length {atom : Set} {f : @formula atom} (letters : LettersList f) : nat :=
  let lst := get_list letters in
  length lst.

Fixpoint n_impl {atom : Set} (consequent : @formula atom) (lst : list formula) {struct lst} : @formula atom:=
  match lst with
  | nil => consequent
  | A :: tail => n_impl (f_imp A consequent) tail
  end.

Definition In_flip {A : Type} (xs : list A) : A -> Prop :=
  fun x => In x xs.

Fixpoint apply_rewriter {atom : Set } (v : atom -> bool) (letters : list atom) : formula -> Prop :=
  match letters with
      | nil => empty
      | h :: t => extend (apply_rewriter v t) (rewriter v (f_atom h))
  end.

Fixpoint rewriters_list {atom : Set} (v : atom -> bool) (letters : list atom) : list formula :=
  match letters with
  | nil => nil
  | a :: tail => (rewriter v (f_atom a)) :: (rewriters_list v tail)
  end.

Definition generate_context {atom : Set } (v : atom -> bool) {f : @formula atom} (letters : LettersList f) : formula -> Prop :=
  let lst := get_list letters in
  apply_rewriter v lst.

Lemma rewriter_impl {atom : Set} (v : atom -> bool) (letters : list atom) : forall F : formula, (apply_rewriter v letters) |- F -> empty |- n_impl F (rewriters_list v letters).
Proof.
  induction letters as [| A tail IH].
  - intros F H.
    simpl.
    simpl in H.
    exact H.
  - intros F H.
    simpl.
    simpl in H.
    apply deduction in H.
    specialize (IH (f_imp (rewriter v (f_atom A)) F)).
    specialize (IH H).
    exact IH.
Qed.

Lemma last_elem_impl {atom : Set } (v : atom -> bool) (A : atom) (tail : list atom) (Γ : @formula atom -> Prop) :
  let An := last tail A in
  forall F : formula, Γ |- n_impl F (rewriters_list v (A :: tail)) ->
                 Γ |- f_imp (rewriter v (f_atom An)) (n_impl F (rewriters_list v (removelast (A :: tail)))).
Proof.
  intro An.
  induction tail as [| B tail' IH].
  - intros F H.
    simpl.
    simpl in H.
    simpl in An.
    exact H.
  - intros F H.
    simpl.
    simpl in H.
    simpl in IH.
    simpl in An.
Abort.

Lemma letters_not_letters {atom : Set } {f : @formula atom} (letters : list atom) : (apply_rewriter (fun _ => true) letters |- f) -> (apply_rewriter (fun _ => false) letters |- f) -> empty |- f.
Proof.
  unfold generate_context.
  intros HTrue HFalse.
  simpl.
  simpl in HTrue.
  simpl in HFalse.
  apply rewriter_impl in HTrue.
  apply rewriter_impl in HFalse.
  induction letters.
  - simpl in HTrue.
    exact HTrue.
  - simpl in HTrue.
    simpl in HFalse.
    unfold rewriter in HTrue.
    simpl in HTrue.
    unfold rewriter in HFalse.
    simpl in HFalse.
Abort.

Lemma letters_f_eq_leters_not_f {atom : Set} (f : @formula atom) : LettersList f = LettersList $~f$.
Proof.
  unfold LettersList.
  simpl.
  reflexivity.
Qed.

Check apply_rewriter.

Lemma apply_rewriter_iff_exists {atom : Set} (v : atom -> bool) (f : @formula atom) (letters : list atom) (A : @formula atom) :
  apply_rewriter v letters A <-> exists x, In x letters /\ rewriter v (f_atom x) = A.
Proof.
  split.
  - intros H.
    induction letters as [| h tail IH].
    + simpl in H.
      unfold empty in H.
      destruct H.
    + simpl in H.
      unfold extend in H.
      unfold elem in H.
      destruct H.
      * specialize (IH H).
        destruct IH as [x [H1 H2]].
        exists x.
        split.
        ** simpl.
           right.
           exact H1.
        ** exact H2.
      * exists h.
        split.
        ** simpl.
           left.
           reflexivity.
        ** exact H.
  - intro H.
    destruct H as [x [H1 H2]].
    induction letters as [| h tail IH].
    + simpl in H1.
      destruct H1.
    + simpl.
      unfold extend.
      unfold elem.
      simpl in H1.
      destruct H1.
      * rewrite <-H in H2.
        right.
        exact H2.
      * apply IH in H.
        left.
        exact H.
Qed.

Lemma generate_context_f_iff_generate_context_not_f {atom : Set } (v : atom -> bool) (f : @formula atom) (letters : LettersList f) (letters_not : LettersList $~f$) (A : @formula atom) : generate_context v letters A <-> generate_context v letters_not A.
Proof.
  split.
  - intro H.
    destruct letters_not as [letters_not [H1 H2]].
    destruct letters as [letters [H3 H4]].
    simpl in H1.
    unfold generate_context.
    simpl.
    unfold generate_context in H.
    simpl in H.
    apply (apply_rewriter_iff_exists v A).
    apply (apply_rewriter_iff_exists v A) in H.
    destruct H as [x [H5 H6]].
    exists x.
    specialize (H1 x).
    specialize (H3 x).
    split.
    + rewrite H1.
      rewrite <-H3.
      exact H5.
    + exact H6.
  - intro H.
    destruct letters_not as [letters_not [H1 H2]].
    destruct letters as [letters [H3 H4]].
    unfold generate_context.
    simpl.
    simpl in H1.
    unfold generate_context in H.
    simpl in H.
    apply (apply_rewriter_iff_exists v A).
    apply (apply_rewriter_iff_exists v A) in H.
    destruct H as [x [H5 H6]].
    exists x.
    specialize (H1 x).
    specialize (H3 x).
    split.
    + rewrite H3.
      rewrite <-H1.
      exact H5.
    + exact H6.
Qed.

Lemma letters_f1_from_letters_impl {atom : Set } (v : atom -> bool) (f1 f2 : @formula atom): (LettersList $f1 -> f2$) -> (LettersList f1).
Proof.
  intro letters.
  set (letters1 := get_letters f1).
  exact (exist _ letters1 (conj (all_letters_exist_in_get_letters f1) (letters_list_not_empty f1))).
Qed.

Lemma letters_f2_from_letters_impl {atom : Set } (v : atom -> bool) (f1 f2 : @formula atom): (LettersList $f1 -> f2$) -> (LettersList f2).
Proof.
  intro letters.
  set (letters2 := get_letters f2).
  exact (exist _ letters2 (conj (all_letters_exist_in_get_letters f2) (letters_list_not_empty f2))).
Qed.

Lemma rewriter_subset_left {atom : Set } (v : atom -> bool) (f1 f2 : @formula atom) (letters1 : LettersList f1) (letters2 : LettersList $f1 -> f2$) :
  (generate_context v letters1) ⊆ (generate_context v letters2).
Proof.
  unfold subset.
  unfold elem.
  unfold generate_context.
  intros A H.
  rewrite (apply_rewriter_iff_exists v A) in H.
  destruct H as [x [H1 H2]].
  destruct letters1 as [list1 H3].
  destruct letters2 as [list2 H4].
  simpl.
  simpl in H1.
  simpl in H4.
  destruct H4 as [H4 _].
  destruct H3 as [H3 _].
  rewrite (apply_rewriter_iff_exists v A).
  exists x.
  specialize H3 with x.
  specialize H4 with x.
  rewrite H3 in H1.
  assert (H5 : occurs x f1 \/ occurs x f2).
  { exact (or_introl (occurs x f2) H1). }
  rewrite <-H4 in H5.
  split.
  - exact H5.
  - exact H2.
Qed.

Lemma rewriter_subset_right {atom : Set } (v : atom -> bool) {f1 f2 : @formula atom} (letters1 : LettersList f2) (letters2 : LettersList $f1 -> f2$) :
  (generate_context v letters1) ⊆ (generate_context v letters2).
Proof.
  unfold subset.
  unfold elem.
  unfold generate_context.
  intros A H.
  rewrite (apply_rewriter_iff_exists v A) in H.
  destruct H as [x [H1 H2]].
  destruct letters1 as [list1 H3].
  destruct letters2 as [list2 H4].
  simpl.
  simpl in H1.
  simpl in H4.
  destruct H4 as [H4 _].
  destruct H3 as [H3 _].
  rewrite (apply_rewriter_iff_exists v A).
  exists x.
  specialize H3 with x.
  specialize H4 with x.
  rewrite H3 in H1.
  assert (H5 : occurs x f1 \/ occurs x f2).
  { exact (or_intror (occurs x f1) H1). }
  rewrite <-H4 in H5.
  split.
  - exact H5.
  - exact H2.
Qed.

Create HintDb Kalmar.
Hint Resolve rewriter_subset_left : Kalmar.
Hint Resolve rewriter_subset_right : Kalmar.

Lemma rewriter_true {atom : Set} (v : atom -> bool) {f : @formula atom} (letters : LettersList f) : (generate_context v letters) |- rewriter v f.
Proof.
  induction f as [a | f IH | f1 IH1 f2 IH2].
  (* F = f_atom a *)
  - destruct letters as [letters H].
    destruct H as [H1 H2].
    unfold generate_context.
    simpl.
    specialize H1 with a.
    unfold occurs in H1.
    assert (H3 : a = a).
    { reflexivity. }
    rewrite <-H1 in H3.
    apply hypo.
    unfold elem.
    apply (apply_rewriter_iff_exists v (f_atom a)).
    exists a.
    split.
    + exact H3.
    + reflexivity.
  (* F = f_not F' *)
  - apply rewriter_pos_neg.
    set (lettersF := get_letters_from_formula f).
    apply (weaken (generate_context v lettersF)).
    + unfold subset.
      unfold elem.
      intros A H1.
      rewrite <-generate_context_f_iff_generate_context_not_f with (letters := lettersF).
      exact H1.
    + rewrite <-letters_f_eq_leters_not_f in letters.
      specialize IH with lettersF.
      exact IH.
  - (* F = f_impl F1 F2 *)
    unfold rewriter.
    rewrite eval_implication.
    unfold rewriter in IH1.
    unfold rewriter in IH2.
    (* destruct letters as [letters H]. *)
    (* destruct H as [H1 H2]. *)
    apply (letters_f1_from_letters_impl v) in letters as letters1.
    apply (letters_f2_from_letters_impl v) in letters as letters2.
    destruct (eval v f1), (eval v f2) ; simpl.
    (* f1 = T, f2 = T *)
    + apply drop_antecedent.
      specialize IH2 with letters2.
      apply (weaken (generate_context v letters2)).
      * auto with Kalmar.
      * exact IH2.
    (* f1 = T, f2 = F *)
    + apply conj_not_not_impl.
      apply meta_conj_intro.
      * apply (weaken (generate_context v letters1)).
         ** auto with Kalmar.
         ** specialize IH1 with letters1.
            apply IH1.
      * apply (weaken (generate_context v letters2)).
         ** auto with Kalmar.
         ** specialize IH2 with letters2.
            apply IH2.
    (* f1 = F, f2 = T *)
    + apply drop_antecedent.
      apply (weaken (generate_context v letters2)).
      * auto with Kalmar.
      * specialize IH2 with letters2.
        exact IH2.
    (* f1 = F, f2 = F *)
    + specialize IH1 with letters1.
      apply meta_neg_a_impl_a_b with (B := f2) in IH1.
      apply (weaken (generate_context v letters1)).
      * auto with Kalmar.
      * exact IH1.
Qed.

Theorem contexts_or_equal {atom : Set} (Γ : @formula atom -> Prop) : forall A: @formula atom, ((fun x => (A = x) \/ (x ∈ Γ)) A) <-> ((fun x => (x ∈ Γ) \/ (A = x)) A).
Proof.
  intro A.
  simpl.
  apply or_comm.
Qed.

Theorem test3 {atom : Set} (Γ : @formula atom -> Prop) (A B: @formula atom) :
  (fun x => (A = x) \/ (x ∈ Γ)) |- B -> Γ |- $A -> B$.
Proof.
  intro H.
  assert (Heq : forall A0, (fun x => A = x \/ x ∈ Γ) A0 <-> (fun x => x ∈ Γ \/ A = x) A0).
  {
    intros.
    split.
    - rewrite or_comm.
      intro H1.
      exact H1.
    - rewrite or_comm.
      intro H1.
      exact H1.
  }
  set (H1 := (eq_entails (fun x => A = x \/ x ∈ Γ) (fun x => x ∈ Γ \/ A = x) B Heq)).
  apply H1 in H.
  clear H1.
  apply deduction in H.
  exact H.
Qed.

(* Lemma is_theorem_if_it_passes_all_cases {atom : Set} {f : @formula atom} (letters : LettersList f) : *)
(*   (forall v : atom -> bool, generate_context v letters |- f) -> empty |- f. *)
(* Proof. *)
(*   intros H. *)
(*   destruct letters as [letters H1]. *)
(*   destruct H1 as [H1 H2]. *)
(*   induction letters as [| A ls IH]. *)
(*   - simpl in H2. *)
(*     exfalso. *)
(*     apply H2. *)
(*     reflexivity. *)
(*   - eapply IH. *)
(*     unfold generate_context in H. *)
(*     unfold In_flip in H. *)
(*     simpl in H. *)
(*     unfold generate_context. *)
(*     unfold In_flip. *)
(*     simpl. *)
(*     set (FalseFun := (fun x : atom => false) : atom -> bool). *)
(*     set (TrueFun := (fun _ : atom => true) : atom -> bool). *)
(*     specialize H with FalseFun as HFalse. *)
(*     unfold rewriter in HFalse. *)
(*     simpl in HFalse. *)
(*     specialize H with TrueFun as HTrue. *)
(*     unfold rewriter in HTrue. *)
(*     simpl in HTrue. *)
(*     assert (H4 : forall B : @formula atom, (fun x : formula => f_atom A = x \/ In x (map (fun a : atom => f_atom a) ls)) B <-> (fun x : formula => In x (map (fun a : atom => f_atom a) ls) \/ (f_atom A = x)) B). *)
(*     { *)
(*       intros B. *)
(*       split. *)
(*       - intro Temp. *)
(*         rewrite or_comm. *)
(*         exact Temp. *)
(*       - intro Temp. *)
(*         rewrite or_comm. *)
(*         exact Temp. *)
(*     } *)
(*     apply eq_entails with (Γ' := (fun x : formula => In x (map (fun a : atom => f_atom a) ls) \/ (f_atom A = x))) in HTrue. *)
(*     apply deduction in HTrue. *)
(*     assert (H5 : forall B : @formula atom, (fun x : formula => *)
(*      f_not (f_atom A) = x \/ In x (map (fun a : atom => f_not (f_atom a)) ls)) B <-> (fun x : formula => In x (map (fun a : atom => f_not (f_atom a)) ls) \/ f_not (f_atom A) = x) B). *)
(*     { *)
(*       intros B. *)
(*       split. *)
(*       - intro Temp. *)
(*         rewrite or_comm. *)
(*         exact Temp. *)
(*       - intro Temp. *)
(*         rewrite or_comm. *)
(*         exact Temp. *)
(*     } *)
(*     apply eq_entails with (Γ' := (fun x : formula => In x (map (fun a : atom => f_not (f_atom a)) ls) \/ f_not (f_atom A) = x)) in HFalse. *)
(*     apply deduction in HFalse. *)
(*     assert (Hf : (fun x : formula => In x (map (fun a : atom => f_atom a) ls)) *)
(*          |- f). *)
(*     apply (meta_T_1_10_7 (f_atom A)). *)
(*     apply HTrue. *)
(*     apply HFalse. *)

(*     unfold rewriter in H. *)
(*     destruct (eval v (f_atom A)). *)
(*     + *)

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

Compute atom_eq 1 1.
Print sumbool.
Fixpoint anytail {atom: Set} (tail: list atom) (vhead: bool) (vtail: bool) (v: atom): bool :=
   match tail with
   | [] => vhead
   | (h::t) =>
       match atom_eq v h with
       | left p => vtail
       | right n => anytail t vhead vtail v
       end
   end.

Eval simpl in (@anytail nat [1; 2; 3; 4] true false 1).

Theorem semantic_completeness {atom : Set} (Hatom: inhabited atom) (F : @formula atom) (v : atom -> bool) : tautology F -> theorem F.
Proof.
  unfold tautology, theorem.
  intro Htauto.
  intro Γ.
  (* 1 *)
  set (letters := get_letters_from_formula F).
  set (FalseFun := (fun _ : atom => false) : atom -> bool).
  set (TrueFun := (fun _ : atom => true) : atom -> bool).
  pose proof (rewriter_true FalseFun letters) as HFalse.
  pose proof (rewriter_true TrueFun letters) as HTrue.
  unfold rewriter in HFalse.
  unfold rewriter in HTrue.
  specialize (Htauto FalseFun) as HFun_False.
  specialize (Htauto TrueFun) as HFun_True.
  unfold is_true in HFun_False.
  unfold is_true in HFun_True.
  rewrite HFun_False in HFalse.
  rewrite HFun_True in HTrue.
  destruct letters as [letters [H1 H2]].
  (* 2 *)
  induction letters as [|h tail IH].
  - simpl in H2.
    exfalso.
    apply H2.
    reflexivity.
  - simpl in H1.
    unfold generate_context in HFalse.
    simpl in HFalse.
    unfold rewriter in HFalse.
    simpl in HFalse.
    unfold generate_context in HTrue.
    simpl in HTrue.
    unfold rewriter in HTrue.
    simpl in HTrue.
    apply deduction in HFalse.
    apply deduction in HTrue.
