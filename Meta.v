From Mendelson Require Import Sets.
From Mendelson Require Import FSignature.
From Mendelson Require Import Formula.
From Mendelson Require Import Syntactic.
From Mendelson Require Import Semantic.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Lists.List.
Import ListNotations.

Module Meta.

Theorem axiom1_tautology {atom : Set} (A B: @formula atom) : tautology (f_axiom1 A B).
Proof.
  unfold f_axiom1, tautology.
  intro v.
  unfold is_true.
  simpl.
  (* доказательство перебором *)
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
  unfold tautology in *.
  intro v.
  specialize (H_A v).
  specialize (H_AB v).
  unfold is_true in *.
  simpl in H_AB.
  destruct (eval v A), (eval v B).
  - reflexivity.
  - simpl in H_AB.
    exact H_AB.
  - reflexivity.
  - exact H_A.
Qed.

Definition theorem {atom : Set} (A : @formula atom) :=
  (@empty (@formula atom)) |- A.

Theorem semantic_non_contradictionness {atom : Set} (A : @formula atom) : theorem A -> tautology A.
Proof.
  unfold theorem.
  intro H.
  induction H as [A H|A B|A B C|A B|A B H1 H2 IH1 IH2].
  (* A принадлежит множеству гипотез *)
  - unfold elem in H.
    unfold empty in H.
    contradiction H.
  - apply axiom1_tautology.
  - apply axiom2_tautology.
  - apply axiom3_tautology.
    (* Если есть формула B, которая доказуема в пустом контексте.
       И есть формула $B -> A$, которая доказуема в пустом контексте.
     *)
  - apply (mp_tautology A B IH2 H2).
Qed.

(* Если формула F --- тавтология, то ~F --- не тавтология *)
Lemma tautology_F_not_F_not_tautology {atom : Set} (A : @formula atom) : tautology A -> ~ tautology $~A$.
Proof.
  intro H.
  intro HNot.
  unfold tautology in *.
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

(* Синтаксическая непротиворечивость *)
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

Fixpoint occurs {atom : Set} (a : atom) (F : formula) {struct F} : Prop :=
  match F with
  | f_atom a' => a = a'
  | f_not p1 => occurs a p1
  | f_imp p1 p2 => occurs a p1 \/ occurs a p2
  end.

Proposition occurs_f_occurs_not_f {atom : Set} (f : @formula atom) : forall x : atom, occurs x f <-> occurs x $~f$.
Proof.
  intro x.
  split.
  intro H.
  - simpl.
    exact H.
  - intro H.
    simpl in H.
    exact H.
Qed.

Class EqDec A :=
  {
    eqb: A -> A -> bool;
    eqb_eq : forall x y, (eqb x y) = true <-> x = y
  }.

Proposition eqb_reflexive {A : Type} `{EqDec A}: forall x : A, (eqb x x) = true.
Proof.
  intro x.
  rewrite eqb_eq.
  reflexivity.
Qed.

(* Check if an element is in the list *)
Fixpoint exists_in {A: Type} `{EqDec A} (x: A) (l: list A) : bool :=
  match l with
  | [] => false
  | h :: t => if eqb x h then true else exists_in x t
  end.

Lemma In_exists_true {A: Type} `{Heq: EqDec A} (x : A) (lst : list A) : In x lst <-> (exists_in x lst) = true.
Proof.
  split.
  - intro H.
    induction lst as [|h tail IH].
    + simpl in H.
      destruct H.
    + simpl.
      simpl in H.
      destruct H.
      * symmetry in H.
        rewrite <-eqb_eq in H.
        rewrite H.
        reflexivity.
      * apply IH in H.
        destruct (eqb x h).
        reflexivity.
        apply H.
  - intro H.
    induction lst as [|h tail IH].
    + simpl in H.
      discriminate H.
    + simpl.
      simpl in H.
      destruct (eqb x h) eqn:IEq.
      * rewrite eqb_eq in IEq.
        symmetry in IEq.
        left.
        exact IEq.
      * apply IH in H.
        right.
        exact H.
Qed.

Lemma not_In_exists_false {A: Type} `{Heq: EqDec A} (x : A) (lst : list A) : ~ In x lst <-> (exists_in x lst) = false.
Proof.
  split.
  - intro H.
    induction lst as [|h tail IH].
    + simpl.
      reflexivity.
    + simpl.
      simpl in H.
      apply Decidable.not_or in H.
      destruct H as [H1 H2].
      apply IH in H2.
      destruct (eqb x h) eqn:H.
      * apply eqb_eq in H.
        assert (H3 : true = true).
        { reflexivity. }
        symmetry in H.
        apply H1 in H.
        destruct H.
      * exact H2.
  - intro H.
    induction lst as [|h tail IH].
    + simpl.
      intro H1.
      exact H1.
    + intro H1.
      simpl in H1.
      simpl in H.
      destruct H1 as [H1 | H1].
      * symmetry in H1.
        rewrite <-eqb_eq in H1.
        rewrite H1 in H.
        discriminate H.
      * apply IH.
        destruct (eqb x h) eqn:H2.
        ** discriminate H.
        ** exact H.
        ** exact H1.
Qed.

Lemma exists_in_not_empty {A: Type} `{Heq: EqDec A} (x : A) (lst : list A) : (exists_in x lst) = true -> lst <> [].
Proof.
  intro H.
  rewrite <-In_exists_true in H.
  induction lst as [|h l' IH].
  - simpl in H.
    contradiction H.
  - intro H1.
    discriminate H1.
Qed.

(* Function to remove duplicates from a list *)
Fixpoint remove_duplicates {A : Type} `{EqDec A} (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => if exists_in h (remove_duplicates t)
              then remove_duplicates t
              else h :: remove_duplicates t
  end.

(* Predicate to check if all elements in a list are unique *)
Fixpoint unique {A : Type} (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~ In x xs /\ unique xs
  end.

Lemma in_remove_duplicates {A : Set} `{Heq: EqDec A} (lst : list A) (x : A) :
  In x (remove_duplicates lst) <-> In x lst.
Proof.
  split.
  - induction lst as [|a tail IH].
    + unfold remove_duplicates.
      simpl.
      intro H.
      exact H.
    + simpl.
      destruct (exists_in a (remove_duplicates tail)) eqn:HExists.
      * right.
        apply IH.
        apply H.
      * simpl.
        intro H.
        destruct H.
        ** left.
           exact H.
        ** right.
           apply IH.
           exact H.
  - intro H.
    induction lst as [|a tail IH].
    + simpl.
      simpl in H.
      exact H.
    + simpl in H.
      simpl.
      destruct H.
      * destruct (exists_in a (remove_duplicates tail)) eqn:HExists.
        ** rewrite H in HExists.
           rewrite <-In_exists_true in HExists.
           apply HExists.
        ** simpl.
           left.
           exact H.
      * apply IH in H.
        destruct (exists_in a (remove_duplicates tail)) eqn:HEq.
        ** exact H.
        ** simpl.
           right.
           exact H.
Qed.

Lemma remove_duplicates_unique {A : Set} `{Heq: EqDec A} (lst : list A):
  unique (remove_duplicates lst).
Proof.
  induction lst as [|h tail IH].
  - simpl.
    exact I.
  - simpl.
    destruct (exists_in h (remove_duplicates tail)) eqn:HExists.
    + rewrite <-In_exists_true in HExists.
      rewrite in_remove_duplicates in HExists.
      exact IH.
    + simpl.
      split.
      * rewrite in_remove_duplicates.
        rewrite <-not_In_exists_false in HExists.
        rewrite in_remove_duplicates in HExists.
        exact HExists.
      * exact IH.
Qed.

Lemma unique_remove_duplicates_same {A : Set} `{Heq: EqDec A} (lst : list A) (H : unique lst):
  remove_duplicates lst = lst.
Proof.
  induction lst as [|h tail IH].
  - simpl.
    reflexivity.
  - simpl in H.
    destruct H as [H1 H2].
    apply IH in H2.
    simpl.
    rewrite H2.
    rewrite not_In_exists_false in H1.
    rewrite H1.
    reflexivity.
Qed.

Fixpoint get_letters_rec {atom : Set} `{EqDec atom} (f : @formula atom) (accum : list atom) {struct f} : list atom :=
  match f with
  | f_atom a => if (exists_in a accum) then accum else a :: accum
  | f_not f' => get_letters_rec f' accum
  | f_imp f1 f2 => remove_duplicates ((get_letters_rec f1 accum) ++ get_letters_rec f2 accum)
  end.

Definition get_letters {atom : Set} `{EqDec atom} (f : @formula atom) : list atom :=
  get_letters_rec f nil.

Proposition get_letters_rec_unique {atom : Set} `{Heq : EqDec atom} (f: @formula atom) :
  unique (get_letters_rec f []).
Proof.
  induction f as [| A IH | f1 IH1 f2 IH2] ; simpl.
  - unfold not.
    split.
    + intro H.
      exact H.
    + exact I.
  - exact IH.
    (* Можно использовать другую теорему remove_duplicates_unique  *)
  - apply remove_duplicates_unique.
Qed.

(* Списки букв для f и ~f одинаковы *)
Proposition get_letters_f_not_f {atom : Set} `{EqDec atom} (f : @formula atom) : get_letters f = get_letters $~f$.
Proof.
  unfold get_letters.
  simpl.
  reflexivity.
Qed.

Proposition in_f_in_not_f {atom : Set} `{Heq : EqDec atom} (f : @formula atom) : forall x : atom, In x (get_letters f) <-> In x (get_letters $~ f$).
Proof.
  intro x.
  rewrite <-get_letters_f_not_f.
  reflexivity.
Qed.

Proposition in_remove_duplicates_concat {atom : Set} `{Heq : EqDec atom} (x : atom) (l1 l2 : list atom) : In x (remove_duplicates (l1 ++ l2)) <-> In x l1 \/ In x l2.
Proof.
  rewrite in_remove_duplicates.
  apply in_app_iff.
Qed.

Lemma all_letters_exist_in_get_letters {atom : Set} `{Heq: EqDec atom} (f : @formula atom) :
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
    + apply in_remove_duplicates_concat in H.
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
      rewrite in_remove_duplicates_concat.
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

Lemma remove_duplicates_empty {A : Type} {HEq: EqDec A} (l : list A) : (remove_duplicates l) = [] <-> l = [].
Proof.
  split.
  - intro H.
    induction l as [|x l' IH].
    + reflexivity.
    + simpl in H.
      destruct (exists_in x (remove_duplicates l')) eqn:H1.
      * apply exists_in_not_empty in H1.
        apply H1 in H.
        contradiction H.
      * discriminate H.
  - intro H.
    rewrite H.
    simpl.
    reflexivity.
Qed.

Lemma letters_list_not_empty {atom : Set} `{Heq: EqDec atom} (f : @formula atom) :
  ~ (get_letters f = []).
Proof.
  intro H.
  induction f as [| A IH | f1 IH1 f2 IH2].
  - cbv in H.
    discriminate H.
  - cbn in H.
    unfold get_letters in IH.
    apply IH in H.
    exact H.
  - unfold get_letters in H.
    unfold get_letters in IH1.
    cbn in H.
    rewrite remove_duplicates_empty in H.
    apply app_eq_nil in H.
    destruct H as [H1 H2].
    apply IH1 in H1.
    exact H1.
Qed.

Lemma get_letters_unique {atom : Set} `{Heq: EqDec atom} (f : @formula atom) :
  unique (get_letters f).
Proof.
  unfold get_letters.
  induction f as [| f' IH | f1 IH1 f2 IH2].
  - simpl.
    unfold not.
    rewrite Decidable.not_false_iff.
    split ; exact I.
  - apply IH.
  - simpl.
    apply remove_duplicates_unique.
Qed.

Fixpoint apply_rewriter {atom : Set } `{Heq: EqDec atom} (v : atom -> bool) (letters : list atom) : formula -> Prop :=
  match letters with
      | nil => empty
      | h :: t => extend (apply_rewriter v t) (rewriter v (f_atom h))
  end.

Lemma apply_rewriter_iff_exists {atom : Set} `{Heq: EqDec atom} (v : atom -> bool) (f : @formula atom) (letters : list atom) (A : @formula atom) :
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

Lemma rewriter_subset_left {atom : Set } `{Heq: EqDec atom} (v : atom -> bool) (f1 f2 : @formula atom) (letters1 letters_impl : list atom)
  (H1 : forall x : atom, In x letters1 <-> occurs x f1) (H2 : forall x : atom, In x letters_impl <-> occurs x $f1 -> f2$):
  (apply_rewriter v letters1) ⊆ (apply_rewriter v letters_impl).
Proof.
  unfold subset.
  unfold elem.
  intros A H.
  rewrite (apply_rewriter_iff_exists v A) in H.
  destruct H as [x H].
  rewrite (apply_rewriter_iff_exists v A).
  exists x.
  specialize H1 with x.
  specialize H2 with x.
  destruct H as [H3 H4].
  rewrite H1 in H3.
  assert (H5 : occurs x f1 \/ occurs x f2).
  { exact (or_introl (occurs x f2) H3). }
  simpl in H2.
  rewrite <-H2 in H5.
  split.
  - exact H5.
  - exact H4.
Qed.

Lemma rewriter_subset_right {atom : Set } `{Heq: EqDec atom} (v : atom -> bool) (f1 f2 : @formula atom) (letters2 letters_impl : list atom) (H1 : forall x : atom, In x letters2 <-> occurs x f2) (H2 : forall x : atom, In x letters_impl <-> occurs x $f1 -> f2$):
  (apply_rewriter v letters2) ⊆ (apply_rewriter v letters_impl).
Proof.
  unfold subset.
  unfold elem.
  intros A H.
  rewrite (apply_rewriter_iff_exists v A) in H.
  destruct H as [x H].
  rewrite (apply_rewriter_iff_exists v A).
  exists x.
  specialize H1 with x.
  specialize H2 with x.
  destruct H as [H3 H4].
  rewrite H1 in H3.
  assert (H5 : occurs x f1 \/ occurs x f2).
  { exact (or_intror (occurs x f1) H3). }
  simpl in H2.
  rewrite <-H2 in H5.
  split.
  - exact H5.
  - exact H4.
Qed.

(* Теорема об истинности переписывателей*)
Lemma rewriter_true {atom : Set} `{Heq: EqDec atom} (f : @formula atom) :
  let letters := (get_letters f) in
  forall v : atom -> bool, (apply_rewriter v letters) |- rewriter v f.
Proof.
  intros letters v.
  pose proof (all_letters_exist_in_get_letters f) as HOccurs.
  induction f as [a | f IH | f1 IH1 f2 IH2].
  (* F = f_atom a *)
  (* Мы имеем ситуацию:
     rewriter v (get_letters (f_atom a)) |- rewriter v (f_atom a)
   *)
  - specialize HOccurs with a.
    unfold occurs in HOccurs.
    assert (H3 : a = a).
    { reflexivity. }
    rewrite <-HOccurs in H3.
    apply hypo.
    unfold elem.
    apply (apply_rewriter_iff_exists v (f_atom a)).
    exists a.
    split.
    + exact H3.
    + reflexivity.
  (* F = f_not F' *)
  - apply rewriter_pos_neg.
    apply IH.
    intro x.
    split.
    + intro H.
      specialize (HOccurs x).
      rewrite occurs_f_occurs_not_f.
      apply HOccurs.
      rewrite <-in_f_in_not_f.
      exact H.
    + intro H.
      specialize (HOccurs x).
      rewrite occurs_f_occurs_not_f in H.
      apply HOccurs in H.
      rewrite <-in_f_in_not_f in H.
      exact H.
  - (* F = f_impl F1 F2 *)
    unfold rewriter in *.
    rewrite eval_implication.
    pose proof (all_letters_exist_in_get_letters f1) as HOccurs1.
    pose proof (all_letters_exist_in_get_letters f2) as HOccurs2.
    set (letters1 := get_letters f1).
    set (letters2 := get_letters f2).
    specialize (IH1 HOccurs1).
    specialize (IH2 HOccurs2).
    destruct (eval v f1), (eval v f2) ; simpl.
    (* f1 = T, f2 = T *)
    + apply drop_antecedent.
      apply (weaken (apply_rewriter v letters2)).
      (* Множество букв f2 --- это подмножество всех букв импликации *)
      * apply (rewriter_subset_right v f1 f2 letters2 letters HOccurs2 HOccurs).
      * exact IH2.
    (* f1 = T, f2 = F *)
    + apply conj_not_not_impl.
      apply meta_conj_intro.
      * apply (weaken (apply_rewriter v letters1)).
        (* Множество букв f1 --- это подмножество всех букв импликации *)
         ** apply (rewriter_subset_left v f1 f2 letters1 letters HOccurs1 HOccurs).
         ** apply IH1.
      * apply (weaken (apply_rewriter v letters2)).
         ** apply (rewriter_subset_right v f1 f2 letters2 letters HOccurs2 HOccurs).
         ** apply IH2.
    (* f1 = F, f2 = T *)
    + apply drop_antecedent.
      apply (weaken (apply_rewriter v letters2)).
      * apply (rewriter_subset_right v f1 f2 letters2 letters HOccurs2 HOccurs).
      * exact IH2.
    (* f1 = F, f2 = F *)
    + apply meta_neg_a_impl_a_b with (B := f2) in IH1.
      apply (weaken (apply_rewriter v letters1)).
      * apply (rewriter_subset_left v f1 f2 letters1 letters HOccurs1 HOccurs).
      * exact IH1.
Qed.

Definition LettersList {atom : Set} `{Heq: EqDec atom} (f : @formula atom) : Type :=
  {
    ls : list atom & prod (forall x : atom, In x ls <-> occurs x f)
                       (prod (~ (ls = []))
                          (prod (unique ls) (forall v : atom -> bool, (apply_rewriter v ls) |- rewriter v f))) }.

Definition get_letters_from_formula {atom : Set} `{Heq: EqDec atom} (f : @formula atom) : LettersList f :=
  let lst := get_letters f in
  existT _ lst (pair (all_letters_exist_in_get_letters f)
                 (pair (letters_list_not_empty f)
                       (pair
                          (get_letters_unique f)
                          (rewriter_true f)))).

(* Фунция возвращает:
  * v_a, если v = a
  * (f_not_a v), если v <> a
*)
Definition a_not_a {atom: Set} `{EqDec atom} (a: atom) (v_a: bool) (f_not_a: atom -> bool) (v: atom): bool :=
  match eqb v a with
  | true => v_a
  | false => f_not_a v
  end.

(* Если x не принадлежит списку lst, то (a_not_a x b f) всегда вернет (f x) *)
Lemma rewriter_a_not_a {atom: Set} `{HEqDec: EqDec atom} (x : atom) (lst: list atom) (H : ~(In x lst)) (f : atom -> bool) (b: bool) :
  forall F, (apply_rewriter (a_not_a x b f) lst) F <-> (apply_rewriter f lst) F.
Proof.
  intro F.
  induction lst as [| a lst' IH].
  - simpl.
    reflexivity.
  - simpl in H.
    apply Decidable.not_or in H.
    destruct H as [H1 H2].
    specialize (IH H2).
    simpl.
    unfold a_not_a.
    unfold rewriter.
    unfold eval.
    destruct (eqb a x) eqn:Heq.
    + rewrite eqb_eq in Heq.
      apply H1 in Heq.
      contradiction Heq.
    + unfold extend.
      unfold elem.
      apply or_iff_compat_r.
      exact IH.
Qed.

(* Эта теорема будет выступать в роли индективной гипотезы для семантической полноты *)
Lemma is_theorem_if_it_true_for_all_cases {atom : Set} `{HEqDec: EqDec atom} (f : @formula atom) (letters : list atom) (HUnique: unique letters) :
  (forall v : atom -> bool, apply_rewriter v letters |- f) -> theorem f.
Proof.
  intro H.
  unfold theorem.
  induction letters as [|x l' IH].
  - specialize H with (fun _ => true).
    simpl in H.
    exact H.
  - simpl in H.
    simpl in HUnique.
    destruct HUnique as [H1 H2].
    apply IH.
    exact H2.
    intro v.
    set (FalseFun := a_not_a x false v : atom -> bool).
    set (TrueFun := a_not_a x true v : atom -> bool).
    specialize (rewriter_a_not_a x l' H1 v) as H4.
    specialize (H FalseFun) as HFalse.
    specialize (H TrueFun) as HTrue.
    specialize (eqb_reflexive x) as HEq.
    apply deduction in HFalse.
    assert (Hsubset : subset (apply_rewriter FalseFun l') (apply_rewriter v l')).
    {
      unfold subset.
      unfold elem.
      intros A H5.
      apply (H4 false A).
      exact H5.
    }

    apply weaken with (Δ := (apply_rewriter v l')) in HFalse.
    2: { exact Hsubset. }
    clear Hsubset.

    unfold rewriter in HFalse.
    unfold FalseFun in HFalse.
    unfold a_not_a in HFalse.
    simpl in HFalse.
    rewrite HEq in HFalse.

    apply deduction in HTrue.
    assert (Hsubset : subset (apply_rewriter TrueFun l') (apply_rewriter v l')).
    {
      unfold subset.
      unfold elem.
      intros A H5.
      apply (H4 true A).
      exact H5.
    }

    apply weaken with (Δ := (apply_rewriter v l')) in HTrue.
    2: { exact Hsubset. }
    clear Hsubset.

    unfold rewriter in HTrue.
    unfold TrueFun in HTrue.
    unfold a_not_a in HTrue.
    simpl in HTrue.
    rewrite HEq in HTrue.
    specialize (meta_T_1_10_7 (f_atom x) f HTrue HFalse) as HResult.
    exact HResult.
Qed.

Theorem semantic_completeness {atom : Set} `{EqDec atom} (F : @formula atom) : tautology F -> theorem F.
Proof.
  unfold tautology, theorem.
  intro Htauto.
  (* Пусть letters --- список пропозициональных *)
  set (letters := get_letters_from_formula F).
  destruct letters as [letters [H1 [H2 [H3 H4]]]].

  (* 2 *)
  induction letters as [|h tail IH].
  - contradiction H2.
    reflexivity.
  - simpl in H3.
    destruct H3 as [H31 H32].
    specialize (is_theorem_if_it_true_for_all_cases F tail H32) as H5.
    apply H5.
    intro v.

    set (FalseFun := a_not_a h false v : atom -> bool).
    set (TrueFun := a_not_a h true v : atom -> bool).
    specialize (H4 FalseFun) as HFalse.
    specialize (H4 TrueFun) as HTrue.

    unfold rewriter in HFalse.
    unfold rewriter in HTrue.
    specialize (Htauto FalseFun) as HFun_False.
    specialize (Htauto TrueFun) as HFun_True.
    unfold is_true in HFun_False.
    unfold is_true in HFun_True.
    rewrite HFun_False in HFalse.
    rewrite HFun_True in HTrue.
    simpl in HFalse.
    apply deduction in HFalse.
    simpl in HTrue.
    apply deduction in HTrue.

    apply weaken with (Δ := (apply_rewriter v tail)) in HFalse.
    2: {
      unfold subset.
      unfold elem.
      intros A HContext.
      apply (rewriter_a_not_a h tail H31 v false) in HContext.
      exact HContext.
    }

    apply weaken with (Δ := (apply_rewriter v tail)) in HTrue.
    2: {
      unfold subset.
      unfold elem.
      intros A HContext.
      apply (rewriter_a_not_a h tail H31 v true) in HContext.
      exact HContext.
    }

    specialize (eqb_reflexive h) as HEq.
    unfold rewriter in HFalse.
    unfold eval in HFalse.
    unfold FalseFun in HFalse.
    unfold a_not_a in HFalse.
    rewrite HEq in HFalse.

    unfold rewriter in HTrue.
    unfold eval in HTrue.
    unfold TrueFun in HTrue.
    unfold a_not_a in HTrue.
    rewrite HEq in HTrue.

    specialize (meta_T_1_10_7 (f_atom h) F HTrue HFalse) as HResult.
    exact HResult.
Qed.
End Meta.
