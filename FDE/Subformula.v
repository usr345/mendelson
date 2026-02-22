From Basis Require Import FSignature.
From FDE Require Import Formula.
From Coq Require Import Arith.
From Coq Require Import Arith.Plus.
Import FormulaDef.
Import FDE_Formula.
Local Open Scope formula_scope.

Module Subformula.
Inductive subformula_rel {atom : Type} : (@formula atom) -> @formula atom -> Prop :=
| subformula_refl : forall f : @formula atom, subformula_rel f f
| subformula_neg : forall (f' f : @formula atom), (subformula_rel f' f) -> subformula_rel f' (f_not f)
| subformula_conjl : forall (f' f g : @formula atom), (subformula_rel f' f) -> subformula_rel f' (f_conj f g)
| subformula_conjr : forall (g' f g : @formula atom), (subformula_rel g' g) -> subformula_rel g' (f_conj f g)
| subformula_disjl : forall (f' f g : @formula atom), (subformula_rel f' f) -> subformula_rel f' (f_disj f g)
| subformula_disjr : forall (g' f g : @formula atom), (subformula_rel g' g) -> subformula_rel g' (f_disj f g)
.

Theorem subformula_rel_trans {atom : Type} (A B C : @formula atom) : 
  subformula_rel A B -> subformula_rel B C -> subformula_rel A C.
Proof.
  intros HAB HBC.
  induction HBC as [| B' C' Hpre IH | B' C' D Hpre IH | B' C' D Hpre IH | B' C' D Hpre IH | B' C' D Hpre IH ].
  - exact HAB.
  - apply subformula_neg.
    apply IH.
    exact HAB.
  - apply subformula_conjl.
    apply IH.
    exact HAB.
  - apply subformula_conjr.
    apply IH.
    exact HAB.
  - apply subformula_disjl.
    apply IH.
    exact HAB.    
  - apply subformula_disjr.
    apply IH.
    exact HAB.
Qed.

Fixpoint size {atom : Type} (f : @formula atom) : nat :=
  match f with
  | f_atom _ => 1
  | f_not f' => 1 + (size f')
  | f_conj f1 f2 => 1 + (size f1) + (size f2)
  | f_disj f1 f2 => 1 + (size f1) + (size f2)
  end.

Fixpoint degree {atom : Type} (f : @formula atom) : nat :=
  match f with
  | f_atom _ => 0
  | f_not f' => 1 + (degree f')
  | f_conj f1 f2 => 1 + (degree f1) + (degree f2)
  | f_disj f1 f2 => 1 + (degree f1) + (degree f2)
  end.

Lemma size_positive {atom : Type} (f : @formula atom) : size f > 0.
Proof.
  induction f; simpl.
  - unfold gt.
    unfold lt.
    apply le_n.
  - unfold gt.
    unfold lt.
    unfold gt in IHf.
    unfold lt in IHf.
    apply le_S.
    exact IHf.
  - unfold gt.
    unfold lt.
    apply le_n_S.
    apply le_0_n.
  - unfold gt.
    unfold lt.
    apply le_n_S.
    apply le_0_n.
Qed.

Lemma sum_ge_1 : forall a b : nat, 1 <= a -> 1 <= b -> 1 <= a + b.
Proof.
  intros a b H1 H2.
  apply le_trans with (1 + 0).  (* 1 <= 1+0 *)
  - apply le_n.
  - apply plus_le_compat.
    + exact H1.
    + apply le_trans with 1.
      * apply le_S.
        apply le_n.
      * exact H2.
Qed.

Lemma size_not_atom {atom : Type} (f : @formula atom) : (forall a : atom, f <> (f_atom a)) -> size f > 1.
Proof.
  intro H.
  destruct f.
  - specialize (H a).
    specialize (H eq_refl).
    destruct H.
  - simpl.
    unfold gt.
    unfold lt.
    apply le_n_S.
    specialize (size_positive f) as Hpos.
    unfold gt in Hpos.
    unfold lt in Hpos.
    exact Hpos.
  - simpl.
    unfold gt.
    unfold lt.
    apply le_n_S.
    apply sum_ge_1.
    + specialize (size_positive f1) as Hpos.
      unfold gt in Hpos.
      unfold lt in Hpos.
      exact Hpos.
    + specialize (size_positive f2) as Hpos.
      unfold gt in Hpos.
      unfold lt in Hpos.
      exact Hpos.
  - simpl.
    unfold gt.
    unfold lt.
    apply le_n_S.
    apply sum_ge_1.
    + specialize (size_positive f1) as Hpos.
      unfold gt in Hpos.
      unfold lt in Hpos.
      exact Hpos.
    + specialize (size_positive f2) as Hpos.
      unfold gt in Hpos.
      unfold lt in Hpos.
      exact Hpos.
Qed.

Lemma size_formula1 {atom : Type} (a : atom) (f : @formula atom) :
  subformula_rel (f_atom a) f -> (f_atom a) <> f -> size f > 1.
Proof.
  intros H Hne.
  inversion H ; subst.
  - specialize (Hne eq_refl).
    destruct Hne.
  - simpl.
    apply le_n_S.
    apply size_positive.
  - simpl.
    apply le_n_S.
    apply sum_ge_1 ; apply size_positive.
  - simpl.
    apply le_n_S.
    apply sum_ge_1 ; apply size_positive.
  - simpl.
    apply le_n_S.
    apply sum_ge_1 ; apply size_positive.
  - simpl.
    apply le_n_S.
    apply sum_ge_1 ; apply size_positive.
Qed.

Lemma formula_ne_atom {atom : Type} (a : atom) (f : @formula atom) :
  subformula_rel (f_atom a) f -> (f_atom a) <> f -> forall b : atom, f <> (f_atom b).
Proof.
  intros H Hne.
  intro b.
  unfold not.
  intro Heq.
  assert (H1 : size f = 1).
  {
    rewrite Heq.
    cbn [size].
    reflexivity.
  }

  specialize (size_formula1 a f H Hne) as H2.
  rewrite H1 in H2.
  unfold gt in H2.
  unfold lt in H2.
  inversion H2.
  inversion H3.
Qed.

(* Useful for induction principles *)
Lemma size_decreases {atom : Type} (f g : @formula atom) :
  subformula_rel f g -> f <> g -> size f < size g.
Proof.
  revert g.
  induction f.
  - intros g Hsub Hneq.
    simpl.
    specialize (size_not_atom g) as H1.
    specialize (formula_ne_atom a g Hsub Hneq) as H2.
    specialize (H1 H2).
    unfold gt in H1.
    exact H1.
  - specialize (Hneq eq_refl).
    destruct Hneq.
  - (* subformula_neg *)
    cbn [size]. 
    cbn [Nat.add].
    unfold lt in IHsubformula_rel.
    unfold lt.
    apply le_S.
    apply IHsubformula_rel.
    Print le.
    intro; subst; apply Hneq; reflexivity.
  - (* subformula_conjl *)
    simpl. apply le_n_S. apply le_trans with (size f). 
    + apply IHH; intro; subst; apply Hneq; reflexivity.
    + apply le_plus_l.
  - (* subformula_conjr *)
    simpl. apply le_n_S. apply le_trans with (size g).
    + apply IHH; intro; subst; apply Hneq; reflexivity.
    + apply le_plus_r.
  - (* subformula_disjl *)
    simpl. apply le_n_S. apply le_trans with (size f).
    + apply IHH; intro; subst; apply Hneq; reflexivity.
    + apply le_plus_l.
  - (* subformula_disjr *)
    simpl. apply le_n_S. apply le_trans with (size g).
    + apply IHH; intro; subst; apply Hneq; reflexivity.
    + apply le_plus_r.
Qed.

Theorem subformula_rel_antisymmetric {atom} (A B : @formula atom) :
  subformula_rel A B -> subformula_rel B A -> A = B.
Proof.
  intros HAB HBA.
  induction HAB as [| A' B' Hpre IH | A' B' C Hpre IH | A' B' C Hpre IH | A' B' C Hpre IH | A' B' C Hpre IH ].
  - reflexivity.
  - 
End Subformula.