From Mendelson Require Import FSignature.
From Mendelson Require Import FDE_formula.
From Mendelson Require Import FDE_semantics.
Import FDE_FormulaDef.
Import FDE_Formula.

Module Syntactic.
  Reserved Notation "A |- B" (at level 98).
  Inductive entails {atom : Type} : @formula atom -> @formula atom -> Type :=
    | axiom1 : forall A B , $A /\ B$ |- A
    | axiom2 : forall A B , $A /\ B$ |- B
    | axiom3 : forall A B , A |- $A \/ B$
    | axiom4 : forall A B , B |- $A \/ B$
    | axiom5 : forall A B C, $A /\ (B \/ C)$ |- $(A /\ B) \/ C$
    | axiom6 : forall A, A |- $~ ~A$
    | axiom7 : forall A, $~ ~A$ |- A
    | trans : forall {A B C}, A |- B -> B |- C -> A |- C
    | conj_intro : forall {A B C}, A |- B -> A |- C -> A |- $B /\ C$
    | case_nalysis : forall {A B C}, A |- C -> B |- C -> $A \/ B$ |- C
    | contrapos : forall {A B}, A |- B -> $~ B$ |- $~ A$
  where "A |- B" := (entails A B).

(* метатеоремы *)

Lemma neg_neg_add {atom : Type} (A B : @formula atom) :
  A |- B -> $~ ~ A$ |- B.
Proof.
  intro H1.
  specialize (axiom7 A) as H2.
  specialize (trans H2 H1) as H3.
  exact H3.
Qed.

Lemma neg_neg_del {atom : Type} (A B : @formula atom) :
  $~~ A$ |- B -> A |- B.
Proof.
  intro H1.
  specialize (axiom6 A) as H2.
  specialize (trans H2 H1) as H3.
  exact H3.
Qed.

Lemma neg_neg_add2 {atom : Type} (A B : @formula atom) :
  A |- B -> A |- $~~B$.
Proof.
  intro H1.
  specialize (axiom6 B) as H2.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

Lemma neg_neg_del2 {atom : Type} (A B : @formula atom) :
  A |- $~~B$ -> A |- B.
Proof.
  intro H1.
  specialize (axiom7 B) as H2.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

Lemma contrapos_rev {atom : Type} (A B : @formula atom) :
  $~B$ |- $~A$ -> A |- B.
Proof.
  intro H.
  apply contrapos in H.
  apply neg_neg_del in H.
  apply neg_neg_del2 in H.
  exact H.
Qed.

(* объектные теоремы *)

Lemma imply_self {atom : Type} (Γ : @formula atom -> Prop) (A : @formula atom) :
  A |- A.
Proof.
  specialize (axiom6 A) as H1.
  specialize (axiom7 A) as H2.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

Lemma DeMorganConjRev {atom : Type} (A B : @formula atom) :
  $~A \/ ~B$ |- $~(A /\ B)$.
Proof.
  specialize (axiom1 A B) as H1.
  specialize (contrapos H1) as H2.
  specialize (axiom2 A B) as H3.
  specialize (contrapos H3) as H4.
  specialize (case_nalysis H2 H4) as H5.
  exact H5.
Qed.

Lemma DeMorganDisj {atom : Type} (A B : @formula atom) :
  $~(A \/ B)$ |- $~A /\ ~B$.
Proof.
  specialize (axiom3 A B) as H1.
  specialize (contrapos H1) as H2.
  specialize (axiom4 A B) as H3.
  specialize (contrapos H3) as H4.
  specialize (conj_intro H2 H4) as H5.
  exact H5.
Qed.

Lemma DeMorganDisjRev {atom : Type} (A B : @formula atom) :
  $~A /\ ~B$ |- $~(A \/ B)$.
Proof.
  specialize (axiom1 $~A$ $~B$) as H1.
  specialize (contrapos H1) as H2.
  apply neg_neg_del in H2.
  specialize (axiom2 $~A$ $~B$) as H3.
  specialize (contrapos H3) as H4.
  apply neg_neg_del in H4.
  specialize (case_nalysis H2 H4) as H5.
  specialize (contrapos H5) as H6.
  apply neg_neg_del in H6.
  exact H6.
Qed.

Lemma DeMorganConj {atom : Type} (A B : @formula atom) :
  $~(A /\ B)$ |- $~A \/ ~B$.
Proof.
  assert (H1 : $~~A /\ ~~B$ |- $A /\ B$).
  {
    specialize (axiom1 $~~A$ $~~B$) as H1.
    apply neg_neg_del2 in H1.
    specialize (axiom2 $~~A$ $~~B$) as H2.
    apply neg_neg_del2 in H2.
    specialize (conj_intro H1 H2) as H3.
    exact H3.
  }

  specialize (DeMorganDisj $~A$ $~B$) as H2.
  apply contrapos in H2.
  apply neg_neg_del2 in H2.
  apply contrapos in H1.
  specialize (trans H1 H2) as H3.
  exact H3.
Qed.

End Syntactic.
