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

  Variant worlds1 : Set := Γ.

  Lemma worlds1_inhabited : inhabited worlds1.
  Proof.
    apply (inhabits Γ).
  Qed.

  Theorem T1_imply_self {atom : Type} : forall A : @formula atom3, |= $A -> A$.
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


End N4_excersizes.
