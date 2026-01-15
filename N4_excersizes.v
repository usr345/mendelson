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

  Theorem T1_imply_self_neg {atom : Type} : ~ forall A : @formula atom3, |= $A -> A$.
  Proof.
    unfold not.
    intro H.
    specialize (H (f_atom P)).

    (* Конструируем контрмодель *)
    pose (
        ρ1 :=
          fun (a : atom3) (w: worlds1) (val : bool) =>
            match w, a, val with
            | _, _, _ => False
            end
      ).

    pose (M1 := {|
                 worlds := worlds1;
                 worlds_inh := worlds1_inhabited;
                 ρ := ρ1;
                 is_normal := fun (w : worlds1) =>
                                match w with
                                | _ => false
                                end;
                 ρ_imp := fun (f1 f2 : @formula atom3) (w: worlds1) (val : bool) =>
                            match f1, f2, w, val with
                            | _, _, _, _ => False
                            end
               |}).

    unfold valid in H.
    specialize (H M1 Γ).
    unfold implication in H.
    cbn [FormulaTruth] in H.
    unfold M1 at 1 in H.
    cbn [is_normal] in H.
    cbn [ρ_imp] in H.
    exact H.
  Qed.

End N4_excersizes.
