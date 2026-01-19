From Mendelson Require Import FSignature.
From Mendelson Require Import K4.
Require Import Lists.List.
Import ListNotations.
Import Formula1.      (* To use the formula type *)

Variant atom2 : Set := P | Q.
Variant worlds2 : Set := Γ | Δ.

Lemma worlds2_inhabited : inhabited worlds2.
Proof.
  apply (inhabits Γ).
Qed.

Definition truth_relation1 : atom2 -> worlds2 -> bool -> Prop :=
  fun (a : atom2) (w : worlds2) (b : bool) =>
   match w, a, b with
    | Γ, P, true => True
    | Γ, P, false => True
    | Γ, Q, true => True
    | _, _, _ => False
    end.

Definition M1 : Model atom2 :=
  {|
    worlds := worlds2;
    worlds_inh := worlds2_inhabited;
    ρ := truth_relation1;
  |}.

Theorem T1 : FormulaTruth M1 (f_conj (f_atom P) (f_atom Q)) Γ true.
Proof.
  unfold FormulaTruth.
  split.
  - (* f_atom P *)
    simpl.
    exact I.
  - (* f_atom Q *)
    simpl.
    exact I.
Qed.

Theorem T2 : FormulaTruth M1 (f_conj (f_atom P) (f_atom Q)) Γ false.
Proof.
  unfold FormulaTruth.
  simpl.
  left.
  apply I.
Qed.

Theorem T3 : FormulaTruth M1 (f_imp (f_atom P) (f_atom Q)) Γ true.
Proof.
  unfold FormulaTruth.
  intros w H.
  destruct w.
  - simpl.
    exact I.
  - simpl.
    destruct H.
Qed.

Variant atom3 : Type := A | B | C.

Variant V4 := empty | false | true | both.

Definition neg4 (a : V4) : V4 :=
  match a with
  | empty => empty
  | false => true
  | true => false
  | both => both
  end.

Definition and4 (a b : V4) : V4 :=
  match a with
  | empty => match b with
             | both => false
             | false => false
             | _ => empty
             end
  | false => false
  | true => b
  | both => match b with
            | empty => false
            | false => false
            | _ => both
            end
  end.

Definition or4 (a b : V4) : V4 :=
  match a with
  | empty => match b with
            | true => true
            | both => true
            | _ => empty
            end
  | false => b
  | true => true
  | both => match b with
            | true => true
            | empty => true
            | _ => both
            end
  end.


(* K4 *)
(* Возвращает 1, если val присутствует во множестве истинностных значений формулы
   f. 0 в противном случае.
*)
Fixpoint eval {atom : Type} {worlds: Set} (w : worlds) (lst : list worlds) (non_empty: ~ ((length lst) = 0)) (f : formula) (ro : worlds -> atom -> V4): V4 :=
  match f with
  | f_atom A => (ro w A val)
  | f_not f' => neg4 (eval w f' ro val)
  | f_conj f1 f2 => and4 (eval w f1 ro val) (eval w f2 ro val)
  | f_disj f1 f2 => or4 (eval w f1 ro val) (eval w f2 ro val)
  | f_imp f1 f2 => (forall_worlds lst
  end
  (* Возвращает true, если для всех миров списка формула f вычисляется в val *)
  with forall_worlds (lst : list worlds) (f : formula) (ro : worlds -> atom -> bool -> bool) : Bool :=
