Require Import Setoid.
From Mendelson Require Import MSets.
Require Import Lists.List.
Import ListNotations.

(* Синтаксис формулы K4 *)
Inductive formula {atom : Type} : Type :=
| f_atom : atom -> formula
| f_not  : formula -> formula
| f_conj  : formula -> formula -> formula
| f_disj  : formula -> formula -> formula
| f_imp  : formula -> formula -> formula.

Definition TruthRelation {atom : Type} {worlds : Set} : Type := 
              atom -> worlds -> bool -> Prop.

Inductive FormulaTruth {atom : Type} {worlds : Set} (ρ : @TruthRelation atom worlds): 
            (@formula atom) -> worlds -> bool -> Prop :=
| ft_atom : forall (A : atom) (w : worlds) (b : bool), ρ A w b -> FormulaTruth ρ (f_atom A) w b
| ft_neg : forall (f : @formula atom) (w : worlds) (b : bool), FormulaTruth ρ f w (negb b) -> FormulaTruth ρ (f_not f) w b
| ft_conj_true : forall (f g : @formula atom) (w : worlds), 
    FormulaTruth ρ f w true -> 
    FormulaTruth ρ g w true -> 
    FormulaTruth ρ (f_conj f g) w true
| ft_conj_false1 : forall (f g : @formula atom) (w : worlds), 
    FormulaTruth ρ f w false -> 
    FormulaTruth ρ (f_conj f g) w false
| ft_conj_false2 : forall (f g : @formula atom) (w : worlds), 
    FormulaTruth ρ g w false -> 
    FormulaTruth ρ (f_conj f g) w false
| ft_disj_true1 : forall (f g : @formula atom) (w : worlds), 
    FormulaTruth ρ f w true -> 
    FormulaTruth ρ (f_disj f g) w true
| ft_disj_true2 : forall (f g : @formula atom) (w : worlds), 
    FormulaTruth ρ g w true -> 
    FormulaTruth ρ (f_disj f g) w false
| ft_disj_false : forall (f g : @formula atom) (w : worlds), 
    FormulaTruth ρ f w false -> 
    FormulaTruth ρ g w false -> 
    FormulaTruth ρ (f_disj f g) w false
| ft_impl_true : forall (f g : @formula atom) (w : worlds), 
    (forall w : worlds, FormulaTruth ρ f w true /\ FormulaTruth ρ g w true) ->
    FormulaTruth ρ (f_imp f g) w true
| ft_impl_false : forall (f g : @formula atom) (w : worlds), 
    (exists w : worlds, FormulaTruth ρ f w true /\ FormulaTruth ρ g w false) ->
    FormulaTruth ρ (f_imp f g) w false.

Variant atom2 : Set := P | Q.
Variant worlds2 : Set := Γ | Δ.

Definition truth_relation1 : @TruthRelation atom2 worlds2 := 
  fun (a : atom2) (w : worlds2) (b : bool) =>
   match w, a, b with
    | Γ, P, true => True
    | Γ, P, false => True
    | Γ, Q, true => True
    | Γ, Q, false => True
    | _, _, _ => False
    end.

Theorem T1 : FormulaTruth truth_relation1 (f_conj (f_atom P) (f_atom Q)) Γ true.
Proof.
  apply ft_conj_true.
  - apply ft_atom.
    unfold truth_relation1.
    apply I.
  - apply ft_atom.
    unfold truth_relation1.
    apply I.
Qed.

Theorem T2 : FormulaTruth truth_relation1 (f_conj (f_atom P) (f_atom Q)) Γ false.
Proof.
  apply ft_conj_false1.
  apply ft_atom.
  unfold truth_relation1.
  apply I.
Qed.

Theorem T3 : FormulaTruth truth_relation1 (f_imp (f_atom P) (f_atom Q)) Γ false.
Proof.
  apply ft_impl_false.
  exists Γ.
  split.
  - apply ft_atom.
    unfold truth_relation1.
    apply I.
  - apply ft_atom.
    unfold truth_relation1.
    apply I.
Qed.

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
  

