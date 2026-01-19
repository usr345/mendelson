Require Import List.
Import ListNotations.

Section STLC.

(* The set of atomic types *)
Parameter T : Type.

Inductive Ty : Type :=
  | Atom : T -> Ty
  | Arrow : Ty -> Ty -> Ty.

Infix "==>" := Arrow (at level 30, right associativity).

(* A context is a list of types. *)
Definition Context := list Ty.

(* Given a type X, the elements of Elem x lst are the positions in lst at which x appears. *)
Inductive Elem {X : Type} : X -> list X -> Type :=
  | Z : forall (x : X) lst, Elem x (x :: lst)
  | S : forall (x y : X) lst, Elem x lst -> Elem x (y :: lst).

Arguments Z {_} {_} {_}.
Arguments S {_} {_} {_} {_} (_).

Check (@Z nat 30 [40; 50; 30] : @Elem nat 30 [30; 40; 50; 30]). (* 30 appears in position Z. *)
Check (S (S (S Z)) : Elem 30 [30; 40; 50; 30]). (* 30 appears in position S (S (S Z)). *)

(* We use Elem to index variables in a context.
   That is, writing (x : Var A Ctx) should be read as "x is a variable (position) of
   type A in context Ctx." *)
Let Var := @Elem Ty.

(* There is a variable "S Z" of type "A ==> B" in context [C ; A ==> B ; B ; A ==> B]. *)
Check fun (A B C : Ty) =>
  (S Z : Var (A ==> B) [C ; A ==> B ; B ; A ==> B]).

(* There is a variable "S (S (S Z))" of type "A ==> B" in context [C ; A ==> B ; B ; A ==> B]. *)
(* Переменная 3 типа "A ==> B" в контексте [C ; A ==> B ; B ; A ==> B] *)
Check fun (A B C : Ty) =>
  (S (S (S Z)) : Var (A ==> B) [C ; A ==> B ; B ; A ==> B]).

(* Terms of a given type in the given context. *)
Inductive Tm : Context -> Ty -> Type :=
  (* Переменная типа A в контексте Ctx является термом типа A в контексте Ctx *)
  | var : forall (Ctx : Context) (A : Ty), Var A Ctx -> Tm Ctx A
  | app : forall (Ctx : Context) (A B : Ty), Tm Ctx (Arrow A B) -> Tm Ctx A -> Tm Ctx B
  | abs : forall (Ctx : Context) (A B : Ty), Tm (A :: Ctx) B -> Tm Ctx (Arrow A B).

Check var.
Arguments var {_} {_}.
Arguments app {_} {_} {_}.
Arguments abs {_} (_) {_}.

(* Example terms *)
Check abs.
(* Identity on a given type A in an arbitrary context. *)
Definition term_id {Ctx} (A : Ty) : Tm Ctx (A ==> A) :=
  abs A (var Z).

Print term_id.
(* The Church numeral 0: λ (f : A → A) . λ (x : A) . x *)
Definition zero {Ctx} (A : Ty) : Tm Ctx ((A ==> A) ==> A ==> A) :=
  abs
    (Arrow A A) (* 1 : A -> A *)
    (abs A (* 0 : A *)
      (var Z)).

(* The Church numeral 1: λ (f : A → A) . λ (x : A) . (f x) *)
Definition one {Ctx} (A : Ty) :=
  abs
    (Arrow A A) (* это f *)
    (abs A
      (app (var (S Z)) (var Z)))
  : Tm Ctx ((A ==> A) ==> A ==> A).


(* The Church numeral 2: λ (f : A → A) . λ (x : A) . f (f x) *)
Definition two {Ctx} (A : Ty) :=
  abs
    (Arrow A A)
    (abs A
      (app (var (S Z)) (app (var (S Z)) (var Z))))
  : Tm Ctx ((A ==> A) ==> (A ==> A)).

Definition succ {Ctx : Context} (A : Ty) : 
  Tm Ctx (((A ==> A) ==> (A ==> A)) ==> ((A ==> A) ==> (A ==> A))) :=
  abs (Arrow (Arrow A A) (Arrow A A)) (* 2 *)
        (abs (Arrow A A) (* 1 *)
          (abs A
            (app 
              (var (S Z)) 
              (app (app (var (S (S Z))) (var (S Z))) (var Z))))).

Definition plus {Ctx : Context} (A : Ty) : 
  Tm Ctx (((A ==> A) ==> (A ==> A)) ==> ((A ==> A) ==> (A ==> A))) :=
  abs (Arrow (Arrow A A) (Arrow A A)) (* 2 *)
        (abs (Arrow A A) (* 1 *)
          (abs A
            (app 
              (var (S Z)) 
              (app (app (var (S (S Z))) (var (S Z))) (var Z))))).

End STLC.