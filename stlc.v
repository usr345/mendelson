Require Import List.
Import ListNotations.
Require Import EqDec.

(* T - множество констант для атомарных типов *)
Inductive ST_type (T : Type) : Type :=
| ST_atom : T -> ST_type T
| ST_arrow : ST_type T -> ST_type T -> ST_type T.

(* V - множество переменных *)
Inductive ST_term (V : Type) `{EqDec V} : Type :=
| T_var : V -> ST_term V
| T_app : ST_term V -> ST_term V -> ST_term V
| T_abs (T : Type) : V -> T -> ST_term V -> ST_term V.

Definition context (V T : Type) `{EqDec V} := list (V * ST_type T).

(* Поиск типа для переменной v в контексте *)
Fixpoint lookup {V T : Type} `{EqDec V} (v : V) (ctx : context V T) {struct ctx} : option(ST_type T) :=
  match ctx with
  | nil => None
  | (v1, v1_type)::tl => if (eqb v v1) then (Some v1_type) else lookup v tl
  end.

(* When lookup returns Some t, the variable indeed has type t in the context. *)
Theorem lookup_found {V T : Type} `{Heq: EqDec V} (v : V) (type : ST_type T) (ctx : context V T) : lookup v ctx = (Some type) <-> In (v, type) ctx.
Proof.
  split.
  - intro H.
    induction ctx as [|(v1, t1) tl IH].
    + simpl in H.
      discriminate H.
    + simpl in H.
      simpl.
      destruct (eqb v v1) as [TRUE | FALSE] eqn:Heq1.
      * injection H as H1.
        left.
        rewrite H1.
        rewrite eqb_eq in Heq1.
        rewrite Heq1.
        reflexivity.
      * right.
        apply IH.
        apply H.
  - intro H.
    induction ctx as [|(v1, t1) tl IH].
    + simpl in H.
      destruct H.
    + simpl.
      simpl in H.
      destruct H.
      * rewrite pair_equal_spec in H.
        destruct H as [H1 H2].
        rewrite H1.
        rewrite eqb_reflexive.
        rewrite H2.
        reflexivity.
      * specialize (IH H).
        destruct (eqb v v1) eqn:Heq1.
        ** (* v != v1 h *)
          admit.
        ** apply IH.



Theorem lookup_not_found {V T : Type} `{EqDec V} (v : V) (type : ST_type T) (ctx : context V T) : lookup v ctx = None <-> ~In (v, type) ctx.
(* When lookup returns None, the variable is not present in the context. *)
