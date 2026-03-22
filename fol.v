From Basis Require Import EqDec.
From Coq Require Import Lists.List.
Import ListNotations.

Module FOL.
  #[projections(primitive)]
  Record language : Type :=
  {
    constant_symbols : Type;
    func_symbols : Type;
    pred_symbols : Type;
    var_symbols : Type;
    func_arity : func_symbols -> nat;
    pred_arity : pred_symbols -> nat
  }.

  Section FOL_def.
    Context { lang : language }.
    Context `{Heqd : EqDec (var_symbols lang)}.  (* assume decidable equality for variables *)

    Inductive term : Type :=
    | const : (constant_symbols lang) -> term
    | var : (var_symbols lang) -> term
    | func_app : forall (f : (func_symbols lang)),
        (* ensure the number of arguments matches arity *)
        list term -> term.

    Inductive wf_term : term -> Prop :=
    | wf_const : forall c : (constant_symbols lang), wf_term (const c)
    | wf_var : forall v : (var_symbols lang), wf_term (var v)
    | wf_func_app : forall (f : (func_symbols lang)) (args : list term),
        length args = func_arity lang f ->
        Forall wf_term args ->
        wf_term (func_app f args).

    Inductive formula : Type :=
    | pred_app : forall (p : pred_symbols lang),
        list term -> formula
    | f_not  : formula -> formula
    | f_conj  : formula -> formula -> formula
    | f_disj  : formula -> formula -> formula
    | f_imp  : formula -> formula -> formula
    | f_forall : (var_symbols lang) -> formula -> formula
    | f_exists : (var_symbols lang) -> formula -> formula.

    Inductive wf_formula : formula -> Prop :=
    | wf_pred_app : forall (p : (pred_symbols lang)) (args : list term),
        length args = pred_arity lang p ->
        Forall wf_term args ->
        wf_formula (pred_app p args)
    | wf_not  : forall f : formula, wf_formula f -> wf_formula (f_not f)
    | wf_conj  : forall f g : formula, wf_formula f -> wf_formula g -> wf_formula (f_conj f g)
    | wf_disj  : forall f g : formula, wf_formula f -> wf_formula g -> wf_formula (f_disj f g)
    | wf_imp  : forall f g : formula, wf_formula f -> wf_formula g -> wf_formula (f_imp f g)
    | wf_forall : forall (v : var_symbols lang) (f : formula), wf_formula f -> wf_formula (f_forall v f)
    | wf_exists : forall (v : var_symbols lang) (f : formula), wf_formula f -> wf_formula (f_exists v f).

    Fixpoint occurrences_in_term (t : term) (bound : list (var_symbols lang)) (v : var_symbols lang) : list bool :=
    match t with
    | const _ => []
    | var v' =>
        if eqb v v'
        then [existsb (fun b => eqb b v) bound]
        else []
    | func_app _ args =>
        let rec aux (lst : list term) : list bool :=
          match lst with
          | [] => []
          | t' :: ts => occurrences_in_term t' bound v ++ aux ts
          end
        in aux args
    end.

    Module Test1.
      Variant const3 : Type := a | b | c.
      Variant funcs2 : Type := f | g.
      Variant var3 : Type := x | y | z.

      Definition var3_arity (f1 : ) -> nat
      Definition language1 : Type :=
      { |
        constant_symbols : const3;
        func_symbols : funcs2;
        pred_symbols : False;
        var_symbols : var3;
        func_arity : func_symbols -> nat;
        pred_arity : fun _ => 0
      | }.
    End Test.

    Fixpoint occurs_in_term (t : term) (v : var_symbols lang) : bool :=
      match t with
      | const _ => false
      | var v' => eqb v v'
      | func_app _ args => existsb (fun t => occurs_in_term t v) args
      end.

    (* Main function: true if v has a bound occurrence in f under the current bound list *)
    Fixpoint bound_nth_occurrence (f : formula) (n : nat) (bound : list (var_symbols lang)) (v : var_symbols lang) : bool :=
      match f with
      | pred_app _ args =>
          (* v appears in some argument AND v is in the bound list *)
          existsb (fun t => occurs_in_term t v) args &&
          existsb (fun b => eqb b v) bound
      | f_not f1 => bound_occurrence f1 bound v
      | f_conj f1 f2 | f_disj f1 f2 | f_imp f1 f2 =>
          bound_occurrence f1 bound v || bound_occurrence f2 bound v
      | f_forall v' f1 =>
          if eqb v v' then
            bound_occurrence f1 (v' :: bound) v   (* v is bound by this quantifier *)
          else
            bound_occurrence f1 bound v
      | f_exists v' f1 =>
          if eqb v v' then
            bound_occurrence f1 (v' :: bound) v
          else
            bound_occurrence f1 bound v
      end.



   (* Wrapper: start with an empty bound list *)
    Definition is_bound (f : { f : formula | wf_formula f }) (v : var_symbols lang) : bool :=
      bound_occurrence (proj1_sig f) [] v.
  End FOL_def.
End FOL.

