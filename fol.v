From Coq Require Import Lists.List.

Module FOL.
  #[projections(primitive)]
  Record language : Type :=
  {
    constant_symbols : Set ;
    func_symbols : Set ;
    pred_symbols : Set ;
    var_symbols : Set ;
    func_arity_table : func_symbols -> nat ;
    pred_arity_table : pred_symbols -> nat
  }.

  Section FOL_def.
    Context { lang : language }.

    Inductive term : Type :=
    | const : ConstSymbol -> term
    | var : VarSymbol -> term
    | func_app : forall (f : FuncSymbol),
        (* ensure the number of arguments matches arity *)
        list term ->
        term.

  Inductive formula : Type :=
  | pred_app : forall (p : PredSymbol),
      list term ->
      formula
  | f_not  : formula -> formula
  | f_conj  : formula -> formula -> formula
  | f_disj  : formula -> formula -> formula
  | f_imp  : formula -> formula -> formula
  | f_forall : VarSymbol -> formula -> formula
  | f_exists : VarSymbol -> formula -> formula.

End MyTheory.
End FOL.
Export FOL.
