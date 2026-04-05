From Basis Require Import EqDec.
From Coq Require Import Lists.List.
From Coq Require Import Fin.
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

  Inductive term (lang : language) : Type :=
  | t_const : constant_symbols lang -> term lang
  | t_var : var_symbols lang -> term lang
  | t_func_app : func_symbols lang -> list (term lang) -> term lang.

  Arguments t_const {lang} _.
  Arguments t_var {lang} _.
  Arguments t_func_app {lang} _ _.

  Inductive wf_term {lang : language} : term lang -> Prop :=
    | wf_const : forall c : (constant_symbols lang), wf_term (t_const c)
    | wf_var : forall v : (var_symbols lang), wf_term (t_var v)
    | wf_func_app : forall (f : (func_symbols lang)) (args : list (term lang)),
        length args = func_arity lang f ->
        Forall (@wf_term lang) args ->
        wf_term (t_func_app f args).

  Fixpoint vars_occurence_term {lang : language} (t : term lang) : list (var_symbols lang) :=
    match t with
    | t_const _ => []
    | t_var v => [v]
    | t_func_app _ lst => fold_right (fun t accum => (vars_occurence_term t) ++ accum) [] lst
    end.

  Inductive formula {lang : language} : Type :=
    | pred_app : forall (p : pred_symbols lang),
        list (term lang) -> formula
    | f_not  : formula -> formula
    | f_conj  : formula -> formula -> formula
    | f_disj  : formula -> formula -> formula
    | f_imp  : formula -> formula -> formula
    | f_forall : (var_symbols lang) -> formula -> formula
    | f_exists : (var_symbols lang) -> formula -> formula.

  Theorem var_symbols_dec (lang : language) `{Heqd : EqDec (var_symbols lang)} : 
    forall x y : var_symbols lang, {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct (eqb x y) eqn:Heq.
    - rewrite eqb_eq in Heq.
      exact (left Heq).
    - apply right.
      unfold not.
      intro Heq1.
      rewrite <-eqb_eq in Heq1.
      rewrite Heq1 in Heq.
      discriminate Heq.
  Qed.

  Fixpoint free_vars_formula {lang : language} `{Heqd : EqDec (var_symbols lang)} (f : @formula lang) : list (var_symbols lang) :=
    match f with
    | pred_app _ arg => fold_right (fun t accum => (vars_occurence_term t) ++ accum) [] arg
    | f_not f' => free_vars_formula f'
    | f_conj f1 f2 => (free_vars_formula f1) ++ (free_vars_formula f2)
    | f_disj f1 f2 => (free_vars_formula f1) ++ (free_vars_formula f2)
    | f_imp f1 f2 => (free_vars_formula f1) ++ (free_vars_formula f2)
    | f_forall x f' => remove (var_symbols_dec lang) x (free_vars_formula f')
    | f_exists x f' => remove (var_symbols_dec lang) x (free_vars_formula f')
    end.

  (* x имеет свободное вхождение в формуле f *)
  Fixpoint free_var_in_formula {lang : language} (x : var_symbols lang) (f : @formula lang) : Prop :=
    match f with
    | pred_app _ args =>
        exists t, In t args /\ In x (vars_occurence_term t)
    | f_not f' => free_var_in_formula x f'
    | f_conj f1 f2 =>
        free_var_in_formula x f1 \/ free_var_in_formula x f2
    | f_disj f1 f2 =>
        free_var_in_formula x f1 \/ free_var_in_formula x f2
    | f_imp f1 f2 =>
        free_var_in_formula x f1 \/ free_var_in_formula x f2
    | f_forall y f' =>
        x <> y /\ free_var_in_formula x f'
    | f_exists y f' =>
        x <> y /\ free_var_in_formula x f'
    end.

  Lemma pred_app_list_prop {lang : language} `{Heqd : EqDec (var_symbols lang)} (x : var_symbols lang) (p : pred_symbols lang) (args : list (term lang)):
      In x (free_vars_formula (pred_app p args)) ->
      free_var_in_formula x (pred_app p args).
  Proof.
    intro H.
    simpl.
    simpl in H.
    induction args as [|a args IH]; simpl.
    - destruct H.
    - apply in_app_or in H as [H | H].
      + exists a.
        split.
        * left.
          reflexivity.
        * exact H.
      + apply IH in H.
        destruct H as [t [H1 H2]].
        exists t.
        split.
        * right.
          exact H1.
        * exact H2.
  Qed.

  Lemma pred_app_prop_list {lang : language} `{Heqd : EqDec (var_symbols lang)} (x : var_symbols lang) (p : pred_symbols lang) (args : list (term lang)):
      free_var_in_formula x (pred_app p args) ->
      In x (free_vars_formula (pred_app p args)).
  Proof.
    intro H.
    simpl.
    simpl in H.
    induction args as [|a args IH]; simpl.
    - destruct H as [t [H1 _]].
      simpl in H1.
      exact H1.
    - apply in_or_app.
      destruct H as [t [H1 H2]].
      simpl in H1.
      destruct H1 as [H1 | H1].
      + left.
        rewrite <-H1 in H2.
        exact H2.
      + right.
        apply IH.
        exists t.
        exact (conj H1 H2).
  Qed.

  Theorem free_vars_formula_correct {lang : language} `{Heqd : EqDec (var_symbols lang)} (f : @formula lang) (x : var_symbols lang):
      In x (free_vars_formula f) <-> free_var_in_formula x f.
  Proof.
    split ; intro H.
    - induction f as [
        p args
      | f' IH
      | f1 IHf1 f2 IHf2
      | f1 IHf1 f2 IHf2
      | f1 IHf1 f2 IHf2
      | y f' IH
      | y f' IH
      ].
      + exact (pred_app_list_prop x p args H).
      + simpl in H.
        specialize (IH H).
        exact IH.
      + simpl in H.
        simpl.
        apply in_app_or in H.
        destruct H as [H | H].
        * specialize (IHf1 H).
          left.
          exact IHf1.
        * specialize (IHf2 H).
          right.
          exact IHf2.
      + simpl in H.
        simpl.
        apply in_app_or in H.
        destruct H as [H | H].
        * specialize (IHf1 H).
          left.
          exact IHf1.
        * specialize (IHf2 H).
          right.
          exact IHf2.
      + simpl in H.
        simpl.
        apply in_app_or in H.
        destruct H as [H | H].
        * specialize (IHf1 H).
          left.
          exact IHf1.
        * specialize (IHf2 H).
          right.
          exact IHf2.
      + simpl in H.
        simpl.
        apply in_remove in H.
        destruct H as [H1 H2].
        specialize (IH H1).
        exact (conj H2 IH).
      + simpl in H.
        simpl.
        apply in_remove in H.
        destruct H as [H1 H2].
        specialize (IH H1).
        exact (conj H2 IH).
    - induction f as [
        p args
      | f' IH
      | f1 IHf1 f2 IHf2
      | f1 IHf1 f2 IHf2
      | f1 IHf1 f2 IHf2
      | y f' IH
      | y f' IH
      ].
      + exact (pred_app_prop_list x p args H).
      + simpl in H.
        specialize (IH H).
        exact IH.
      + simpl in H.
        simpl.
        apply in_or_app.
        destruct H as [H | H].
        * specialize (IHf1 H).
          left.
          exact IHf1.
        * specialize (IHf2 H).
          right.
          exact IHf2.
      + simpl in H.
        simpl.
        apply in_or_app.
        destruct H as [H | H].
        * specialize (IHf1 H).
          left.
          exact IHf1.
        * specialize (IHf2 H).
          right.
          exact IHf2.
      + simpl in H.
        simpl.
        apply in_or_app.
        destruct H as [H | H].
        * specialize (IHf1 H).
          left.
          exact IHf1.
        * specialize (IHf2 H).
          right.
          exact IHf2.
      + simpl in H.
        simpl.
        destruct H as [H1 H2].
        specialize (IH H2).
        specialize (in_in_remove (var_symbols_dec lang) (free_vars_formula f') H1 IH) as H3.
        exact H3.
      + simpl in H.
        simpl.
        destruct H as [H1 H2].
        specialize (IH H2).
        specialize (in_in_remove (var_symbols_dec lang) (free_vars_formula f') H1 IH) as H3.
        exact H3.
  Qed.

  Inductive wf_formula {lang : language} : @formula lang -> Prop :=
    | wf_pred_app : forall (p : pred_symbols lang) (args : list (term lang)),
        length args = pred_arity lang p ->
        Forall (@wf_term lang) args ->
        wf_formula (pred_app p args)
    | wf_not  : forall f : @formula lang, 
        wf_formula f -> wf_formula (f_not f)
    | wf_conj  : forall f g : @formula lang, 
        wf_formula f -> wf_formula g -> wf_formula (f_conj f g)
    | wf_disj  : forall f g : @formula lang, 
        wf_formula f -> wf_formula g -> wf_formula (f_disj f g)
    | wf_imp   : forall f g : @formula lang, 
        wf_formula f -> wf_formula g -> wf_formula (f_imp f g)
    | wf_forall : forall (x : var_symbols lang) (f : @formula lang), 
        wf_formula f -> wf_formula (f_forall x f)
    | wf_exists : forall (x : var_symbols lang) (f : @formula lang), 
        wf_formula f -> wf_formula (f_exists x f).

  Fixpoint substitute {lang : language} `{Heqd : EqDec (var_symbols lang)} (t : term lang) (x : var_symbols lang) (t' : term lang) : term lang :=
      match t with
      | t_const a => t_const a
      | t_var y => if (eqb y x) then t' else t
      | t_func_app f args => t_func_app f (map (fun y => substitute y x t') args)
      end.

  Fixpoint substitute_f {lang : language} `{Heqd : EqDec (var_symbols lang)} (f : @formula lang) (v : var_symbols lang) (t' : term lang) : @formula lang :=
      match f with
      | pred_app p args => pred_app p (map (fun x => substitute x v t') args)
      | f_not f' => f_not (substitute_f f' v t')
      | f_conj f1 f2 => f_conj (substitute_f f1 v t') (substitute_f f2 v t')
      | f_disj f1 f2 => f_disj (substitute_f f1 v t') (substitute_f f2 v t')
      | f_imp f1 f2 => f_imp (substitute_f f1 v t') (substitute_f f2 v t')
      | f_forall x f' => if (eqb v x) then f else f_forall x (substitute_f f' v t')
      | f_exists x f' => if (eqb v x) then f else f_exists x (substitute_f f' v t')
      end.

Theorem substitute_wf_term
  {lang : language} `{Heqd : EqDec (var_symbols lang)}
  (t t' : term lang) (x : var_symbols lang) :
  wf_term t ->
  wf_term t' ->
  wf_term (substitute t x t').
Proof.
  revert t' x.
  induction t using term_ind.
  - intros t' x Ht' Hwf.
    simpl.
    apply wf_const.
  - (* t_var *)
    intros t' x Ht' Hwf.
    destruct (eqb v x) eqn:Heq.
    + apply eqb_eq in Heq. 
      rewrite <-Heq.
      simpl.
      rewrite eqb_reflexive.
      exact Hwf.
    + simpl.
      rewrite Heq.
      apply wf_var.
  - (* t_func_app *)
    intros t x Hwf Ht.
    inversion Hwf; subst.
    simpl.
    apply wf_func_app.
    + rewrite map_length. 
      exact H1.
    + induction l as [|a l'].
      * apply Forall_nil.
      * apply Forall_cons.
        ** inversion H2; subst.

      * intros Ht Hwf H1.
        apply Forall_nil.
      * intros Ht Hwf H1.
        apply Forall_cons.
        -- simpl in Hwf.

           [left; reflexivity | exact Ht' | exact Ha].
        -- (* tail *)
           exact IHargs.
Qed.

  Theorem substitute_wf_term
    {lang : language} `{Heqd : EqDec (var_symbols lang)}
    (t t' : term lang) (v : var_symbols lang) :
    wf_term t ->
    wf_term t' ->
    wf_term (substitute t v t').
  Proof.
    intros Hwf.
    revert t' v.
    induction Hwf as
      [c
      |x
      |f args Hlen Hargs IHargs]; intros t' v Ht'; simpl.
    - constructor.
    - destruct (eqb x v) eqn:Heq.
      + apply eqb_eq in Heq. subst. exact Ht'.
      + constructor.
    - constructor.
      + rewrite map_length. exact Hlen.
      + induction IHargs as [|a args Ha Hrest IHrest]; simpl.
        * constructor.
        * constructor.
          -- apply Ha. exact Ht'.
          -- exact IHrest.
  Qed.

  Theorem substitute_wf_term {lang : language} `{Heqd : EqDec (var_symbols lang)} (t t' : term lang) (v : var_symbols lang):
      wf_term t ->
      wf_term t' ->
      wf_term (substitute t v t').
  Proof.
    intros Ht Ht'.
    induction t as [c | x | f args].
    - simpl.
      apply wf_const.
    - simpl.
      destruct (eqb x v) eqn:Heq.
      + exact Ht'.
      + apply wf_var.
    - induction args as [|x args IH].
      + simpl.
        exact Ht.
      + inversion Ht ; subst.
        simpl in H1.
        simpl.
        apply wf_func_app.
        * simpl.
          rewrite <-H1.
          rewrite map_length.
          reflexivity.
        * apply Forall_cons.
          ** 


    Definition well_substitute 

  Module Test1.
    Variant const : Type := a | b | c.
    Variant funcs : Type := f | g.
    Variant pred : Type := P | Q | R.
    Variant var : Type := x | y | z.

    Definition funcs_arity1 (f : funcs): nat :=
    match f with
    | f => 3
    | g => 2
    end.

    Definition pred_arity1 (p : pred): nat :=
    match p with
    | P => 1
    | Q => 2
    | R => 3
    end.

    Definition test_language : language :=
    {|
      constant_symbols := const;
      func_symbols := funcs;
      pred_symbols := pred;
      var_symbols := var;
      func_arity := funcs_arity1;
      pred_arity := pred_arity1
    |}.

    Definition vars_eqb (v1 v2 : var) : bool :=
    match v1, v2 with
    | x, x => true
    | y, y => true
    | z, z => true
    | _, _ => false
    end.

    Theorem vars_eqb_eq : forall x y : var, (vars_eqb x y) = true <-> x = y.
    Proof.
      intros x0 y0.
      split ; intro H.
      - destruct x0, y0 ; simpl in H ; try discriminate H ; reflexivity.
      - rewrite H.
        destruct x0, y0 ; simpl ; try discriminate H ; reflexivity.
    Qed.

    Instance EqDec_var : EqDec var :=
    {
      eqb := vars_eqb;
      eqb_eq := vars_eqb_eq
    }.

    #[local] Notation termL := (FOL.term test_language).

    #[local] Notation "'const_' c" := (FOL.t_const (lang := test_language) c) (at level 50).
    #[local] Notation "'var_' v" := (FOL.t_var (lang := test_language) v) (at level 50).
    #[local] Notation "'app_' f ',' args" := (FOL.t_func_app (lang := test_language) f args) (at level 50).

    Definition term1 : FOL.term test_language :=
      app_ g , [const_ a; app_ f , [var_ x; var_ y; const_ b] ].

    Example test1 : 
        vars_occurence_term term1 = [x; y].
    Proof.
      cbn.
      reflexivity.
    Qed.

    Compute (substitute term1 x (const_ c)).
  End Test1.

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
End FOL.

