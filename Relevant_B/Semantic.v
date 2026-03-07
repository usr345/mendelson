From Basis Require Import FSignature.
From Relevant_B Require Import Formula.
Import FormulaDef.
Import Relevant_B_Formula.
Local Open Scope formula_scope.

Module Semantic.
  Record Model {atom : Type} :=
  {
    worlds : Type;
    w0 : worlds;
    is_normal : worlds -> bool;
    R : worlds -> worlds -> worlds -> Prop;
    star : worlds -> worlds;
    star_involutive : forall w : worlds, star (star w) = w;
    v : atom -> worlds -> Prop;
  }.

  Fixpoint valid {atom : Type} (M: @Model atom) (f : formula) (w : worlds M) : Prop :=
    match f with
    | f_atom A => M.(v) A w
    | f_not f' => ~ (valid M f' (M.(star) w))
    | f_conj f g => (valid M f w) /\ (valid M g w)
    | f_disj f g => (valid M f w) \/ (valid M g w)
    | f_imp f g =>  match (M.(is_normal) w) with
                    | true => forall w' : M.(worlds), (valid M f w') -> (valid M g w')
                    | false => forall x y : M.(worlds), (M.(R) w x y) -> (valid M f x) -> (valid M g y)
                    end
    end.

End Semantic.