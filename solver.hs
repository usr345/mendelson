import Debug.Trace (trace)
import qualified Data.List

data Formula a =
  F_atom a
  | F_neg (Formula a)
  | F_impl (Formula a) (Formula a)
  | F_conj (Formula a) (Formula a)
  | F_disj (Formula a) (Formula a)
  deriving Show

data Tree a = Node (Formula a) [[Tree a]] deriving Show

process :: Formula a -> Tree a
process formula =
  Node formula (case formula of
    F_atom a -> []
    F_neg (F_atom a) -> []
    F_impl a b -> [[process (F_neg a)], [process b]]
    F_neg (F_impl a b) -> [[process a, process (F_neg b)]]
    F_conj a b -> [[process a, process b]]
    F_neg (F_conj a b) -> [[process (F_neg a)], [process (F_neg b)]]
    F_disj a b -> [[process a], [process b]]
    F_neg (F_disj a b) -> [[process (F_neg a), process (F_neg b)]]
    F_neg (F_neg a) -> [[process a]])

f1 :: Formula String
f1 = (F_neg (F_neg (F_atom "A")))

f2 :: Formula String
f2 = F_neg (F_impl (F_atom "A") (F_impl (F_atom "B") (F_atom "A")))

get_atoms :: Show a => Tree a -> [Formula a] -> [[Formula a]]
get_atoms (Node f lst) accum =
    let
        accum1 = (case f of
            F_atom a -> (F_atom a) : accum
            F_neg (F_atom a) -> (F_neg (F_atom a)) : accum
            _ -> accum)
    in
    case lst of
        [] -> [accum1]
        -- Дерево из 1-го узла
        [[subtree]] -> (get_atoms subtree accum1)
        [[subtree1, subtree2]] -> [Data.List.concat ((get_atoms subtree1 accum1) ++ (get_atoms subtree2 accum1))]
        [[subtree1], [subtree2]] -> [Data.List.concat (get_atoms subtree1 accum1), Data.List.concat (get_atoms subtree2 accum1)]
        --[[subtree1], [subtree2]] -> (get_atoms subtree1 accum1) ++ (get_atoms subtree2 accum1)
        _ -> [accum1]
