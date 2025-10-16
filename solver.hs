import Debug.Trace (trace)
import qualified Data.List

data Formula a =
  F_atom a
  | F_neg (Formula a)
  | F_impl (Formula a) (Formula a)
  | F_conj (Formula a) (Formula a)
  | F_disj (Formula a) (Formula a)

instance (Show a) => Show (Formula a) where
  show f =
    case f of
      F_atom a -> show a
      F_neg f1 -> "¬" ++ show f1
      F_impl f1 f2 -> "(" ++ (show f1) ++ " -> " ++ (show f2) ++ ") "
      F_conj f1 f2 -> "(" ++ (show f1) ++ " /\\ " ++ (show f2) ++ ") "
      F_disj f1 f2 -> "(" ++ (show f1) ++ " \\/ " ++ (show f2) ++ ") "


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

merge_lists :: [[a]] -> [[a]] -> [[a]]
merge_lists lst1 lst2 = (++) <$> lst1 <*> lst2

has_contradiction_inner :: Eq a => [(a, Bool)] -> (a, Bool) -> Bool
has_contradiction_inner lst a =
  let (x, y) = a
  in
    case lst of
    [] -> False
    (b, mark):hs -> if x == b
                    then if mark /= y then
                           True
                         else
                           has_contradiction_inner hs a
                    else
                           has_contradiction_inner hs a


has_contradiction :: Eq a => [(a, Bool)] -> Bool
has_contradiction lst =
  case lst of
    [] -> False
    h:hs -> if (has_contradiction_inner hs h) == True then
              True
            else
              has_contradiction hs

all_lists_contradiction :: Eq a => [[(a, Bool)]] -> Maybe([(a, Bool)])
all_lists_contradiction lst =
  case lst of
    [] -> Nothing
    h:hs -> if (has_contradiction h) == True then
              all_lists_contradiction hs
            else
              Just h

-- Если формула тавтология - вернет Nothing или вернет контрпример
-- при котором формула ложна
formula_is_tautology :: Eq a => Formula a -> Maybe([(a, Bool)])
formula_is_tautology f =
  let
    atoms = get_atoms (process $ F_neg f) []
  in
    all_lists_contradiction atoms

f1 :: Formula String
f1 = (F_neg (F_neg (F_atom "A")))

f2 :: Formula String
f2 = F_neg (F_impl (F_atom "A") (F_impl (F_atom "B") (F_atom "A")))

f3_1 :: Formula String
f3_1 = F_impl (F_atom "A") (F_impl (F_atom "B") (F_atom "C"))

f3_2 :: Formula String
f3_2 = (F_impl (F_impl (F_atom "A") (F_atom "B")) (F_impl (F_atom "A") (F_atom "C")))

f3 :: Formula String
f3 = F_neg (F_impl f3_1 f3_2)

f4 :: Formula String
f4 = F_neg (F_disj (F_atom "A") (F_neg (F_atom "A")))

f5_1 :: Formula String
f5_1 = F_impl (F_impl (F_atom "A") (F_atom "B")) (F_atom "C")

f5_2 :: Formula String
f5_2 = F_impl (F_impl (F_atom "B") (F_atom "A")) (F_atom "C")

f5 :: Formula String
f5 = F_impl (F_disj f5_1 f5_2) (F_atom "C")

-- get_atoms (process f2) []

get_atoms :: Tree a -> [(a, Bool)] -> [[(a, Bool)]]
-- get_atoms (Node f lst) accum =
--     let
--         accum1 = (case f of
--             F_atom a -> (F_atom a) : accum
--             F_neg (F_atom a) -> (F_neg (F_atom a)) : accum
--             _ -> accum)
--     in
--     case lst of
--         [] -> [accum1]
--         -- Дерево из 1-го узла
--         [[subtree]] -> trace ("subtree = " ++ show (subtree)) (get_atoms subtree accum1)
--         [[subtree1, subtree2]] -> trace ("subtree1 = " ++ show (subtree1) ++ "\nsubtree2 = " ++ show (subtree2)) [(Data.List.concat $ get_atoms subtree1 accum1) ++ (Data.List.concat $ get_atoms subtree2 accum1)]
--         [[subtree1], [subtree2]] -> trace ("subtree1' = " ++ show (subtree1) ++ "\nsubtree2' = " ++ show (subtree2) ) [Data.List.concat (get_atoms subtree1 accum1), Data.List.concat (get_atoms subtree2 accum1)]
--         _ -> trace ("??? = " ++ show (lst)) [accum1]

get_atoms (Node f lst) accum =
    let
        accum1 = (case f of
            F_atom a -> (a, True) : accum
            F_neg (F_atom a) -> (a, False) : accum
            _ -> accum)
    in
    case lst of
        [] -> [accum1]
        -- Дерево из 1-го узла
        [[subtree]] -> get_atoms subtree accum1
        [[subtree1, subtree2]] -> merge_lists (get_atoms subtree1 accum1) (get_atoms subtree2 accum1)
        [[subtree1], [subtree2]] -> (get_atoms subtree1 accum1) ++ (get_atoms subtree2 accum1)
        _ -> [accum1]
