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
f1 = F_neg (F_neg (F_atom "A"))

f2 :: Formula String
f2 = F_neg (F_impl (F_atom "A") (F_impl (F_atom "B") (F_atom "A")))

get_atoms :: Tree a -> [[Formula a]]
get_atoms (Node f lst) = case f of
   F_atom
