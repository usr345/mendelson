import Debug.Trace (trace)
import System.IO
import qualified Data.List

data Formula a =
  F_atom a
  | F_neg (Formula a)
  | F_impl (Formula a) (Formula a)
  | F_conj (Formula a) (Formula a)
  | F_disj (Formula a) (Formula a)

-- 0 - наивысший приоритет
priority :: Formula a -> Int
priority f =
  case f of
      F_atom _ -> 0
      F_neg _ -> 1
      F_conj _ _ -> 2
      F_disj _ _ -> 3
      F_impl _ _ -> 4

-- Вывести в строку формулу из 2-х подформул
show_formula2 :: (Show a) => Formula a -> Formula a -> String -> Int -> Int -> Int -> (Formula a -> String) -> String
show_formula2 f1 f2 op p1 p2 p3 show_fun =
  (if p2 < p1 then
      (show_fun f1)
    else
      "(" ++ (show_fun f1) ++ ")")
  ++ " " ++ op ++ " " ++
  if p3 < p1 then
    (show_fun f2)
  else
    "(" ++ (show_fun f2) ++ ")"

instance (Show a) => Show (Formula a) where
  show f =
    let p1 = priority f
    in
    case f of
      F_atom a -> show a
      F_neg f1 -> let p2 = priority f1 in
                    "¬" ++ if p2 <= p1 then
                             (show f1)
                           else
                             "(" ++ (show f1) ++ ")"
      F_impl f1 f2 -> let p2 = priority f1
                          p3 = priority f2
                      in
                        show_formula2 f1 f2 "->" p1 p2 p3 show
      F_conj f1 f2 -> let p2 = priority f1
                          p3 = priority f2
                      in
                        show_formula2 f1 f2 "/\\" p1 p2 p3 show

      F_disj f1 f2 -> let p2 = priority f1
                          p3 = priority f2
                      in
                        show_formula2 f1 f2 "\\/" p1 p2 p3 show

show_html :: Show a => Formula a -> String
show_html f =
    let p1 = priority f
    in
    case f of
      F_atom a -> show a
      F_neg f1 -> let p2 = priority f1 in
                    "&#172;" ++ if p2 <= p1 then
                             (show_html f1)
                           else
                             "(" ++ (show_html f1) ++ ")"
      F_impl f1 f2 -> let p2 = priority f1
                          p3 = priority f2
                      in
                        show_formula2 f1 f2 " &#8835; " p1 p2 p3 show_html
      F_conj f1 f2 -> let p2 = priority f1
                          p3 = priority f2
                      in
                        show_formula2 f1 f2 " &#8743; " p1 p2 p3 show_html

      F_disj f1 f2 -> let p2 = priority f1
                          p3 = priority f2
                      in
                        show_formula2 f1 f2 " &#8744; " p1 p2 p3 show_html


show_latex :: Show a => Formula a -> String
show_latex f =
  case f of
      F_atom a -> show a
      F_neg f1 -> "\\neg " ++ show_latex f1
      F_impl f1 f2 -> " " ++ (show_latex f1) ++ " \\supset " ++ (show_latex f2) ++ " "
      F_conj f1 f2 -> " " ++ (show_latex f1) ++ " \\land " ++ (show_latex f2) ++ " "
      F_disj f1 f2 -> " " ++ (show_latex f1) ++ " \\lor " ++ (show_latex f2) ++ " "


data Tree a =
  Closed_leaf (Formula a) (Formula a)
  | Open_leaf (Formula a)
  | One_child (Formula a) (Tree a)
  | Sequence (Formula a) (Tree a) (Tree a)
  | Fork (Formula a) (Tree a) (Tree a)
  deriving Show

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

process_inner :: Formula a -> [(a, Bool)] -> Tree a

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

newtype NoQuotes = NoQuotes String
instance Show NoQuotes where show (NoQuotes str) = str

atom_A :: NoQuotes
atom_A = NoQuotes "A"
atom_B = NoQuotes "B"
atom_C = NoQuotes "C"

f1 :: Formula NoQuotes
f1 = (F_neg (F_neg (F_atom atom_A)))

f2 :: Formula NoQuotes
f2 = F_neg (F_impl (F_atom atom_A) (F_impl (F_atom atom_B) (F_atom atom_C)))

f3_1 :: Formula NoQuotes
f3_1 = F_impl (F_atom atom_A) (F_impl (F_atom atom_B) (F_atom atom_C))

f3_2 :: Formula NoQuotes
f3_2 = (F_impl (F_impl (F_atom atom_A) (F_atom atom_B)) (F_impl (F_atom atom_A) (F_atom atom_C)))

f3 :: Formula NoQuotes
f3 = F_neg (F_impl f3_1 f3_2)

f4 :: Formula NoQuotes
f4 = F_neg (F_disj (F_atom atom_A) (F_neg (F_atom atom_A)))

f5_1 :: Formula NoQuotes
f5_1 = F_impl (F_impl (F_atom atom_A) (F_atom atom_B)) (F_atom atom_C)

f5_2 :: Formula NoQuotes
f5_2 = F_impl (F_impl (F_atom atom_B) (F_atom atom_A)) (F_atom atom_C)

f5 :: Formula NoQuotes
f5 = F_impl (F_disj f5_1 f5_2) (F_neg (F_atom atom_C))

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

show_dot :: Show a => Tree a -> String
show_dot tree = let (body, _) = show_dot_inner tree "" 1 Nothing
                in
                  "digraph {\n" ++ body ++ "}"
-- Узел дерева -> аккумулятор для результата -> текущий номер узла -> Maybe(номер родительского узла)
-- Возвращает (результирующая строка, номер последнего узла)
show_dot_inner :: Show a => Tree a -> String -> Int -> Maybe(String) -> (String, Int)
show_dot_inner tree accum num parent_num =
  let
    str_num = "N" ++ (show num)
    edge = (case parent_num of
        Nothing -> ""
        Just parent_node -> parent_node ++ " -> " ++ str_num ++ "\n")
  in
  case tree of
    Node f lst ->
      let
        node = str_num ++ "[label=\"" ++ (show_html f) ++ "\"]\n"
        accum1 = accum ++ node ++ edge
      in
        case lst of
          [] -> (accum1, num)
          [[subtree]] -> show_dot_inner subtree accum1 (num + 1) (Just str_num)
          [[subtree1, subtree2]] ->
            let
              (accum2, num2) = show_dot_inner subtree1 accum1 (num + 1) (Just str_num)
            in
              show_dot_inner subtree2 accum2 (num2 + 1) (Just $ "N" ++ (show num2))
          [[subtree1], [subtree2]] ->
            let
              (accum2, num2) = show_dot_inner subtree1 accum1 (num + 1) (Just str_num)
            in
              show_dot_inner subtree2 accum2 (num2 + 1) (Just str_num)
          _ -> (accum1, num)
-- let
--                   in

-- accum1
--     Node f [[subtree]] -> show_dot_inner subtree accum1

--     _ -> ""
main :: IO ()
main = do
    let filePath = "output.gv"
    let tree = process $ F_conj (F_neg (F_neg (F_neg (F_neg (F_atom atom_A))))) (F_conj (F_atom atom_B) (F_atom atom_C))
    let content = show_dot tree
    writeFile filePath content

    let filePath1 = "output1.gv"
    let tree1 = process $ F_disj (F_neg (F_neg (F_neg (F_neg (F_atom atom_A))))) (F_impl (F_impl (F_atom atom_B) (F_atom atom_A)) (F_atom atom_C))
    let content1 = show_dot tree1
    writeFile filePath1 content1
    putStrLn $ "Content successfully written to " ++ filePath1
