module Solver where

-- import Debug.Trace (trace)
-- import qualified Data.List
import Formula
import Queue

data Tree a =
  Closed_leaf (Formula a) (Bot a)
  | Open_leaf (Formula a)
  | One_child (Formula a) (Tree a)
  | Fork (Formula a) (Tree a) (Tree a)
  deriving Show

has_contradiction_inner :: Eq a => [(a, Bool)] -> (a, Bool) -> Maybe(a)
has_contradiction_inner lst a =
  let (x, y) = a
  in
    case lst of
    [] -> Nothing
    (b, mark):hs -> if x == b
                    then if mark /= y then
                           Just b
                         else
                           has_contradiction_inner hs a
                    else
                           has_contradiction_inner hs a

has_contradiction :: Eq a => [(a, Bool)] -> Maybe(a)
has_contradiction lst =
  case lst of
    [] -> Nothing
    h:hs -> case (has_contradiction_inner hs h) of
      Nothing -> has_contradiction hs
      Just a -> Just a

data Path a =
  P_atom a Bool
  | P_one (Formula a)
  | P_sequence (Formula a) (Formula a)
  | P_fork (Formula a) (Formula a)

analyze :: Formula a -> Path a
analyze f =
  case f of
    F_atom a -> P_atom a True
    F_neg (F_atom a) -> P_atom a False
    F_neg (F_neg f') -> P_one f'
    F_conj f1 f2 -> P_sequence f1 f2
    F_neg (F_conj f1 f2) -> P_fork (F_neg f1) (F_neg f2)
    F_disj f1 f2 -> P_fork f1 f2
    F_neg (F_disj f1 f2) -> P_sequence (F_neg f1) (F_neg f2)
    F_impl f1 f2 -> P_fork (F_neg f1) f2
    F_neg (F_impl f1 f2) -> P_sequence f1 (F_neg f2)

process_inner :: (Show a, Eq a) => Formula a -> [(a, Bool)] -> Queue (Formula a) -> Queue (Formula a, Formula a) -> Tree a
process_inner f atoms seq_queue fork_queue =
  let result = analyze f in
    case result of
      P_atom a signum ->
        let
          atoms' = (a, signum):atoms
        in
          case (has_contradiction atoms') of
            -- найдено противоречие - больше ничего не делаем
            Just b -> Closed_leaf f (Bot (F_atom b))
            Nothing -> case (dequeue seq_queue) of
              -- seq очередь не пуста
              Just (f', seq_queue') -> One_child f (process_inner f' atoms' seq_queue' fork_queue)
              -- seq очередь пуста
              Nothing -> case (dequeue fork_queue) of
                -- fork очередь не пуста
                Just ((f1, f2), fork_queue') ->
                  let
                    tree1 = (process_inner f1 atoms' seq_queue fork_queue')
                    tree2 = (process_inner f2 atoms' seq_queue fork_queue')
                  in
                    Fork f tree1 tree2
                -- fork очередь пуста
                Nothing -> Open_leaf f

      P_one f' -> One_child f (process_inner f' atoms seq_queue fork_queue)
      P_sequence f1 f2 -> let seq_queue' = enqueue f2 seq_queue in
        One_child f (process_inner f1 atoms seq_queue' fork_queue)
      P_fork f1 f2 -> case (dequeue seq_queue) of
          Nothing -> Fork f (process_inner f1 atoms seq_queue fork_queue) (process_inner f2 atoms seq_queue fork_queue)
          Just (f', seq_queue') -> let fork_queue2 = enqueue (f1, f2) fork_queue in
            One_child f (process_inner f' atoms seq_queue' fork_queue2)

process :: (Show a, Eq a) => Formula a -> Tree a
process f =
  let
    empty = Queue [] []
  in
    process_inner f [] empty empty

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
    Open_leaf f ->
      let
        node = str_num ++ "[label=\"" ++ (show_html f) ++ "\"]\n"
        accum1 = accum ++ node ++ edge
      in
        (accum1, num)
    Closed_leaf f1 f2 ->
      let
        str_num2 = "N" ++ (show $ num + 1)
        node = str_num ++ "[label=\"" ++ (show_html f1) ++ "\"]\n" ++
          str_num2 ++ "[label=\"" ++ (show f2) ++ "\"]\n"
        edge1 = str_num ++ " -> " ++ str_num2 ++ "\n"
        accum1 = accum ++ node ++ edge ++ edge1
      in
        (accum1, num + 1)
    One_child f subtree ->
      let
        node = str_num ++ "[label=\"" ++ (show_html f) ++ "\"]\n"
        accum1 = accum ++ node ++ edge
        (accum2, num2) = show_dot_inner subtree accum1 (num + 1) (Just str_num)
      in
        (accum2, num2)
    Fork f subtree1 subtree2 ->
      let
        node = str_num ++ "[label=\"" ++ (show_html f) ++ "\"]\n"
        accum1 = accum ++ node ++ edge
        (accum2, num2) = show_dot_inner subtree1 accum1 (num + 1) (Just str_num)
        (accum3, num3) = show_dot_inner subtree2 accum2 (num2 + 1) (Just str_num)
      in
        (accum3, num3)
--     Node f lst ->
--       let
--         node = str_num ++ "[label=\"" ++ (show_html f) ++ "\"]\n"
--         accum1 = accum ++ node ++ edge
--       in
--         case lst of
--           [] -> (accum1, num)
--           [[subtree]] -> show_dot_inner subtree accum1 (num + 1) (Just str_num)
--           [[subtree1, subtree2]] ->
--             let
--               (accum2, num2) = show_dot_inner subtree1 accum1 (num + 1) (Just str_num)
--             in
--               show_dot_inner subtree2 accum2 (num2 + 1) (Just $ "N" ++ (show num2))
--           [[subtree1], [subtree2]] ->
--             let
--               (accum2, num2) = show_dot_inner subtree1 accum1 (num + 1) (Just str_num)
--             in
--               show_dot_inner subtree2 accum2 (num2 + 1) (Just str_num)
--           _ -> (accum1, num)
