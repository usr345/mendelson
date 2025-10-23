import Debug.Trace (trace)
import System.IO
import qualified Data.List
import Formula

data Tree a =
  Closed_leaf (Formula a) (Formula a)
  | Open_leaf (Formula a)
  | One_child (Formula a) (Tree a)
  | Sequence (Formula a) (Tree a) (Tree a)
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


process_inner :: (Show a, Eq a) => Formula a -> [(a, Bool)] -> Bool -> (Tree a, [(a, Bool)])
process_inner f atoms no_calc =
  case f of
    F_atom a -> let atoms' = (a, True):atoms
                in
                  case no_calc of
                    -- Нужно считать
                    False -> case (has_contradiction atoms') of
                                 Nothing -> (Open_leaf f, atoms')
                                 Just b -> (Closed_leaf f (F_atom b), atoms')
                    True -> (Open_leaf f, atoms')
    F_neg (F_atom a) -> let atoms' = (a, False):atoms
                        in
                          case no_calc of
                            False -> case (has_contradiction atoms') of
                                         Nothing -> (Open_leaf f, atoms')
                                         Just b -> (Closed_leaf f (F_atom b), atoms')
                            True -> (Open_leaf f, atoms')
    F_neg (F_neg f') -> let (subtree, atoms') = process_inner f' atoms no_calc
                        in
                          (One_child f subtree, atoms')
    F_neg (F_conj f1 f2) -> let (subtree1, _) = process_inner f1 atoms no_calc
                                (subtree2, _) = process_inner f2 atoms no_calc
                            in
                              (Fork f subtree1, atoms')
    -- F_conj f1 f2 -> let (subtree2, atoms2) = process_inner f2 atoms subtree
    --                 in
    --                   trace ((show subtree2) ++ " " ++ (show atoms2))
    --                   $ process_inner f1 atoms2 (Just subtree2)
    _ -> (Open_leaf f, [])

process :: (Show a, Eq a) => Formula a -> Tree a
process f =
  let (tree, _) = process_inner f [] False
  in
    tree

newtype NoQuotes = NoQuotes String deriving Eq
instance Show NoQuotes where show (NoQuotes str) = str

atom_A :: NoQuotes
atom_A = NoQuotes "A"
atom_B = NoQuotes "B"
atom_C = NoQuotes "C"

f1 :: Formula NoQuotes
f1 = F_atom atom_A

f2 :: Formula NoQuotes
f2 = F_neg (F_atom atom_A)

f3 :: Formula NoQuotes
f3 = F_neg (F_neg (F_atom atom_A))

f4 :: Formula NoQuotes
f4 = F_conj (F_atom atom_A) (F_neg (F_atom atom_A))


    -- F_neg (F_atom a) ->
    -- F_impl a b -> [[process (F_neg a)], [process b]]
    -- F_neg (F_impl a b) -> [[process a, process (F_neg b)]]
    -- F_conj a b -> [[process a, process b]]
    -- F_neg (F_conj a b) -> [[process (F_neg a)], [process (F_neg b)]]
    -- F_disj a b -> [[process a], [process b]]
    -- F_neg (F_disj a b) -> [[process (F_neg a), process (F_neg b)]]
    -- F_neg (F_neg a) -> [[process a]]

-- process :: Formula a -> Tree a
-- process formula =
--   Node formula ()
