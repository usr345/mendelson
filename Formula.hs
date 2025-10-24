module Formula where

data Formula a =
  F_atom a
  | F_neg (Formula a)
  | F_impl (Formula a) (Formula a)
  | F_conj (Formula a) (Formula a)
  | F_disj (Formula a) (Formula a)

-- 0 - наивысший приоритет
priority :: Formula a -> Int
priority (F_atom _)    = 0
priority (F_neg _)     = 1
priority (F_conj _ _)  = 2
priority (F_disj _ _)  = 3
priority (F_impl _ _)  = 4

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


newtype Bot a = Bot (Formula a)

instance (Show a) => Show (Bot a) where
  show (Bot f) = "&#8869;(" ++ (show_html f) ++ ", " ++ show_html (F_neg f) ++ ")"
