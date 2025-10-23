-- import System.IO
import Formula
import Solver

newtype NoQuotes = NoQuotes String deriving Eq
instance Show NoQuotes where show (NoQuotes str) = str

atom_A :: NoQuotes
atom_A = NoQuotes "A"
atom_B :: NoQuotes
atom_B = NoQuotes "B"
atom_C :: NoQuotes
atom_C = NoQuotes "C"

f1 :: Formula NoQuotes
f1 = F_atom atom_A

f2 :: Formula NoQuotes
f2 = F_neg (F_atom atom_A)

f3 :: Formula NoQuotes
f3 = F_neg (F_neg (F_atom atom_A))

f4 :: Formula NoQuotes
f4 = F_conj f1 f2

f5 :: Formula NoQuotes
f5 = F_conj f2 f1

f6 :: Formula NoQuotes
f6 = F_disj f1 f2

a1 :: Formula NoQuotes
a1 = F_neg (F_impl (F_atom atom_A) (F_impl (F_atom atom_B) (F_atom atom_A)))

a2 :: Formula NoQuotes
a2 = F_neg (F_disj (F_atom atom_A) (F_neg (F_atom atom_A)))

a3_1 :: Formula NoQuotes
a3_1 = F_impl (F_atom atom_A) (F_impl (F_atom atom_B) (F_atom atom_C))

a3_2 :: Formula NoQuotes
a3_2 = (F_impl (F_impl (F_atom atom_A) (F_atom atom_B)) (F_impl (F_atom atom_A) (F_atom atom_C)))

a3 :: Formula NoQuotes
a3 = F_neg (F_impl a3_1 a3_2)

main :: IO ()
main = do
    let filePath = "output.gv"
    let tree = process a3
    let content = show_dot tree
    writeFile filePath content
