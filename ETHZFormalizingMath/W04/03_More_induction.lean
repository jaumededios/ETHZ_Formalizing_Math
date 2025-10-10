
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic


/-
Today's class is heavily based on the "Inductive Types" and "Induction"
chapters of "Theorem Proving in Lean"
-/


-- # Induction beyond the natural numbers

-- ## Examples: Lists

namespace Hidden

inductive List (α : Type*) where
| nil  : List α
| cons : α → List α → List α

namespace List
variable {α : Type*}

def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
------
theorem append_nil (as : List α) :
    append as nil = as := sorry


def length (a : List α) : ℕ := sorry

theorem len_append (a b : List α) :
  length (append a b) = length a + length b
  := by sorry
end List

-- # Examples: Trees

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree


def Depth (t : BinaryTree):ℕ := match t with
  | BinaryTree.leaf => 0
  | BinaryTree.node t1 t2 => 1 + max (Depth t1) (Depth t2)



namespace BinaryTree

#eval Depth (node (node leaf (node leaf leaf)) leaf)


def Isomorphic (t1 t2 : BinaryTree) : Bool :=
  match t1  with
  | leaf  => match t2 with
    | leaf => true
    | node _ _ => false
  | node n1 n2 => match t2 with
    | leaf => false
    | node m1 m2 => (Isomorphic n1 m1)∧(Isomorphic n2 m2)∨
                    (Isomorphic n1 m2)∧(Isomorphic n2 m1)

#eval Isomorphic (node (node leaf (node leaf leaf)) leaf)
                 (node leaf (node leaf (node leaf leaf)))

example (t1 t2 : BinaryTree) (HI : Isomorphic t1 t2) : Depth t1 = Depth t2 := sorry


end BinaryTree

end Hidden
