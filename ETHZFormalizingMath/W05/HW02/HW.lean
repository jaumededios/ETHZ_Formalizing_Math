import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
open Lean Elab Command


/-
# Part 1: Induction on the natural numbers

Prove the theorems that we left empty in class
-/
def divides (x n : ℕ) : Prop := ∃ k: ℕ , n = x*k

-- Easy
theorem divides_trans {a b c : ℕ} :
  divides a b → divides b c → divides a c := by sorry

-- Easy
theorem divides_self (a : ℕ) : divides a a := by sorry

-- Easy
theorem divides_smaller {a b : ℕ} (h0 : b > 0) (hd : divides a b) : a ≤ b
  := by sorry

def isPrime (p : ℕ) : Prop := (p>1)∧(∀ x:ℕ, x>1 → (divides x p → x=p))

-- Easy
theorem not_prime_has_factors
  (n : ℕ) (h1 : n > 1) (hn : ¬ isPrime n) :
  ∃ m>1, divides m n ∧ m<n := by sorry

#check Nat.recOn


-- Create your own induction lemma
-- Medium
theorem strong_recursion
  (p : ℕ → Prop)
  (ind : (n : ℕ) → ((m : ℕ) → m < n → p m) → p n)
  (t : ℕ) :
  p t := by sorry

-- This one we already did in class
theorem prime_divides (n : ℕ) (hn : n > 1) :
  ∃ p: Nat, isPrime p ∧ divides (p:Nat) n := by
  induction n using strong_recursion with | ind n hind =>
    by_cases is_prime: (isPrime n)
    case pos =>
      exact ⟨ n, ⟨is_prime, divides_self n⟩⟩
    case neg =>
      rcases not_prime_has_factors n hn is_prime with ⟨m,⟨m_big, m_divides_n, m_small⟩⟩
      rcases hind m m_small m_big with ⟨p, ⟨p_prime,p_divides_m⟩⟩
      exact ⟨p, ⟨p_prime, divides_trans p_divides_m m_divides_n ⟩ ⟩



-- # Part 2: Induction beyond the natural numbers 1: Trees

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



/- For the following exercise, direct induction will not work

You have two options:

-- Option 1: Write a stronger induction hypothesis and use it
-- Option 2: Use the syntactic sugar "induction t1 generalizing t2" or something similar

Code first Option 1 and then Option 2.
Ideally you should be able to copy-paste most of the code from option 1 to option 2
-/

-- Medium
example (t1 t2 : BinaryTree) (HI : Isomorphic t1 t2) :  Isomorphic t2 t1 := sorry


-- Hard
example (t1 t2 t3: BinaryTree)
        (H12 : Isomorphic t1 t2)
        (H12 : Isomorphic t2 t3) : Isomorphic t1 t3 := sorry

end BinaryTree




-- # Part 3: Induction beyond the natural numbers 2: Lists
-- ## Defining lists
namespace Hidden

inductive List (α : Type*) where
| nil  : List α
| cons : α → List α → List α

namespace List
variable {α : Type*}

-- ## Appending lists
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)

theorem nil_append (as : List α) :
  append nil as = as := rfl
theorem cons_append (a : α) (as bs : List α) :
  append (cons a as) bs = cons a (append as bs) := rfl
------

-- Easy
theorem append_nil (as : List α) :
    append as nil = as := sorry

-- ## Length function
--- Define a function that computes the length of a list
-- Easy
def length (a : List α) : ℕ := sorry

-- And show that works well with appending

-- Medium
theorem len_append (a b : List α) :
  length (append a b) = length a + length b
  := by sorry


/-
The two sections below this are harder:
-/


-- ## The Reduce map

-- Think deeply about this definition and what it means
def reduce {α β : Type*} (f : α → β → β) (f0 : β) (l : List α) :=
  match l with
  | nil => f0
  | cons a0 tail => f a0 (reduce f f0 tail)


-- Define again the function "length" using "reduce"
-- Medium
def length' (l: List α) : ℕ  := sorry

---


--- Define the sum of elements in a list using reduce
-- Medium
def AddList (l: List ℕ) : ℕ := sorry

-- ## Reversing lists

-- Define a function that reverses a list. C
-- Medium
def reverse (a : List α) : (List α) :=
match a with
  | nil => nil
  | cons a la => append la (cons a nil)

--- For these two you may want to define some auxiliary lemmas


-- Hard
theorem reverse_involution (a : List α) : reverse (reverse a) = a := by sorry

-- Hard
theorem reverse_add (a b : List α) : reverse (append a b) = append (reverse b) (reverse a) := sorry



-- # For the brave
/-
This is beyond the content of the class.
You do not need to even attempt this to get the maximum grade, but it's cool to think about.

1. In the special case of Reduce where we have (f : α → α → α)  (In other words α = β),
   find what condition do you need f to have so that reduce f f0 l = reduce f f0 (reverse l)

   You should find hypotheses weak enough so that they apply to showing
    - Addlist f = Addlist (reverse f)
    - length' f = length' (reverse f)

2. Repeat part 1 changing reverse for "append", or at least convince yourself you can do that.
-/

end List



end Hidden
