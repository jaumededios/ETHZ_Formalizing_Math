import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
open Lean Elab Command


/-
# Part 1: Induction on the natural numbers

Prove the theorems that we left empty in class
-/
def divides (x n : ℕ) : Prop := ∃ k: ℕ , n = x*k

-- Easy
theorem divides_trans {a b c : ℕ} : divides a b → divides b c → divides a c := by
  intro h1 h2
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  use m * n
  rw [hn, hm]
  ring

-- Easy
theorem divides_self (a : ℕ) : divides a a := by use 1; ring

-- Easy
theorem divides_smaller {a b : ℕ} (h0 : b > 0) (hd : divides a b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hd
  --aesop
  subst hk
  exact Nat.le_mul_of_pos_right a (Nat.pos_of_mul_pos_left h0)

def isPrime (p : ℕ) : Prop := (p>1)∧(∀ x:ℕ, x>1 → (divides x p → x=p))

-- Easy
theorem not_prime_has_factors (n : ℕ) (h1 : n > 1) (hn : ¬ isPrime n) :
    ∃ m > 1, divides m n ∧ m < n := by
  rw [isPrime] at hn
  push_neg at hn
  obtain ⟨x, hge1, hd, hne⟩ := hn h1
  use x
  have hle : x ≤ n := divides_smaller (Nat.zero_lt_of_lt h1) hd
  exact ⟨hge1, hd, by omega⟩

#check Nat.recOn


-- Create your own induction lemma
-- Medium

theorem strong_recursion (p : ℕ → Prop) (ind : (n : ℕ) → ((m : ℕ) → m < n → p m) → p n) (t : ℕ) :
    p t := by
  apply ind
  induction t with
  | zero => simp
  | succ k hi =>
    intro m hm
    rcases Nat.lt_add_one_iff_lt_or_eq.mp hm with h1 | h2
    · exact hi _ h1
    · rw [h2]
      apply ind
      exact hi


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

#check Isomorphic leaf

/- For the following exercise, direct induction will not work

You have two options:

-- Option 1: Write a stronger induction hypothesis and use it
-- Option 2: Use the syntactic sugar "induction t1 generalizing t2" or something similar

Code first Option 1 and then Option 2.
Ideally you should be able to copy-paste most of the code from option 1 to option 2
-/

theorem tree_recursion (p : BinaryTree → Prop) (hLeaf : p leaf)
    (hNode : ∀ t1 t2, p t1 → p t2 → p (node t1 t2)) (t : BinaryTree) : p t := by
  induction t with
  | leaf => exact hLeaf
  | node t1 t2 ih1 ih2 => exact hNode t1 t2 ih1 ih2

-- Medium
example (t1 t2 : BinaryTree) (HI : Isomorphic t1 t2) : Isomorphic t2 t1 := by
  induction t1 using tree_recursion generalizing t2 with
  | hLeaf => cases t2 with | leaf => assumption | node => exact HI
  | hNode x y hx hy => cases t2 with | leaf => exact HI | node a b => grind [Isomorphic]

theorem Isomorphic_refl (t1 t2 : BinaryTree) (HI : Isomorphic t1 t2) : Isomorphic t2 t1 := by
  induction t1 generalizing t2 with
  | leaf => cases t2 with | leaf => assumption | node => exact HI
  | node x y hx hy => cases t2 with | leaf => exact HI | node a b => grind [Isomorphic]

-- Hard
example (t1 t2 t3 : BinaryTree) (H12 : Isomorphic t1 t2) (H23 : Isomorphic t2 t3) :
    Isomorphic t1 t3 := by
  induction t1 generalizing t2 t3 with
  | leaf => grind [BinaryTree, Isomorphic]
    /-
    cases t2 with
    | leaf => assumption
    | node => cases t3 with | leaf => rfl | node => assumption
    -/
  | node a b ha hb =>
    cases t2 with
    | leaf =>
      cases t3 with
      | leaf => grind
      | node => grind only [Isomorphic]
    | node c d =>
      cases t3 with
      | leaf => simp_all [Isomorphic]
      | node e f => grind [Isomorphic]
end BinaryTree




-- # Part 3: Induction beyond the natural numbers 2: Lists
-- ## Defining lists
namespace Hidden

inductive List (α : Type*) where
| nil  : List α
| cons : α → List α → List α

#check List.nil -- []
#check List.cons 0 List.nil -- [0]
#check List.cons 1 (List.cons 0 List.nil) -- [0, 1]
#check List.cons 2 (List.cons 1 (List.cons 0 List.nil)) -- [0, 1, 2]

namespace List
variable {α : Type*}

-- ## Appending lists
def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := rfl

theorem cons_append (a : α) (as bs : List α) :
  append (cons a as) bs = cons a (append as bs) := rfl
------

-- Easy
theorem append_nil (as : List α) : append as nil = as := by
  fun_induction append with
  | case1 => rfl
  | case2 a as ih => rw [ih]

-- ## Length function
--- Define a function that computes the length of a list
-- Easy
def length (a : List α) : ℕ :=
  match a with
  | nil => 0
  | cons _ as => 1 + length as

-- And show that works well with appending

-- Medium
theorem len_append (a b : List α) : length (append a b) = length a + length b := by
  fun_induction append a b with -- all_goals grind [length] does the job
  | case1 => simp [length]
  | case2 x xs ih =>
    rw [length, length, ih]
    ring


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
def length' (l : List α) : ℕ := reduce (fun _ y => 1 + y) 0 l

-- Check to make sure
#eval length' (List.nil : List ℕ)
#eval length' (List.cons 100 List.nil)
#eval length' (List.cons 5 (List.cons 60 (List.cons 100 List.nil)))

-- Even better: just prove it
example (l : List α) : length l = length' l := by
  unfold length'
  fun_induction reduce _ 0 l with
  | case1 => rfl
  | case2 head tail ih =>
    rw [← ih, length]

--- Define the sum of elements in a list using reduce
-- Medium
def AddList (l : List ℕ) : ℕ := reduce (fun x y => x + y) 0 l

#check List.cons 2 (List.cons 1 (List.cons 0 List.nil)) -- [0, 1, 2]
#eval reduce (fun a b : ℕ => a + b) 4 (List.cons 3 (List.cons 8 (List.cons 5 List.nil)))

def AddList' (l : List ℕ) : ℕ := match l with
| nil => 0
| cons head tail => head + AddList' tail

-- The same proof as before works
example (l : List ℕ) : AddList' l = AddList l := by
  unfold AddList
  fun_induction reduce _ 0 l with
  | case1 => rfl
  | case2 head tail ih =>
    rw [← ih, AddList']

-- ## Reversing lists

-- Define a function that reverses a list. C
-- Medium
def reverse (a : List α) : (List α) :=
match a with
  | nil => nil
  | cons a la => append (reverse la) (cons a nil)

--- For these two you may want to define some auxiliary lemmas

lemma reverse_add_single (head : α) (tail : List α) :
    reverse (append tail (cons head nil)) = append (cons head nil) (reverse tail) := by
  fun_induction reverse with
  | case1 => rfl
  | case2 x xs ih => simp [append, reverse, ih]

lemma append_assoc (a b c : List α) : append (append a b) c = append a (append b c) := by
  fun_induction append a b with
  | case1 => rfl
  | case2 head tail ih => simp [append, ih]


-- Hard
theorem reverse_involution (a : List α) : reverse (reverse a) = a := by
  fun_induction reverse a with
  | case1 => rfl
  | case2 head tail ih =>
    rw [reverse_add_single, ih, cons_append, nil_append]

-- b.reverse.append (tail.reverse.append (cons head nil))
-- append b.reverse (append tail.reverse (cons head nil))

-- Hard
theorem reverse_add (a b : List α) : reverse (append a b) = append (reverse b) (reverse a) := by
  fun_induction reverse a with
  | case1 => rw [nil_append, append_nil]
  | case2 head tail ih => rw [cons_append, reverse, ih, append_assoc]



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

lemma reduce_append (a b : List α) (f0 : α) (f : α → α → α) :
    reduce f f0 (append a b) = reduce f (reduce f f0 b) a := by
  induction a with
  | nil => rfl
  | cons => grind [append, reduce]

lemma reverse_single (head : α) (tail : List α) :
    (cons head tail).reverse = append tail.reverse (cons head nil) := by
  grind [reverse]

theorem brave {f : α → α → α} (hswap : ∀ x y z, f x (f y z) = f y (f x z)) (f0 : α) (l : List α)
    : reduce f f0 l = reduce f f0 (reverse l) := by
  have pull_swap :
      ∀ (x y : α) (l : List α), reduce f (f x y) l = f x (reduce f y l) := by
    intro x y l
    induction l with
    | nil => simp [reduce]
    | cons a t ih => simp [reduce, ih, hswap a x (reduce f y t)]
  induction l with
  | nil => rfl
  | cons head tail ih =>
    simp_rw [reduce, ih, ← pull_swap]
    simp_rw [reverse_single, reduce_append]
    rfl

example (l : List ℕ) : AddList l = AddList (reverse l) := by
  apply brave
  intros
  ring

end List



end Hidden
