import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

/-
Today's class is heavily based on the "Inductive Types" and "Induction"
chapters of "Theorem Proving in Lean"
-/




-- # Back to pattern matching: structural recursion

open Nat
variable (x : Nat) {α β : Type}

-- Lean has a powerful pattern-matching engine

def swap (p : α × β) : β × α :=
  match p with
  | (a, b) => (b, a)


def sub1 : Nat → Nat
  | 0     => 0
  | x + 1 => x

def isZero : Nat → Bool
  | 0     => true
  | _ + 1 => false

def factorial : ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1)*(factorial n)

#eval factorial 5

def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x

example : (x : ℕ) → sub1 (sub1 x )= sub2 x
  | 0 =>  rfl
  | 1 =>  rfl
  | _+2 =>  rfl

def foo : Nat → Nat → Nat
  | 0,     n     => n
  | m + 1, 0     => foo m 0
  | m + 1, n + 1 => m+n


-- Which also applies to propositions
#print And

example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

#print Exists
example (p q : α → Prop) :
        (∃ x, p x ∨ q x) →
        (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

namespace Nat
-- congrArg f a=b -> fa = fb
theorem zero_add'' : ∀ n, Nat.add Nat.zero n = n
  | Nat.zero   => rfl
  | Nat.succ n => congrArg Nat.succ (Nat.zero_add'' n)
end Nat



-- # Constructing our own natural numbers in Lean

namespace Hidden

inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr


namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

-- Magic (Next week) that lets us use `+` and `0` for our version of Nat
instance : Add Nat where add := add
instance : Zero Nat where zero := zero

theorem add_zero (m : Nat) : m + 0 = m := sorry
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := sorry

#check Nat.recOn

-- we could try to brute force build it but it won't work
-- def add' (m n : Nat) : Nat := Nat.recOn n m (fun n mplusn ↦ succ mplusn)

-- Now we can redo (one!) of the proofs from the first day while understanding what's going on

theorem zero_add (m : Nat) : zero + m = m := sorry

example (m : Nat) : zero + m = m := by sorry

end Nat


-- At this point you could do the whole NNG on lean,
-- luckily for you, you don't need to..
-- Instead, we exit Hidden and go back to "normal" mathlib
end Hidden

-- Normal natural numbers, not hidden ones

def divides (x n : ℕ) : Prop := ∃ k: ℕ , n = x*k

theorem divides_trans {a b c : ℕ} :
  divides a b → divides b c → divides a c := by sorry

theorem divides_self (a : ℕ) : divides a a := by sorry

theorem divides_smaller {a b : ℕ} (h0 : b > 0) (hd : divides a b) : a ≤ b
  := by sorry

def isPrime (p : ℕ) : Prop := (p>1)∧(∀ x>1,divides x p → x=p)

-- This one is much harder than the others
theorem not_prime_has_factors
  (n : ℕ) (h1 : n > 1) (hn : ¬ isPrime n) :
  ∃ m>1, divides m n ∧ m<n := by sorry

#check Nat.recOn
#check Nat.strongRec

-- We could also create our own Induction Lemma
theorem my_strong_recursion
  (p : ℕ → Prop)
  (ind : (n : ℕ) → ((m : ℕ) → m < n → p m) → p n)
  (t : ℕ) :
  p t := by sorry

theorem prime_divides (n : ℕ) (hn : n > 1) :
  ∃ p, isPrime p ∧ divides p n := by sorry
