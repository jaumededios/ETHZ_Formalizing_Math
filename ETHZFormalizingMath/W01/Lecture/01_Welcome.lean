import Mathlib

-----------------------------------
-- 0. The very very basics of Lean
----------------------------------

-- Lean does most computations the way you expect.
-- To see the result of a computation, write #eval
#eval 2+2
-- Click on the underlined blue word.
-- The result appears. on the right hand side.

-- Lean does not use parentheses to define function evaluations
#eval max 2 4

-- We can define functions with def
def f (x : ℕ) :=  x + 1

#eval f 3 -- 4

-- In Lean, everything has a type.

-- We can use #check to check the type of an expression
#check f

-- The types are very close to what we have learnt
-- but that's not always intuitive

#eval (3:ℕ) -- This is the natural number 3
#eval (3:ℝ) -- This is the real number 3. What is a real number?




------------------------------------------------
-- 1. Stating an proving theorems with rewrites
------------------------------------------------

-- Mathlib has a lot of already proven theorems and definitions
-- But they're usually scary

#check mul_assoc  -- multiplication is associative in semigroups
#check mul_comm -- multiplication is commutative in commutative magmas

-- Lean knows how to "coerce" the theorems into normal cases
variable (a b c : ℝ) -- If we define a b c as real variables
#check (mul_assoc a b c) -- Lean knows ℝ (written \R) is a commutative semigroup



-- Theorems are proven by transforming the goal.
-- Click on a step of the proof, to see the state of the proof

--The rewrite rw [...] tactic lets you rewrite the goal using an expression
example (a b c : ℝ) :  -- Variables
        a * b * c = b * (a * c)  -- conclusion
        := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]




example (a b c d : ℝ)         -- Variables
        (hyp : c = b * a )    -- Hypotheses
        (hyp' : 0 = a * b) :
        c = 0 -- Conclusion
        := by
  rw [hyp] -- rewrites using a hypothesis
  sorry -- continue the proof yourself!


lemma my_add_sub (R:Type) [Ring R]
                  (a b : R) :
        a + b + -b = a := by
  sorry -- try rw? to ask for "rewrites that stick"







----------------------
-- 1.2 The Calc tactic
----------------------

example
      (G : Type) [Group G] (a b c : G) -- Variables
      (h1: b*a = 1) (h2: a*c = 1): -- Hypotheses
      b=c  -- conclussion
      := by -- Start of proof
      calc -- We enter a calculation proof
      b = b*1 := by sorry -- use "hint" or "rw?" if you don't know what to do
      _ = b*(a*c):= by sorry --
      _ = (b*a)*c := by sorry --
      _ = 1*c := by sorry --
      _ = c := by sorry -- try "aesop" for dark magic







-------------------------
-- 1.3 Quantifiers (∃,∀)
-------------------------

-- If there is a forall in the conclusion, we "intro" the elements into the space
example
  (R: Type) [Ring R]:
  ∀ a b : R, a + b + - b = a
  := by
  intro a b -- we introduce a and b
  sorry -- you can use apply [my_lemma] to apply a lemma, similarly to rw for expressions

-- If we have to show something exists, we find it and "use" it
example
  (R: Type) [Ring R]:
  ∃ z: R, ∀ x y : R, x*z = y*z
  := by
  sorry

-- If we know something exists, we can use it:
example
  (a: ℝ)
  (square: ∃ s:ℝ, a = s^2):
  a≥ 0
  := by
  obtain ⟨ s, hs ⟩ := square
  sorry -- rewrrite using hs, and use apply? to find a lemma

-- You should think of a "forall" as a map from an element to a conclusion
example
  (G:Type) [Group G]
  (ord3: ∀ h: G, h^3 =1):
  ∀ g:G, g^6 = 1 := by
  intro g
  calc --
    g^6 = (g^3)^2 := by sorry
    _ = (1)^2 := by sorry -- do not use hint here, it gives weird stuff
    _ = 1 := by sorry


-- 1.4 Definitions
------------------

-- A definition is a map from the types to a proposition
def bounded (f: ℝ → ℝ) : Prop :=
  ∃ M: ℝ, ∀ x:ℝ, |f x| ≤ M

-- Exercise

def continuous_at (f: ℝ → ℝ) (x:ℝ) : Prop :=  sorry

def continuous (f: ℝ → ℝ) : Prop := sorry
