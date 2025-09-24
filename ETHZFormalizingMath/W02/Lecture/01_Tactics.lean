import Mathlib

/- Plan for Today's class

1. Some refresher on the tactics that we have access to

2. A more grown-up proof in Algebra: Constructiong the nilradical ring

3. A more grown-up proof in Analysis: Sum of continuous functions is continuous

-/
------------------------------------------------------------------------------

/-
# Tactics warm-up (for NNG grads)

Tiny examples showing tactics you can use today:
`rw`, `simp`, `rcases`, `by_cases`, `linarith`, `ring`, `norm_num`, `ext`, `aesop`,
`refine`/`simpa` patterns.
-/

section TacticsWarmup

-- 1) `simp`, `simp?`, and `simpa`
--    Great for cleaning goals built from `rfl`-ish lemmas and `[simp]` rules.
example (x y : ℝ) : x + 0 + y = x + y := by
  sorry

-- 2) `rw` / `rw [← …]` — directed rewriting.
example (x y : ℝ) (h : x = y) : x + x = y + y := by
  sorry

-- 3) `rcases` — destructuring ∧ / ∨ / ∃ in one go.
example (h : ∃ n : ℕ, n ≥ 10 ∧ Even n) : ∃ m, m ≥ 5 := by
  sorry


-- 4) `by_cases` + `simp [*]` — classical case splits.
example (my_prop : Prop)  : my_prop ∨ ¬ my_prop := by
  sorry

-- 5) `linarith` — linear arithmetic over ℚ/ℝ/ℤ.
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  sorry

-- 6) `ring` — normalize polynomial expressions in (semi)rings.
variable {R : Type} [CommRing R]
example (a b : R) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  sorry

-- 7) `norm_num` — crunch concrete numerals.
example : (37 : ℤ) % 5 = 2 := by
  sorry

-- 8) `ext` of `funext` (a.k.a. function/structure extensionality).
--    Super useful later for equalities of functions, ideals, submodules, products…
example (f g : ℝ → ℝ) :
    (fun x => f x + g x) = fun x => (f + g) x := by
  sorry


-- 9) `aesop` — a strong general-purpose finisher for logic-y goals.
example (a b : ℝ) (h : a = b) : b = a := by
  sorry

-- 10) `congrarg` — apply a function to both sides of an equality
example (x y z : ℝ) (h : x = y) : (fun w : ℝ => w + z) x = y + z := by
  sorry

end TacticsWarmup
