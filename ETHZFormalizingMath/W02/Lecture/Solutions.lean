import Mathlib


/- Plan for Today's class

1. Some more rewrite-style proofs in the Grown-Up (VSCode) Lean

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
  simp [add_zero]  -- `simp?` can suggest rules; `simpa` closes the goal.

-- 2) `rw` / `rw [← …]` — directed rewriting.
example (x y : ℝ) (h : x = y) : x + x = y + y := by
  rw [h]

-- 3) `rcases` — destructuring ∧ / ∨ / ∃ in one go.
example (h : ∃ n : ℕ, n ≥ 10 ∧ Even n) : ∃ m, m ≥ 5 := by
  rcases h with ⟨n, hn, _heven⟩
  exact ⟨n, by linarith⟩

-- 4) `by_cases` + `simp [*]` — classical case splits.
example (p : Prop) [Decidable p] : p ∨ ¬ p := by
  by_cases hp : p <;> simp [hp]

-- 5) `linarith` — linear arithmetic over ℚ/ℝ/ℤ.
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  linarith

-- 6) `ring` — normalize polynomial expressions in (semi)rings.
variable {R : Type} [CommRing R]
example (a b : R) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring



-- 7) `norm_num` — crunch concrete numerals.
example : (37 : ℤ) % 5 = 2 := by
  norm_num

-- 8) `ext` of `funext` (a.k.a. function/structure extensionality).
--    Super useful later for equalities of functions, ideals, submodules, products…
example (f g : ℝ → ℝ) :
    (fun x => f x + g x) = fun x => (f + g) x := by
  funext x
  simp


-- 9) `aesop` — a strong general-purpose finisher for logic-y goals.
example (a b : ℝ) (h : a = b) : b = a := by
  aesop

-- 10) `congrarg` — apply a function to both sides of an equality
example (x y z : ℝ) (h : x = y) : (fun w : ℝ => w + z) x = y + z := by
  apply congrArg (fun t => t + z)
  simp [h]

end TacticsWarmup




-- # The Nilradical

section Nilradical

-- The goal of this section will be to make sense of the following theorem

-- theorem nilrad_subset_of_Prime (R : Type) [CommRing R] (I : Ideal R)
--                                (hI : I.IsPrime) :
--                                nilrad R ≤ I


-- The nilradical of R is defined as the set of nilpotent elements
-- nilrad R := {x:R | ∃ n:ℕ , x^n = 0}

#print IsNilpotent






-- ### Classes

#print Semigroup

-- When I write
variable (S : Type) [Semigroup S]
-- What I'm saying is that S is a type with attached functions

variable (a b c : S)

/- Since a b c are in a Semigroup, I can apply the
   Semigroup.mul_assoc, whithout having to remember
   where it comes from -/

#check Semigroup.mul_assoc a b c






-- ### {Braced} parameters

-- Example
lemma sum_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :a+b>0 := by bound
lemma sum_pos_braces {a b : ℝ} (ha : a > 0) (hb : b > 0) :a+b>0 := by bound

#check sum_pos 3 2 three_pos two_pos
#check sum_pos_braces three_pos two_pos

-- By using @, we can "force" the inferred values
#check @sum_pos_braces 3 2 three_pos two_pos


-- ### Into the Nilradical

variable (R : Type) [CommRing R] (x y : R)

/-- Element * Nilpotent = Nilpotent -/
lemma mul_nilpotent (a b : R) (hb : IsNilpotent b) :
    IsNilpotent (a * b) := by
  unfold IsNilpotent
  obtain ⟨nb, hnb ⟩  :=  hb
  use nb
  ring_nf
  rw [hnb]
  ring



/-- Sum of nilpotents is nilpotent -/

lemma overshoot_pow_zero {R : Type}
  [CommRing R] (r : R) (x y : ℕ)
  (ineq : y ≥ x) (nilp : r ^ x = 0) : (r^y=0)
  := by
  calc
  r^y = r^(x+(y-x)):= by rw [Nat.add_sub_cancel' ineq]
  _   = r^x * r^(y-x) := by ring_nf
  _   = 0 := by rw[nilp,zero_mul]

lemma nilpotent_add {a b : R} (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (a + b) := by
    unfold IsNilpotent
    obtain ⟨nb, hnb ⟩  :=  hb
    obtain ⟨na, hna ⟩  :=  ha
    use na + nb
    rw [@add_pow]
    refine Finset.sum_eq_zero ?_
    intro x hx

    by_cases ineq : (x≥na)
    · rw [overshoot_pow_zero a na x ineq hna]
      ring
    · have other_ineq : ((na + nb - x) ≥ nb) := by omega
      rw [overshoot_pow_zero b nb (na + nb - x) other_ineq hnb]
      ring


-- The nilradical of an ideal. [Duplicates an existing definition in mathlib].
/-
Regular math:

An ideal is a subset of a ring that:
  - Contains zero
  - Is closed under internal addition
  - Is closed under multiplication by external elements
-/

/-
Lean Ideals (First idea)
An ideal I is a "structure" containing
  - A carrier set (the set of elements in the ideal)
  - A proof that 0 ∈ I
  - A proof that (a b : ℝ) (a b ∈ I) → (a + b ∈ I)
  - A proof that (a b : ℝ) (b ∈ I)   → (a ⬝ b ∈ I)
-/
#print Ideal
#print Submodule

def nilrad : Ideal R where
  carrier := {a : R | IsNilpotent a}
  zero_mem' := by
                use 1
                ring
  add_mem' := by apply nilpotent_add
  smul_mem' s t := by apply mul_nilpotent
/-
Lean Ideals (actual implementation)
  - An Ideal I of R is a submodule of R as an R-module
-/

/-- Nilpotents -/


lemma primeIdeal_contains_IsNilpotent_mem
  {R : Type} [CommRing R]
  {I : Ideal R} (hI : Ideal.IsPrime I)
  {a : R} {n : ℕ} (ha : a ^ n ∈ I) :
    a ∈ I := by
    exact Ideal.IsPrime.mem_of_pow_mem hI n ha


theorem nilrad_subset_of_Prime
  {I : Ideal R} (hI : I.IsPrime) :
  nilrad R ≤ I := by
    intro x hx
    obtain ⟨ n, hn ⟩ := hx
    have ha: x^n ∈ I := by
      rw[hn]
      apply zero_mem
    exact primeIdeal_contains_IsNilpotent_mem hI ha
end Nilradical





section Continuous

variable {X Y Z T : Type}
         [MetricSpace X] [MetricSpace Y]
         [MetricSpace Z] [MetricSpace T]


#synth  MetricSpace (X × Y)
variable (x1 x2 : X) (y1 y2 : Y)
#check dist (x1, y1) (x2, y2)

def Continuous_at (x : X) (f : X → Y) : Prop :=
  ∀ ε>0,∃ δ>0, ∀ (y:X), dist x y < δ → dist (f x) (f y) <ε

theorem Comp_Continuous (x : X) (f : X → Y) (g : Y → Z)
  (hf : Continuous_at x f) (hg : Continuous_at (f x) g) :
  Continuous_at x (g∘f) := by
  unfold Continuous_at
  intro ε εpos
  rcases  hg ε εpos with ⟨δg, δgpos, gineq⟩
  obtain ⟨δf, δfpos, fineq⟩ :=  hf δg δgpos
  use δf, δfpos
  simp_all



def FProd (f : X → Y) (g : Z → T) := (fun (x, z) => (f x, g z))

theorem Prod_Continuous (f : X → Y) (g : Z → T) (x : X) (z : Z)
  (hf : Continuous_at x f) (hg : Continuous_at z g) :
  Continuous_at (x,  z) (FProd f g) := by
  unfold Continuous_at
  intro ε εpos
  rcases hf ε εpos with ⟨δf, δfpos, fclose⟩
  rcases hg ε εpos with ⟨δg, δgpos, gclose⟩
  use (min δf δg), lt_min δfpos δgpos
  simp_all [Prod.dist_eq, FProd]

def Diag (A : Type) : (A → A × A):= (fun a => (a,a))

theorem Diag_Continuous (x : X) :
  Continuous_at x (Diag X)
    := by
    intro ε εpos
    use ε, εpos
    simp [Diag,Prod.dist_eq]

def R_add : ℝ×ℝ → ℝ := fun (a,b) ↦ a+b

theorem R_add_continuous_at (v : ℝ × ℝ) :
  Continuous_at v R_add := by
    rcases v with ⟨x, y⟩
    unfold Continuous_at
    intro ε εpos
    use ε / 3, by linarith
    rintro ⟨a, b⟩ hclose
    simp_all [Prod.dist_eq]
    calc
      |(x + y) - (a + b)| = |(x - a) + (y - b)| := by ring_nf
      _ ≤ |x - a| + |y - b| := by exact abs_add_le (x - a) (y - b)
      _ ≤ ε/3 + ε/3 := by bound
      _ < ε := by linarith

variable (f : X → Y) (g : X → Y)

theorem add_cont_at (f g : ℝ → ℝ) (x : ℝ)
  (hf : Continuous_at x f)
  (hg : Continuous_at x g) :
  Continuous_at x (f+g)
  := by
    let R_add: ℝ×ℝ → ℝ := fun (a,b) ↦ a+b
    let fg := FProd f g
    have comp_eq : f+g = R_add ∘ (fg ∘ Diag ℝ):= by
      simp_all only [R_add, fg]
      rfl
    rw [comp_eq]
    apply Comp_Continuous
    case hf =>
      apply Comp_Continuous
      case hf =>
       apply Diag_Continuous x
      case hg =>
       apply Prod_Continuous f g x x hf hg
    case hg =>
     apply R_add_continuous_at ((fg ∘ Diag ℝ) x)

end Continuous
