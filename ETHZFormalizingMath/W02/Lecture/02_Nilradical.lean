import Mathlib

-- # The Nilradical

section Nilradical

/-
Goal: The nilradical is an Ideal contained in the intersection of all prime ideals.
-/



-- An element of a Ring is Nilpotent if  ∃ n:ℕ , x^n = 0
#print IsNilpotent


-- ### Classes

/- A Semigroup is a type /set/ with extra attached information:
 - A multiplication operation
 - Which is associatiove -/
#print Semigroup

-- When I write
variable (S : Type) [Semigroup S]
-- What I'm saying is that S is a type with attached functions



/- Since a b c are in a Semigroup, I can apply the
   Semigroup.mul_assoc, whithout having to remember
   where it comes from -/

variable (a b c : S)
#check Semigroup.mul_assoc a b c




-- ### {Braced} parameters

-- Example
lemma sum_pos        (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :a+b>0 := by bound
lemma sum_pos_braces {a b : ℝ} (ha : a > 0) (hb : b > 0) :a+b>0 := by bound

#check sum_pos 3 2 three_pos two_pos
#check sum_pos_braces three_pos two_pos

-- By using @, we can make the inferred values explicit
#check @sum_pos_braces 3 2 three_pos two_pos


-- ### Into the Nilradical

variable (R : Type) [CommRing R] (x y : R)

/-- Element * Nilpotent = Nilpotent -/
lemma mul_nilpotent (a b : R) (hb : IsNilpotent b) :
    IsNilpotent (a * b) := by sorry



/-- Sum of nilpotents is nilpotent -/

lemma nilpotent_add {a b : R} (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (a + b) := by
    sorry

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
/-
Lean Ideals (actual implementation)
  - An Ideal I of R is a submodule of R as an R-module
-/

#print Ideal
#print Submodule

def nilrad : Ideal R where
  carrier := {a : R | IsNilpotent a}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' s t := by sorry


/-- Nilpotents -/


lemma primeIdeal_contains_IsNilpotent_mem
  {R : Type} [CommRing R]
  {I : Ideal R} (hI : Ideal.IsPrime I)
  {a : R} {n : ℕ} (ha : a ^ n ∈ I) :
    a ∈ I := by
    sorry


theorem nilrad_subset_of_Prime
  {I : Ideal R} (hI : I.IsPrime) :
  nilrad R ≤ I := by sorry
