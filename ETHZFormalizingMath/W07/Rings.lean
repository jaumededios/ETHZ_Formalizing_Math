import Mathlib

#check Ring

#check Units ℤ
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x


example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance

variable (R S : Type*) [Ring R] [Ring S]
#check RingHom R S
#check RingEquiv R S


universe u v

-- Modules over a Ring
section Module



class Module' (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x -- right distributivity
  zero_smul : ∀ x : M, (0 : R) • x = 0

-- Example: Vector space
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module' K V]

example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

end Module



section Subspaces

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure Submodule' (K : Type u) (V : Type v) [Semiring K] [AddCommMonoid V] [Module K V] : Type v
    extends AddSubmonoid V, SubMulAction K V

-- ℝ is an ℝ-linear subspace of ℂ
noncomputable example : Submodule ℝ ℂ := sorry

-- Example: Pre-image of a subspace by a linear map
def comap' {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V := sorry
