import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
open Polynomial Module LinearMap End




variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {W : Type*} [AddCommGroup W] [Module K W]


-- # The algebra of endomorphisms


abbrev Module.End' (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] M


variable {K : Type*} [Field K]
  {V : Type*} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]

-- Modules are a (non-commutative) ring! \
example (φ ψ : Module.End K V) : φ * ψ = φ ∘ₗ ψ :=
  End.mul_eq_comp φ ψ

-- In fact they are an algebra over the base field
example (P : Polynomial K) (φ : Module.End K V) : V →ₗ[K] V :=
  Polynomial.aeval φ P


open Polynomial

example (φ : Module.End K V) : Polynomial.aeval φ (X : K[X]) = φ :=
  aeval_X φ


-- IsCoprime means there exist u v with up+vq = 1!
example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  sorry


/- # Eigenspace, -vectors, -values-/

variable {K R : Type*} {V M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]

-- Generalized Eigenspace
def genEigenspace' (f : Module.End R M) (μ : R) : ℕ∞ →o Submodule R M where
  toFun k := ⨆ l : ℕ, ⨆ _ : l ≤ k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi ↦ hi.trans hkl

-- Eigenspace as a special case
abbrev eigenspace' (f : Module.End R M) (μ : R) : Submodule R M :=
  genEigenspace' f μ 1 -- k = 1

-- Eigenspace is ker(φ - a • 1)
example (φ : Module.End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  Module.End.eigenspace_def

-- Eigenvalue
example (φ : Module.End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

-- set of eigenvalues
example (φ : Module.End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalues are roots of the minimal polynomial
example (φ : Module.End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : Module.End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
