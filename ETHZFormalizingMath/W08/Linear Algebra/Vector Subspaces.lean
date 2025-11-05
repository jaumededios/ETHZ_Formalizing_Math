import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic


universe u v

structure Submodule' (K : Type u) (V : Type v) [Semiring K] [AddCommMonoid V] [Module K V] : Type v
    extends AddSubmonoid V, SubMulAction K V


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


-- # The pre-image/comap of a sbmodule is a submodule

def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V := sorry

-- ## The span of a submodule

#check Submodule.span
#check Submodule.span_induction

#check Submodule.span_union
#check Submodule.span_eq

-- ## Sum (and intersection) of submodules (sup ⊔  and inf ⊓)


-- ## The span induction

#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check Submodule.mem_sup


example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by sorry

open Function LinearMap

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

-- ## The kernel of a module

#check LinearMap.mem_ker
example : Injective φ ↔ ker φ = ⊥ := by sorry
