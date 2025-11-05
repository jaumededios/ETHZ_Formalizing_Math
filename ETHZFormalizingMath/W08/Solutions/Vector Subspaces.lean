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
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    rw [Set.mem_preimage, LinearMap.map_zero]
    exact zero_mem H
  add_mem' := by
    rintro a b ha hb
    rw [Set.mem_preimage, LinearMap.map_add]
    exact Submodule.add_mem H ha hb
  smul_mem' := by
    rintro a v hv
    rw [Set.mem_preimage, map_smul]
    exact H.smul_mem a hv

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
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
  | mem x h =>
    cases h with
    | inl l =>
      use x, l, 0, Submodule.zero_mem T
      module
    | inr r =>
      use  0, Submodule.zero_mem S, x, r
      module
  | zero =>
      use 0, S.zero_mem, 0, T.zero_mem
      module
  | add x y hx hy hx' hy' =>
      rcases hx' with ⟨s, hs, t, ht,x_eq⟩
      rcases hy' with ⟨s', hs', t', ht',y_eq⟩
      use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
      rw [x_eq, y_eq]
      module
  | smul a x hx hx' =>
      rcases hx' with ⟨s, hs, t, ht, t_eq⟩
      rw [t_eq]
      use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
      module

open Function LinearMap

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

-- ## The kernel of a module

#check LinearMap.mem_ker
example : Injective φ ↔ ker φ = ⊥ := by
  constructor
  case mp =>
    intro inj
    ext x
    constructor
    case mp =>
      intro x_ker
      rw[(LinearMap.map_eq_zero_iff φ inj).mp x_ker]
      module
    case mpr =>
      intro x_in_bot
      have : φ x = φ 0 := by simp_all only [Submodule.mem_bot, map_zero]
      have : x=0       := by exact inj this
      simp only [this, zero_mem]
  case mpr =>
    intro ker_trivial  x y hphi
    have diff: (x - y) ∈ (⊥:Submodule K V) := by rw[← ker_trivial]; simp [map_sub, sub_self, hphi]
    simp_all only [Submodule.mem_bot]
    rw [eq_of_sub_eq_zero diff]
