import Mathlib

-- # Monoids


#check Monoid
#check CommMonoid
#check AddCommMonoid


example {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (f : MonoidHom M N) (g : N →* P) : M →* P := g.comp f

-- Monoid Morphisms

#check MonoidHom


example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

def timesTwo : AddMonoidHom ℕ ℕ where
  toFun := fun x ↦ x*2
  map_zero' := by group
  map_add' :=  by intro a b; group



-- # Groups

#check Group


-- Two tactics: group and abel

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

-- ## Group homeomorphisms

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

-- Group isomorphisms

-- ≃*

variable {G G' : Type*} [Group G] [Group G']

#check G ≃* G'
#check MulEquiv G G'


-- ## Subgroups

#check Subgroup

example : AddSubgroup ℚ where
  -- Set.range ((↑) : ℤ → ℚ)
  carrier := {x:ℚ | ∃ x':ℤ, x  = x'}
  add_mem' := by
    rintro a b ⟨az,haz⟩ ⟨bz,hbz⟩
    use az+bz
    simp
    rw [haz, hbz]


  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp


-- Exercise: Conjugating a subgroup


def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    simp
    use 1
    constructor
    · exact Subgroup.one_mem H
    · group
  inv_mem' := by
    simp
    intro x_1 x_2 h2 h_inv
    use x_2⁻¹
    constructor
    · exact Subgroup.inv_mem H h2
    · rw[h_inv]
      group

  mul_mem' := by
    simp
    aesop

--  Preimage (comap) of a subgroup

def comap {G G' : Type*} [Group G] [Group G'] (f: G →* G') (H': Subgroup G') : Subgroup G where
  carrier := {a:G | f a ∈ H'}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simp at *; exact Subgroup.mul_mem H' ha hb
  inv_mem' := by intro a ha; simp at *; exact ha



variable {G G' : Type*} [Group G] [Group G'] {H : Subgroup G'} {f : G →* G'}

@[simp] lemma comap_def {x : G} : x ∈ comap f H ↔ f x ∈ H := by tauto

-- Groups are a Lattice! (there is a ≤ operation, a ⊓ and a ⊔ operations)

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  intro a ha
  simp at *
  tauto

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ (S⊓T) = comap φ (S) ⊓ comap φ (T) := by
  ext x
  constructor
  <;> intro hx
  <;> simp at *
  <;> tauto



noncomputable section GroupActions

example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm
