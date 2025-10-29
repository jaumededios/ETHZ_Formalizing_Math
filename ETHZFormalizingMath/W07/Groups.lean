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

def timesTwo : AddMonoidHom ℕ ℕ := sorry


-- # Groups

#check Group


-- Two tactics: group and abel

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by sorry

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by sorry

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

example : AddSubgroup ℚ := sorry


-- Exercise: Conjugating a subgroup


def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G := sorry

--  Preimage (comap) of a subgroup

def comap {G G' : Type*} [Group G] [Group G'] (f: G →* G') (H': Subgroup G') : Subgroup G := sorry



variable {G G' : Type*} [Group G] [Group G'] {H : Subgroup G'} {f : G →* G'}

-- Groups are a Lattice! (there is a ≤ operation, a ⊓ and a ⊔ operations)

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := sorry


example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ (S⊓T) = comap φ (S) ⊓ comap φ (T) := sorry


-- # Group Actions

example {G X : Type*} [Group G] [MulAction G X] (g g' : G) (x : X) :
  -- •
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm


-- # Quotient Groups
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H
