import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

open Set Filter Topology


-- # What are filters?

#check Filter
-- Based on [N. Bourbaki, *General Topology*][bourbaki1966]

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α` => Unlike Bourbaki!. -/

structure Filter' (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

--## Examples

-- The Principal Filter (\MCP, Filter.principal)
example {α : Type*} (s : Set α) : Filter α := 𝓟 s

-- The "Big Things" filter
example : Filter ℕ := atTop

-- This is not the definition of atTop but to get some intuition
def atTop' {α : Type*} [Inhabited α] [Lattice α] : Filter α where
  sets := {p |  ∃ lb , ∀ a:α,  lb≤a → a ∈ p}
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry


-- The Neighborhood Filter (\MCN \nhds)
example (X : Type) [TopologicalSpace X] (x : X) : Filter X := 𝓝 x

variable (X : Type)
#synth CompleteLattice (Filter X)


-- # Filters express the notion of limit

-- ## x tends to y

-- Definition
-- F tends to y near x if the pre-image of every Neighborhood of y contains a neighborhood of x

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

-- We can push forward filters via: preimage f⁻¹' myFilter.sets
variable (α β : Type*) (fa fa' : Filter α)


-- ## Maps of filters
-- The forward map of a filter
#check Filter.map

def map' (m : α → β) (f : Filter α) : Filter β  := _

-- Filters have a Partial order
#synth PartialOrder (Filter α)
-- But it's the wrong one
example : fa ≤ fa' ↔ fa.sets ⊇ fa'.sets := by simp_all only [sets_subset_sets];

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G := Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := sorry

-- # Filter operations

-- ## Comaps of filters

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

-- Comap is the family of sets "Bigger than the preimage"
#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)


variable {α β γ : Type*} (F G : Filter α) {m : γ → β} {n : β → α}

example (comap_comap : comap m (comap n F) = comap (n ∘ m) F) := by tauto

-- Maps and comaps are related:

#check map_le_iff_le_comap

-- ## Sups and infs of Filters

#check F⊔G
#check F⊓G


-- ## Products via comaps and infs

example : 𝓝 (x₀, y₀) = (𝓝 x₀) ×ˢ (𝓝 y₀) := nhds_prod_eq

-- Let's try to construct the product
-- example : (𝓝 x₀) ×ˢ (𝓝 y₀) := sorry

#check le_inf_iff




example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by sorry

-- # Basis of Filters

#check HasBasis

-- Open sets containing x₀ are a basis of 𝓝 x₀
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) (fun ε ↦ Ioo  (x₀ - ε) (x₀ + ε)) :=
  nhds_basis_Ioo_pos x₀
example : HasBasis atTop (fun _ : ℕ ↦ True) Ici := atTop_basis

-- TendsTo (and inequalities of filters in general) can be turned into inequalities of basis
#check HasBasis.tendsto_iff


-- Now we can write some "Not nonsense" mathematics
example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  sorry

-- # Eventually

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  Eventually.and  hP hQ

example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

-- We can define "eventual equality"
example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

#check Eventually.of_forall
#check Eventually.mono
#check Eventually.and

-- This is called Eventually.mp
example {α : Type*} {p q : α → Prop} {f : Filter α} (hp : ∀ᶠ (x : α) in f, p x)
  (hpq : ∀ᶠ (x : α) in f, p x → q x) : ∀ᶠ (x : α) in f, q x :=
  Eventually.mono (Eventually.and hp hpq) (by tauto)
#check Eventually.mp

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := sorry


example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  -- filter_upwards [hP, hQ, hR]
  sorry
