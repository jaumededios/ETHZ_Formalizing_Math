import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

-- # Metric spaces: Back to the begining

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace


-- ## Balls


variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

-- ## Continuity, sequences

-- Proof idea
#check Metric.nhds_basis_ball
-- Which follows from
#check Metric.isOpen_iff

-- Or more explicitly
#check Metric.nhds_basis_ball.mem_iff
#check Metric.nhds_basis_closedBall.mem_iff

-- The fancy filter-based definitions go back to the usual ones

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

-- # Examples

-- ## Composition of functions


example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity


example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
    have :(fun p : X × X ↦ dist (f p.1) (f p.2)) = dist.uncurry ∘ (fun x: X × X ↦ (f x.1, f x.2))
     :=  by tauto
    rw [this]
    apply Continuous.comp
    · exact continuous_dist
    · apply Continuous.prodMk
      · apply Continuous.comp hf continuous_fst
      · apply Continuous.comp hf continuous_snd


example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  Continuous.comp continuous_dist ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  · exact hf.comp continuous_fst
  · exact hf.comp continuous_snd




example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) := by
  apply Continuous.comp hf (Continuous.add (continuous_pow 2) continuous_id)


-- ## Closed sets

#check IsClosed
#check closure

example {s : Set X} : (a ∈ s) →  a ∈ (closure s) := by
  intro ha;
  unfold closure; simp;
  tauto

example {s : Set X} : IsClosed (closure s):= by
  unfold closure;
  refine isClosed_sInter ?_;
  intro t ⟨h1,h2⟩; exact h1


#check Metric.mem_closure_iff
#check Metric.tendsto_atTop

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s := by
    rw [Metric.mem_closure_iff]
    rw [Metric.tendsto_atTop] at hu
    intro ε hε
    rcases hu ε hε with ⟨N, hN⟩
    use (u N), (hs N)
    rw[dist_comm]
    use (hN N (by tauto))



-- Of course we could have used stuff from the library
-- IsClosed.mem_of_tendsto

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  IsClosed.mem_of_tendsto hs hu (Eventually.of_forall hus)


-- # Compactness


example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

-- ## Uniform continuity
example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff


#check eq_empty_or_nonempty
#check isClosed_le
#check IsClosed.isCompact
#check  IsCompact.exists_isMinOn

example
  {X : Type*} [MetricSpace X] [CompactSpace X]
  {Y : Type*} [MetricSpace Y] {f : X → Y}
  (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε ε_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  have φ_cont : Continuous φ := hf.fst'.dist hf.snd'
  let K := { p : X × X | ε ≤ φ p }
  have K_closed : IsClosed K := isClosed_le continuous_const φ_cont
  have K_cpct : IsCompact K := K_closed.isCompact
  rcases eq_empty_or_nonempty K with hK | hK
  · use 1, by norm_num
    intro x y _
    have : (x, y) ∉ K := by simp [hK]
    exact lt_of_not_ge this
  · rcases K_cpct.exists_isMinOn hK continuous_dist.continuousOn with ⟨⟨x₀, x₁⟩, xx_in, H⟩
    use dist x₀ x₁
    constructor
    · have : dist (f x₀) (f x₁) ≥ ε := by simp_all only [gt_iff_lt, mem_setOf_eq, ge_iff_le, φ, K]
      have : (f x₀) ≠ (f x₁) := by intro eqf; apply dist_eq_zero.mpr at eqf; grind
      have : x₀ ≠ x₁ := by exact fun a ↦ this (congrArg f a)
      exact dist_pos.mpr this
    · intro x x'
      contrapose!
      intro hyp
      have : (x,x')∈ K := by simp_all only [gt_iff_lt, mem_setOf_eq, φ, K]
      exact H this



-- ## Cauchy sequences

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

-- ## Uniform continuity
example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff


#check eq_empty_or_nonempty
#check isClosed_le
#check IsClosed.isCompact
#check  IsCompact.exists_isMinOn

example
  {X : Type*} [MetricSpace X] [CompactSpace X]
  {Y : Type*} [MetricSpace Y] {f : X → Y}
  (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε ε_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  have φ_cont : Continuous φ := hf.fst'.dist hf.snd'
  let K := { p : X × X | ε ≤ φ p }
  have K_closed : IsClosed K := isClosed_le continuous_const φ_cont
  have K_cpct : IsCompact K := K_closed.isCompact
  rcases eq_empty_or_nonempty K with hK | hK
  · use 1, by norm_num
    intro x y _
    have : (x, y) ∉ K := by simp [hK]
    exact lt_of_not_ge this
  · rcases K_cpct.exists_isMinOn hK continuous_dist.continuousOn with ⟨⟨x₀, x₁⟩, xx_in, H⟩
    use dist x₀ x₁
    constructor
    · have : dist (f x₀) (f x₁) ≥ ε := by simp_all only [gt_iff_lt, mem_setOf_eq, ge_iff_le, φ, K]
      have : (f x₀) ≠ (f x₁) := by intro eqf; apply dist_eq_zero.mpr at eqf; grind
      have : x₀ ≠ x₁ := by exact fun a ↦ this (congrArg f a)
      exact dist_pos.mpr this
    · intro x x'
      contrapose!
      intro hyp
      have : (x,x')∈ K := by simp_all only [gt_iff_lt, mem_setOf_eq, φ, K]
      exact H this



-- ## Cauchy sequences

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu
