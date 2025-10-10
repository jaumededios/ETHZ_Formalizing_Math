import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Bound

section Continuous

variable {X Y Z T : Type}
         [MetricSpace X] [MetricSpace Y]
         [MetricSpace Z] [MetricSpace T]


#synth  MetricSpace (X × Y)
variable (x1 x2 : X) (y1 y2 : Y)
#check dist (x1, y1) (x2, y2)

def Continuous_at (x : X) (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (y : X), dist x y < δ → dist (f x) (f y) < ε

theorem Comp_Continuous {x : X} {f : X → Y} {g : Y → Z}
    (hf : Continuous_at x f) (hg : Continuous_at (f x) g) :
    Continuous_at x (g ∘ f) := by
  unfold Continuous_at
  intro ε εpos
  rcases  hg ε εpos with ⟨δg, δgpos, gineq⟩
  obtain ⟨δf, δfpos, fineq⟩ :=  hf δg δgpos
  use δf, δfpos
  simp_all

def FProd (f : X → Y) (g : Z → T) := (fun (x, z) => (f x, g z))

theorem Prod_Continuous {f : X → Y} {g : Z → T} {x : X} {z : Z}
    (hf : Continuous_at x f) (hg : Continuous_at z g) :
    Continuous_at (x,  z) (FProd f g) := by
  unfold Continuous_at
  intro ε εpos
  rcases hf ε εpos with ⟨δf, δfpos, fclose⟩
  rcases hg ε εpos with ⟨δg, δgpos, gclose⟩
  use (min δf δg), lt_min δfpos δgpos
  simp_all [Prod.dist_eq, FProd]

def Diag {A : Type} : (A → A × A) := (fun a => (a,a))

theorem Diag_Continuous (x : X) : Continuous_at x Diag := by
  intro ε εpos
  use ε, εpos
  simp [Diag,Prod.dist_eq]

def R_add : ℝ×ℝ → ℝ := fun (a,b) ↦ a+b

theorem R_add_continuous_at (v : ℝ × ℝ) : Continuous_at v R_add := by
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

theorem add_cont_at {f g : ℝ → ℝ} {x : ℝ} (hf : Continuous_at x f) (hg : Continuous_at x g) :
    Continuous_at x (f+g) := by
  let R_add: ℝ×ℝ → ℝ := fun (a,b) ↦ a+b
  let fg := FProd f g
  have comp_eq : f+g = R_add ∘ (fg ∘ Diag):= by
    simp_all only [R_add, fg]
    rfl
  rw [comp_eq]
  apply Comp_Continuous
  · exact Comp_Continuous (Diag_Continuous x) (Prod_Continuous hf hg)
  · exact R_add_continuous_at ((fg ∘ Diag) x)

-- New stuff

def R_sub : ℝ × ℝ → ℝ := fun (a,b) ↦ a - b

def lin (m : ℝ) : ℝ → ℝ := fun x ↦ m * x

theorem lin_cont_at (m : ℝ) (x : ℝ) : Continuous_at x (lin m) := by
  intro ε hε
  rcases ne_or_eq m 0 with h0 | h1
  · use ε / 2 * 1 / abs m, by field_simp; bound
    intro y hd
    simp_all only [lin, Real.dist_eq, ← mul_sub m x, abs_mul]
    grw [hd]
    field_simp
    exact one_lt_two
  · simp [h1, lin]
    aesop

theorem R_sub_continuous_at (v : ℝ × ℝ) : Continuous_at v R_sub := by
  convert_to Continuous_at v (R_add ∘ FProd (lin 1) (lin (-1)))
  · funext v
    simp [R_sub, R_add, FProd, lin]
    ring
  · apply Comp_Continuous
    · exact Prod_Continuous (lin_cont_at 1 v.1) (lin_cont_at (-1) v.2)
    · exact R_add_continuous_at (FProd (lin 1) (lin (-1)) v)

def square (x : ℝ) := x ^ 2

theorem sq_cont_at (x : ℝ) : Continuous_at x square := by
  intro ε hε
  use min 1 (ε / (2 * (1 + 2 * |x|))), by positivity
  intro y hd
  simp_rw [lt_inf_iff, dist] at hd
  simp_rw [dist, square, sq_sub_sq, abs_mul]
  calc
    |x + y| * |x - y| ≤ |x + y| * (ε / (2 * (1 + 2 * |x|))) := by gcongr; bound
    _ = |y - x + 2 * x| * (ε / (2 * (1 + 2 * |x|))) := by grind
    _ ≤ (|y - x| + |2 * x|) * _ := by gcongr; exact abs_add_le _ _
    _ = (|x - y| + 2 * |x|) * _ := by rw [abs_sub_comm, abs_mul, Nat.abs_ofNat]
    _ ≤ (1 + 2 * |x|) * _ := by gcongr; nlinarith;
    _ < ε := by field_simp; exact one_lt_two

theorem polarization_identity (x y : ℝ) : x * y = ((x + y) ^ 2 - (x - y) ^ 2) / 4 := by ring

def mul : ℝ × ℝ → ℝ := fun (y, z) ↦ y * z

theorem Fpolarization :
    mul = lin (1 / 4) ∘ R_sub ∘ (FProd (square ∘ R_add) (square ∘ R_sub) ∘ Diag) := by
  unfold mul
  funext v
  simp [polarization_identity, Diag, FProd, R_add, R_sub, square, lin, Diag]
  ring

example (x : ℝ × ℝ) : Continuous_at x mul := by
  convert_to Continuous_at x (lin (1 / 4) ∘ R_sub ∘ FProd (square ∘ R_add) (square ∘ R_sub) ∘ Diag)
  · unfold mul
    funext v
    simp [polarization_identity, Diag, FProd, R_add, R_sub, square, lin, Diag]
    ring
  · grind [Comp_Continuous, Diag_Continuous, Prod_Continuous,
     R_add_continuous_at, R_sub_continuous_at, sq_cont_at, lin_cont_at, FProd, R_sub]
    /- Or if you want to grind yourself:
    repeat apply Comp_Continuous
    · exact Diag_Continuous x
    · apply Prod_Continuous
      · exact Comp_Continuous (R_add_continuous_at _) (sq_cont_at _)
      · exact Comp_Continuous (R_sub_continuous_at _) (sq_cont_at _)
    · exact R_sub_continuous_at ((FProd (square ∘ R_add) (square ∘ R_sub) ∘ Diag) x)
    · exact lin_cont_at _ _
    -/

end Continuous
