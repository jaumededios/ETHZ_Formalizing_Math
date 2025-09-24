import Mathlib




section Continuous

variable {X Y Z T: Type}
         [MetricSpace X] [MetricSpace Y]
         [MetricSpace Z] [MetricSpace T]

def Continuous_at (x : X) (f : X → Y) : Prop :=
  ∀ ε>0,∃ δ>0, ∀ (y:X), dist x y < δ → dist (f x) (f y) <ε

theorem Comp_Continuous (x : X) (f : X → Y) (g : Y → Z)
  (hf : Continuous_at x f) (hg : Continuous_at (f x) g) :
  Continuous_at x (g∘f) := by sorry

def FProd (f : X → Y) (g : Z → T) := (fun (x, z) => (f x, g z))

-- Hint: Using rw? or similar you should be able to find Prod.dist_eq
-- (I add the hint since it took me a couple of tries0
theorem Prod_Continuous (f : X → Y) (g : Z → T) (x : X) (z : Z)
  (hf : Continuous_at x f) (hg : Continuous_at z g) :
  Continuous_at (x,  z) (FProd f g) := by
  sorry


def Diag (A : Type) : (A → A × A):= (fun a => (a,a))

theorem Diag_Continuous (x : X) :
  Continuous_at x (Diag X)
    := by sorry

def R_add : ℝ×ℝ → ℝ := fun (a,b) ↦ a+b

theorem R_add_continuous_at (v : ℝ × ℝ) :
  Continuous_at v R_add := by
    sorry

variable (f : X → Y) (g : X → Y)

theorem add_cont (f g : ℝ → ℝ) (x : ℝ)
  (hf : Continuous_at x f)
  (hg : Continuous_at x g) :
  Continuous_at x (f+g)
  := by
    sorry

end Continuous
