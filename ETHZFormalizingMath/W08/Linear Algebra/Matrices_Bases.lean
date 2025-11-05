import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Data.Real.Basic
open Polynomial Module LinearMap End



-- # Matrices

open Matrix


-- Adding vectors
#eval ![1, 2] + ![3, 4]  -- ![4, 6]

-- Adding matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplying matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![13, 16; 29, 36]


-- matrices acting on vectors on the left
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- matrices acting on vectors on the left, resulting in a size one matrix
#eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- matrices acting on vectors on the right
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]

-- vector dot product
#eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- matrix transpose \^T
#eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- determinant
#eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- trace
#eval !![(1 : ℤ), 2; 3, 4].trace -- `5`

-- inverse
example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp


-- ## What are matrices?

-- Fin n is the "canonical" type of n elements
example : (fun _ _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num

example : (fun _ _ ↦ 1 : Fin 2 → Fin 2 → ℤ) *(fun _ _ ↦ 1) = (fun _ _ ↦ 1) := by
  ext x y
  simp

def Matrix.vandermonde {n : ℕ} (v : Fin n → ℝ) :=
     Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ))


-- # Basis


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


-- A basis is a map from the "index set" to the vector space with special properties
variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)


-- The basis vector with index ``i``
#check (B i : V)

-- the linear isomorphism with the model space given by ``B``
-- The special property is repr: \finsupp →₀
-- There is an isomorphism from V to "Finitely supported functions from ι to K"
def MyBasis : Basis ι K V where
  repr := sorry
#check (B.repr : V ≃ₗ[K] ι →₀ K)

-- the component function of ``v``
#check (B.repr v : ι →₀ K)

-- the component of ``v`` with index ``i``
#check (B.repr v i : K)

open LinearMap Matrix


-- Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
#check toMatrix_comp
#check id_comp
#check comp_id
#check toMatrix_id

-- Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.
#check Matrix.det_mul
#check Matrix.det_one

example [Fintype ι] [DecidableEq ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
  sorry
