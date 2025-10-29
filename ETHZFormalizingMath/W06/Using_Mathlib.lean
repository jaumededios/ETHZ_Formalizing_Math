/-
Reduced+updated version of Jireh Loeraux's talk on
LFTCM 2024: Using Mathlib - You can find it on youtube
-/

import Mathlib

#eval 0

/-!
## Tools for finding results in Mathlib:

+ [The undergrad list](https://leanprover-community.github.io/undergrad.html)
  gives some sense of what is available in Mathlib, but it's not exhaustive.

+ [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
  is great reference, but you either need to know where to look, or what things are
  named. To help with naming, you can reference the
  [naming conventions](https://leanprover-community.github.io/contribute/naming.html).

+ [Loogle](https://loogle.lean-lang.org) is useful if you know somehings about the types appearing
  in the statement.

+ [Moogle](https://moogle.ai) or [LeanSearch](https://leansearch.net) is useful if you only know
  the natural language phrasing.

+ [Zulip](https://leanprover.zulipchat.com‌/) in the `Is there code for X?` stream is a good place
  to ask for help.

+ The `exact?` or `apply?` tactic, when the theorem in question is definitely there,
  but you don't know the name. Powerful when combined with "have".
-/

-- ## Example 1: Real.sqrt

example (x : ℝ) : x.sqrt ^ 2 = x := by
  -- exact? -- fails very slowly, we forgot a hypothesis
  -- apply? Tells us
  sorry


open scoped Real in
example : Real.sqrt π ^ 2 = π := by sorry

/-
We can search for this with Loogle as well in the following ways:

* [`sqrt, ?x ^ 2`](https://loogle.lean-lang.org/?q=sqrt%2C+%3Fx+%5E+2)
  returns "unknown identifier `sqrt`", so we should use `Real.sqrt` instead.
+ [`Real.sqrt`](https://loogle.lean-lang.org/?q=Real.sqrt) 252 hits, our result is #37
+ [`Real.sqrt, ?x ^ 2`](https://loogle.lean-lang.org/?q=Real.sqrt%2C+%3Fx+%5E+2)
  returns all theorems involving `Real.sqrt` and `?x ^ 2`, but many more besides the one we want
+ [`⊢ Real.sqrt ?x ^ 2 = ?x`](https://loogle.lean-lang.org/?q=⊢+Real.sqrt+%3Fx+%5E+2+%3D+%3Fx)
  returns a result with this type in the conclusion, the only hit is the result we want.
-/



/-! ### Example 3: ​If the number of vectors exceeds the dimension, the set is linearly dependent

Moogle [​If the number of vectors exceeds the dimension, the set is linearly dependent](https://www.moogle.ai/search/raw?q=If%20the%20number%20of%20vectors%20exceeds%20the%20dimension%2C%20the%20set%20is%20linearly%20dependent)

* almost no useful results, execpt we do know that `LinearIndependent` exists, but that
  `LinearDependent` does not seem to.
* closest result is: `exists_linearIndependent_cons_of_lt_rank`
* also has: `linearIndependent_iff_card_eq_finrank_span`

We realize that Mathlib talks about `rank` and `finrank`, but not `dimension`.
-/

#check linearIndependent_iff_card_le_finrank_span
#check LinearIndependent
#check Module.rank
#check Module.finrank
#check linearIndependent_iff_card_eq_finrank_span

-- One attempted formalization, actually invalid unless we add that `V` is finite-dimensional
-- Because `Module.finrank` takes the junk value `0` if `V` is not finite-dimensional.

example {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] {b : ι → V} (h : Module.finrank K V < Fintype.card ι) :
    ¬ LinearIndependent K b :=
  sorry

/-
Let's keep looking.

Loogle: [`LinearIndependent, Module.rank`](https://loogle.lean-lang.org/?q=LinearIndependent%2C+Module.rank)

This yields things like:

-/
universe u v w
#check LinearIndependent.cardinal_le_rank
#check le_rank_iff_exists_linearIndependent_finset
#check le_rank_iff_exists_linearIndependent

-- another formalization, this time not requiring finitely many vectors
example {R : Type u} {M : Type w} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial R]
    {ι : Type w} {v : ι → M} (h : Module.rank R M < Cardinal.mk ι) : ¬ LinearIndependent R v := by
  contrapose h
  simp_all
  exact? says exact LinearIndependent.cardinal_le_rank h

-- an alternate proof of the same fact
example {R : Type u} {M : Type w} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial R]
    {ι : Type w} {v : ι → M} (h : Module.rank R M < Cardinal.mk ι) : ¬ LinearIndependent R v := by
  apply mt LinearIndependent.cardinal_le_rank
  exact? says exact not_le_of_gt h

/- Searching the Mathlib docs for `linearindependent le finrank` yields the following as the
third hit. Note: when searching the documentation, prefer lowercase do not add `_` or `.`. Using
lowercase will match case-insensitively. The search matches substrings. -/
#check LinearIndependent.fintype_card_le_finrank

lemma foo {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] [StrongRankCondition R]
    [Module.Finite R M] {ι : Type u} [Fintype ι] {b : ι → M}
    (h : Module.finrank R M < Fintype.card ι) :
    ¬ LinearIndependent R b := by
  contrapose h
  simp_all
  exact? says exact LinearIndependent.fintype_card_le_finrank h

-- If a set in `ℝⁿ` has more than `n` vectors, then it is linearly dependent.
example (n : ℕ) (s : Finset (Fin n → ℝ)) (h : s.card > n) :
    ¬ LinearIndependent ℝ ((↑) : s → Fin n → ℝ) := by
  contrapose h
  simp_all
  have := h.finset_card_le_finrank -- this is slightly different than the one we found above!
  simpa

-- Given three specific vectors in `ℝ²`, they are linearly dependent.
example : ¬ LinearIndependent ℝ (![![1, 0], ![1, 1], ![0, 1]] : Fin 3 → (Fin 2 → ℝ)) := by
  apply foo
  simp


/-! ### Example 4: Moogle wins first hit!  -/

-- the transition matrix between orthonormal bases is unitary
#check OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
-- every natural number is the sum of four squares
#check Nat.sum_four_squares
-- open mapping theorem
#check ContinuousLinearMap.isOpenMap
-- closed graph theorem
#check LinearMap.continuous_of_isClosed_graph
-- Hahn Banach extension theorem
#check exists_extension_of_le_sublinear
#check Real.exists_extension_norm_eq
-- Hahn Banach separation theorem
#check geometric_hahn_banach_open
#check geometric_hahn_banach_compact_closed
#check ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem
