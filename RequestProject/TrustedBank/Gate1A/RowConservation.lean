import Mathlib

/-!
# Gate 1A — M-row conservation (finite-dimensional Hilbert bank)

Abstract, purely linear-algebraic content: if a family of vectors is built by
multiplying a fixed scalar *row weight* `w m` into a vector `x μ`, then the total
`ℓ²` mass factors exactly as

```
∑_μ ‖X μ‖² = (∑_m |w m|²) · (∑_μ ‖x μ‖²).
```

We then prove that this total mass is *invariant* under

* coordinate permutations of the row index,
* unitary maps applied to the vector factor,
* orthogonal direct-sum relabelling of the row index,
* diagonal unit-modulus multipliers.

The only thing established is: **reorganisation does not erase the row `L²` mass.**
Nothing here says anything about whether `SOURCE-AVG-JDR` is provable or impossible;
Gate 1A remains **OPEN**.
-/

open scoped BigOperators

namespace TrustedBank
namespace Gate1A

variable {ι ν μ : Type*}

/-- The row-weighted family: `rowVec w x (m, n) = w m * x n`. -/
def rowVec (w : ι → ℂ) (x : ν → ℂ) : ι × ν → ℂ := fun p => w p.1 * x p.2

/-- Squared `ℓ²` mass of a finitely supported family of complex scalars. -/
noncomputable def massSq [Fintype ι] (f : ι → ℂ) : ℝ := ∑ i, ‖f i‖ ^ 2

@[simp] lemma massSq_apply [Fintype ι] (f : ι → ℂ) : massSq f = ∑ i, ‖f i‖ ^ 2 := rfl

lemma massSq_nonneg [Fintype ι] (f : ι → ℂ) : 0 ≤ massSq f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Row-mass factorization for one vector.** -/
theorem massSq_rowVec [Fintype ι] [Fintype ν] (w : ι → ℂ) (x : ν → ℂ) :
    massSq (rowVec w x) = massSq w * massSq x := by
  simp only [massSq_apply, rowVec, Fintype.sum_prod_type, norm_mul, mul_pow,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- **M-row conservation.**  For a whole family `x : μ → ν → ℂ` of vectors, the total
squared mass of the row-weighted vectors factors exactly. -/
theorem total_massSq_rowVec [Fintype ι] [Fintype ν] [Fintype μ]
    (w : ι → ℂ) (x : μ → ν → ℂ) :
    ∑ m : μ, massSq (rowVec w (x m)) = massSq w * ∑ m : μ, massSq (x m) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => massSq_rowVec w (x m)

/-- The row mass is not erased: if the row weights carry positive mass and the vectors
carry positive mass, the row-weighted family carries positive mass. -/
theorem total_massSq_pos [Fintype ι] [Fintype ν] [Fintype μ]
    (w : ι → ℂ) (x : μ → ν → ℂ) (hw : 0 < massSq w) (hx : 0 < ∑ m : μ, massSq (x m)) :
    0 < ∑ m : μ, massSq (rowVec w (x m)) := by
  rw [total_massSq_rowVec]; exact mul_pos hw hx

/-! ## Invariance under reorganisation -/

/-- Invariance of the row mass under a permutation of the row index. -/
theorem massSq_comp_equiv [Fintype ι] {ι' : Type*} [Fintype ι'] (e : ι' ≃ ι) (w : ι → ℂ) :
    massSq (w ∘ e) = massSq w := by
  simp only [massSq, Function.comp_apply]
  exact e.sum_comp fun i => ‖w i‖ ^ 2

/-- Invariance of the row mass under a diagonal unit-modulus multiplier. -/
theorem massSq_diagonal_unit [Fintype ι] (u w : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    massSq (fun i => u i * w i) = massSq w := by
  simp [massSq, hu]

/-- Invariance of the total mass under an orthogonal direct-sum relabelling of the row
index: splitting the rows into two blocks adds the two block masses. -/
theorem massSq_sum_type [Fintype ι] {ι' : Type*} [Fintype ι'] (w : ι ⊕ ι' → ℂ) :
    massSq w = massSq (fun i => w (Sum.inl i)) + massSq (fun i => w (Sum.inr i)) := by
  simp [massSq, Fintype.sum_sum_type]

/-- Invariance of the vector mass under a unitary (linear isometry) map. -/
theorem massSq_unitary [Fintype ν] [Fintype μ]
    (U : EuclideanSpace ℂ ν ≃ₗᵢ[ℂ] EuclideanSpace ℂ ν) (x : μ → EuclideanSpace ℂ ν) :
    ∑ m : μ, ‖U (x m)‖ ^ 2 = ∑ m : μ, ‖x m‖ ^ 2 := by
  simp [U.norm_map]

/-- **Summary theorem (row mass is conserved by reorganisation).**  Permuting rows,
applying a diagonal unit-modulus multiplier, or both, leaves the total row-weighted
mass unchanged and equal to the factorized value. -/
theorem total_massSq_reorganisation_invariant [Fintype ι] [Fintype ν] [Fintype μ]
    (w u : ι → ℂ) (e : ι ≃ ι) (x : μ → ν → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    ∑ m : μ, massSq (rowVec (fun i => u i * w (e i)) (x m))
      = massSq w * ∑ m : μ, massSq (x m) := by
  rw [total_massSq_rowVec, massSq_diagonal_unit _ _ hu]
  congr 1
  exact massSq_comp_equiv (ι := ι) e w

end Gate1A
end TrustedBank
