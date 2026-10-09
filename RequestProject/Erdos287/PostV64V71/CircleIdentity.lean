import RequestProject.Erdos287.PostV64V71.WeightedCorrelation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Erdős #287 — V71 circle-method identity and exact major/minor decomposition

**Status: BANK (LEAN PROVED).**  Pure Fourier orthogonality on `[0,1]`; no analytic estimate.

* `eC x = exp(2πi x)`;
* `SM M K α = ∑_{n∈I} f_K(n) e(αn)`;
* `integral_eC_int` — `∫₀¹ e(hα) dα = [h = 0]` for `h ∈ ℤ`;
* `circle_correlation_identity` — `C_K(M) = ∫₀¹ 2 cos(2πα) |S_M(α)|² dα`;
* `majorArcs M Q` — the union of the closed arcs `|α - a/q| ≤ Q/M`, `1 ≤ q ≤ Q`, `0 ≤ a ≤ q`
  (the V71 choice is `Q = ⌊(log M)^12⌋₊`, `majorArcsV71`);
* `Cmajor`, `Cminor` — the set integrals of the circle integrand over `(0,1] ∩ 𝔐` and
  `(0,1] \ 𝔐`;
* `major_minor_exact_decomposition` — `C_K = C_major + C_minor` (exact; no estimate claimed).
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Erdos287.PostV64V71

/-- `e(x) = exp(2πi x)`. -/
noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

theorem eC_add (a b : ℝ) : eC a * eC b = eC (a + b) := by
  unfold eC; rw [← Complex.exp_add]; push_cast; ring_nf

theorem conj_eC (a : ℝ) : conj (eC a) = eC (-a) := by
  unfold eC; rw [← Complex.exp_conj]; congr 1
  simp [Complex.conj_ofReal, map_ofNat]

theorem continuous_eC_mul (c : ℝ) : Continuous fun α : ℝ => eC (α * c) := by
  unfold eC; fun_prop

theorem two_cos_eq (α : ℝ) : ((2 * Real.cos (2 * Real.pi * α) : ℝ) : ℂ) = eC α + eC (-α) := by
  unfold eC
  push_cast
  rw [Complex.cos]
  have h1 : (2 * Real.pi * α : ℂ) * Complex.I = 2 * Real.pi * Complex.I * α := by ring
  have h2 : -(2 * Real.pi * α : ℂ) * Complex.I = 2 * Real.pi * Complex.I * ((-α : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2]; push_cast; ring

/-- **Orthogonality**: `∫₀¹ e(hα) dα = [h = 0]` for `h ∈ ℤ`. -/
theorem integral_eC_int (h : ℤ) :
    ∫ α in (0 : ℝ)..1, eC (α * h) = if h = 0 then 1 else 0 := by
  split_ifs with h0
  · subst h0; simp [eC]
  · set c : ℂ := 2 * Real.pi * Complex.I * h with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast h0
    have hfun : (fun α : ℝ => eC (α * h)) = fun α : ℝ => Complex.exp (c * α) := by
      funext α; unfold eC; rw [hc]; push_cast; ring_nf
    rw [hfun, integral_exp_mul_complex hc0]
    have h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      rw [hc]; push_cast
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * 1 = (h : ℂ) * (2 * Real.pi * Complex.I)
        by ring]
      exact Complex.exp_int_mul_two_pi_mul_I h
    rw [h1]; simp

/-- `S_M(α) = ∑_{n∈I} f_K(n) e(αn)`. -/
noncomputable def SM (M K : ℕ) (α : ℝ) : ℂ := ∑ n ∈ Iset M, (fK K n : ℂ) * eC (α * n)

/-- The circle integrand `2 cos(2πα) |S_M(α)|²`. -/
noncomputable def circleIntegrand (M K : ℕ) (α : ℝ) : ℝ :=
  2 * Real.cos (2 * Real.pi * α) * ‖SM M K α‖ ^ 2

theorem continuous_SM (M K : ℕ) : Continuous (SM M K) := by
  unfold SM
  exact continuous_finset_sum _ fun n _ => continuous_const.mul (continuous_eC_mul n)

theorem continuous_circleIntegrand (M K : ℕ) : Continuous (circleIntegrand M K) := by
  unfold circleIntegrand
  have := continuous_SM M K
  fun_prop

/-- Pointwise expansion of the circle integrand. -/
theorem circleIntegrand_expand (M K : ℕ) (α : ℝ) :
    ((circleIntegrand M K α : ℝ) : ℂ) =
      ∑ n ∈ Iset M, ∑ m ∈ Iset M, ((fK K n * fK K m : ℝ) : ℂ) *
        (eC (α * (((n : ℤ) - m + 1 : ℤ) : ℝ)) + eC (α * (((n : ℤ) - m - 1 : ℤ) : ℝ))) := by
  unfold circleIntegrand
  rw [Complex.ofReal_mul, two_cos_eq, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold SM
  rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, Complex.conj_ofReal, conj_eC]
  have e3 : ∀ a b c : ℝ, eC a * eC b * eC c = eC (a + b + c) := fun a b c => by
    rw [eC_add, eC_add]
  have : (eC α + eC (-α)) * (↑(fK K n) * eC (α * ↑n) * (↑(fK K m) * eC (-(α * ↑m)))) =
      (fK K n : ℂ) * (fK K m) * (eC α * eC (α * n) * eC (-(α * m)) +
        eC (-α) * eC (α * n) * eC (-(α * m))) := by ring
  rw [this, e3, e3]
  push_cast
  congr 2
  · congr 1; ring
  · congr 1; ring

/-- The `(n, m)` term of the expanded circle integral. -/
theorem term_integral (K n m : ℕ) :
    ∫ α in (0 : ℝ)..1, ((fK K n * fK K m : ℝ) : ℂ) *
        (eC (α * (((n : ℤ) - m + 1 : ℤ) : ℝ)) + eC (α * (((n : ℤ) - m - 1 : ℤ) : ℝ))) =
      ((if Adj n m then fK K n * fK K m else 0 : ℝ) : ℂ) := by
  have hi : ∀ s : ℤ, IntervalIntegrable (fun α : ℝ => eC (α * ((s : ℤ) : ℝ))) volume 0 1 :=
    fun s => (continuous_eC_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi _) (hi _),
    integral_eC_int, integral_eC_int]
  unfold Adj
  by_cases h1 : n = m + 1
  · rw [if_pos (Or.inl h1), if_neg (by omega), if_pos (by omega)]
    simp
  · by_cases h2 : m = n + 1
    · rw [if_pos (Or.inr h2), if_pos (by omega), if_neg (by omega)]
      simp
    · rw [if_neg (show ¬ (n = m + 1 ∨ m = n + 1) by tauto),
        if_neg (show ¬ ((n : ℤ) - m + 1 = 0) by omega),
        if_neg (show ¬ ((n : ℤ) - m - 1 = 0) by omega)]
      simp

/-- **V71 circle-method identity**: `C_K(M) = ∫₀¹ 2 cos(2πα) |S_M(α)|² dα`. -/
theorem circle_correlation_identity (M K : ℕ) :
    CK M K = ∫ α in (0 : ℝ)..1, circleIntegrand M K α := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [circleIntegrand_expand]
  have hterm : ∀ n m : ℕ, Continuous fun α : ℝ => ((fK K n * fK K m : ℝ) : ℂ) *
      (eC (α * (((n : ℤ) - m + 1 : ℤ) : ℝ)) + eC (α * (((n : ℤ) - m - 1 : ℤ) : ℝ))) :=
    fun n m => continuous_const.mul ((continuous_eC_mul _).add (continuous_eC_mul _))
  rw [intervalIntegral.integral_finset_sum (fun n _ =>
    (continuous_finset_sum _ fun m _ => hterm n m).intervalIntegrable _ _)]
  unfold CK
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_finset_sum (fun m _ => (hterm n m).intervalIntegrable _ _),
    Complex.ofReal_sum]
  exact (Finset.sum_congr rfl fun m _ => term_integral K n m).symm

/-! ## Major / minor arcs (exact decomposition only) -/

/-- Major arcs: `⋃_{1 ≤ q ≤ Q} ⋃_{0 ≤ a ≤ q} [a/q - Q/M, a/q + Q/M]`. -/
def majorArcs (M Q : ℕ) : Set ℝ :=
  ⋃ q ∈ Finset.Icc 1 Q, ⋃ a ∈ Finset.range (q + 1),
    Set.Icc ((a : ℝ) / q - (Q : ℝ) / M) ((a : ℝ) / q + (Q : ℝ) / M)

/-- The V71 major arcs with `Q = ⌊(log M)^12⌋₊`. -/
noncomputable def majorArcsV71 (M : ℕ) : Set ℝ := majorArcs M ⌊Real.log M ^ 12⌋₊

theorem measurableSet_majorArcs (M Q : ℕ) : MeasurableSet (majorArcs M Q) := by
  unfold majorArcs
  exact Finset.measurableSet_biUnion _ fun q _ =>
    Finset.measurableSet_biUnion _ fun a _ => measurableSet_Icc

/-- `C_major = ∫_{(0,1] ∩ 𝔐} 2cos(2πα)|S|²`. -/
noncomputable def Cmajor (M K : ℕ) (𝔐 : Set ℝ) : ℝ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 ∩ 𝔐, circleIntegrand M K α

/-- `C_minor = ∫_{(0,1] \ 𝔐} 2cos(2πα)|S|²`. -/
noncomputable def Cminor (M K : ℕ) (𝔐 : Set ℝ) : ℝ :=
  ∫ α in Set.Ioc (0 : ℝ) 1 \ 𝔐, circleIntegrand M K α

/-- **Exact major/minor decomposition**: `C_K = C_major + C_minor` for any measurable `𝔐`
(in particular for the V71 major arcs).  No estimate of either piece is claimed. -/
theorem major_minor_exact_decomposition (M K : ℕ) {𝔐 : Set ℝ} (h𝔐 : MeasurableSet 𝔐) :
    CK M K = Cmajor M K 𝔐 + Cminor M K 𝔐 := by
  rw [circle_correlation_identity, intervalIntegral.integral_of_le zero_le_one]
  unfold Cmajor Cminor
  rw [integral_inter_add_diff h𝔐]
  exact (continuous_circleIntegrand M K).integrableOn_Ioc

/-- The V71 instance of the decomposition. -/
theorem major_minor_exact_decomposition_V71 (M K : ℕ) :
    CK M K = Cmajor M K (majorArcsV71 M) + Cminor M K (majorArcsV71 M) :=
  major_minor_exact_decomposition M K (measurableSet_majorArcs _ _)

end Erdos287.PostV64V71
