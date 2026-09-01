import Mathlib

/-!
# Erdős #287 — the single Perron contour: exact `L¹` identity and logarithmic budget

This module proves, unconditionally and in the kernel, the exact one-contour integral

`∫_{-T}^{T} (c² + t²)^{-1/2} dt = 2 · arsinh (T / c)`  for `c > 0`,

and derives from it the logarithmic budget at the Perron parameters `c = 1/L`, `T = L^K`:

`∫_{-L^K}^{L^K} ((1/L)² + t²)^{-1/2} dt = 2 · arsinh (L^{K+1}) ≤ 2 · log (1 + 2 L^{K+1})`.

It then packages the result as an explicit interface `SingleContourL1Bound` together with a
deterministic compiler that consumes such a bound.  Nothing here is an asymptotic or
physical statement about the Erdős #287 source: this is the *single-contour* analytic
lemma only.  In particular, and by design, no statement of this file bounds a *total* over
an uncontrolled family of contours — see the counterguard module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PerronContour

/-! ## §1  The exact single-contour `L¹` identity -/

/-- **`singleContour_integral_eq_arsinh`.**  `LEAN_PROVED`.  For `c > 0`,
`∫_{-T}^{T} (c² + t²)^{-1/2} dt = 2 arsinh (T/c)`. -/
theorem singleContour_integral_eq_arsinh (c T : ℝ) (hc : 0 < c) :
    (∫ t in (-T)..T, (Real.sqrt (c ^ 2 + t ^ 2))⁻¹) = 2 * Real.arsinh (T / c) := by
  have hpos : ∀ t : ℝ, 0 < Real.sqrt (c ^ 2 + t ^ 2) := by
    intro t
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg t, sq_nonneg c]
  have hcc : Real.sqrt (c ^ 2) = c := Real.sqrt_sq hc.le
  have hsq : ∀ t : ℝ, Real.sqrt (1 + (t / c) ^ 2) = Real.sqrt (c ^ 2 + t ^ 2) / c := by
    intro t
    rw [eq_div_iff (ne_of_gt hc), ← hcc, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [hcc]
    field_simp
  have hderiv : ∀ t ∈ Set.uIcc (-T) T,
      HasDerivAt (fun s : ℝ => Real.arsinh (s / c)) (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => s / c) (1 / c) t := by
      simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id t).div_const c
    have h2 := (Real.hasDerivAt_arsinh (t / c)).comp t h1
    convert h2 using 1
    rw [hsq t]
    field_simp
  have hcont : Continuous fun t : ℝ => (Real.sqrt (c ^ 2 + t ^ 2))⁻¹ := by
    apply Continuous.inv₀
    · fun_prop
    · intro t; exact ne_of_gt (hpos t)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _),
    neg_div, Real.arsinh_neg]
  ring

/-- **`arsinh_le_log_one_add_two_mul`.**  `LEAN_PROVED`.  For `x ≥ 0`,
`arsinh x ≤ log (1 + 2x)`. -/
theorem arsinh_le_log_one_add_two_mul (x : ℝ) (hx : 0 ≤ x) :
    Real.arsinh x ≤ Real.log (1 + 2 * x) := by
  have h : Real.arsinh x = Real.log (x + Real.sqrt (1 + x ^ 2)) := by rw [Real.arsinh]
  rw [h]
  apply Real.log_le_log
  · nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + x ^ 2), Real.sqrt_nonneg (1 + x ^ 2)]
  · have hle : Real.sqrt (1 + x ^ 2) ≤ 1 + x := by
      rw [show (1:ℝ) + x = Real.sqrt ((1 + x) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      apply Real.sqrt_le_sqrt; nlinarith
    linarith

/-- **`singleContour_integral_le_log`.**  `LEAN_PROVED`.  The logarithmic single-contour
budget: for `c > 0` and `T ≥ 0`,
`∫_{-T}^{T} (c² + t²)^{-1/2} dt ≤ 2 log (1 + 2T/c)`. -/
theorem singleContour_integral_le_log (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, (Real.sqrt (c ^ 2 + t ^ 2))⁻¹) ≤ 2 * Real.log (1 + 2 * (T / c)) := by
  rw [singleContour_integral_eq_arsinh c T hc]
  have := arsinh_le_log_one_add_two_mul (T / c) (by positivity)
  linarith

/-! ## §2  The Perron parameters `c = 1/L`, `T = L^K` -/

/-- **`perronContour_integral_eq`.**  `LEAN_PROVED`.  At `c = 1/L` and `T = L^K` with
`L > 0`, the exact value of the single-contour integral is `2 arsinh (L^{K+1})`. -/
theorem perronContour_integral_eq (L : ℝ) (hL : 0 < L) (K : ℕ) :
    (∫ t in (-(L ^ K))..(L ^ K), (Real.sqrt ((1 / L) ^ 2 + t ^ 2))⁻¹)
      = 2 * Real.arsinh (L ^ (K + 1)) := by
  rw [singleContour_integral_eq_arsinh (1 / L) (L ^ K) (by positivity)]
  congr 1
  rw [pow_succ]
  field_simp

/-- **`perronContour_log_budget`.**  `LEAN_PROVED`.  The logarithmic budget at the Perron
parameters: `∫ ≤ 2 log (1 + 2 L^{K+1})`. -/
theorem perronContour_log_budget (L : ℝ) (hL : 0 < L) (K : ℕ) :
    (∫ t in (-(L ^ K))..(L ^ K), (Real.sqrt ((1 / L) ^ 2 + t ^ 2))⁻¹)
      ≤ 2 * Real.log (1 + 2 * L ^ (K + 1)) := by
  rw [perronContour_integral_eq L hL K]
  have := arsinh_le_log_one_add_two_mul (L ^ (K + 1)) (by positivity)
  linarith

/-! ## §3  The `SingleContourL1Bound` interface and its deterministic compiler -/

/-- **A single-contour `L¹` bound.**  An explicit finite datum: a contour half-length `T`,
an offset `c > 0`, and a numerical bound on the `L¹` mass of the Perron kernel on that
contour. -/
structure SingleContourL1Bound where
  /-- The Perron offset. -/
  c : ℝ
  /-- Positivity of the offset. -/
  c_pos : 0 < c
  /-- The contour half-length. -/
  T : ℝ
  /-- Non-negativity of the half-length. -/
  T_nonneg : 0 ≤ T
  /-- The numerical `L¹` budget. -/
  bound : ℝ
  /-- The `L¹` mass of the kernel on the contour is within budget. -/
  l1_le : (∫ t in (-T)..T, (Real.sqrt (c ^ 2 + t ^ 2))⁻¹) ≤ bound

/-- The interface is **inhabited**: the logarithmic budget of §1 supplies a bound for every
admissible pair `(c, T)`. -/
noncomputable def singleContourL1Bound_log (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T) : SingleContourL1Bound where
  c := c
  c_pos := hc
  T := T
  T_nonneg := hT
  bound := 2 * Real.log (1 + 2 * (T / c))
  l1_le := singleContour_integral_le_log c T hc hT

/-- The Perron specialisation of the interface. -/
noncomputable def perronSingleContourL1Bound (L : ℝ) (hL : 0 < L) (K : ℕ) : SingleContourL1Bound :=
  singleContourL1Bound_log (1 / L) (L ^ K) (by positivity) (by positivity)

/-- **Deterministic single-contour compiler.**  If a quantity `S` is dominated by `A` times
the contour `L¹` mass, then a `SingleContourL1Bound` converts this into the explicit numeric
bound `A · bound`. -/
theorem contour_compile (B : SingleContourL1Bound) (A S : ℝ) (hA : 0 ≤ A)
    (hS : S ≤ A * ∫ t in (-B.T)..B.T, (Real.sqrt (B.c ^ 2 + t ^ 2))⁻¹) :
    S ≤ A * B.bound :=
  hS.trans (mul_le_mul_of_nonneg_left B.l1_le hA)

/-- **Cardinality-explicit aggregation.**  Summing single-contour bounds over a finite
family multiplies the budget by the **cardinality** of the family, which therefore has to be
controlled separately.  This is the positive counterpart of the per-contour counterguard. -/
theorem contour_total_compile {ι : Type*} (F : Finset ι) (B : SingleContourL1Bound)
    (A : ℝ) (hA : 0 ≤ A) (S : ι → ℝ)
    (hS : ∀ i ∈ F, S i ≤ A * ∫ t in (-B.T)..B.T, (Real.sqrt (B.c ^ 2 + t ^ 2))⁻¹) :
    ∑ i ∈ F, S i ≤ (F.card : ℝ) * (A * B.bound) := by
  calc ∑ i ∈ F, S i ≤ ∑ _i ∈ F, A * B.bound :=
        Finset.sum_le_sum fun i hi => contour_compile B A (S i) hA (hS i hi)
    _ = (F.card : ℝ) * (A * B.bound) := by rw [Finset.sum_const, nsmul_eq_mul]

end PerronContour
end Erdos287
