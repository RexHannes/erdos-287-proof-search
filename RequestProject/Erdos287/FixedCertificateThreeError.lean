import Mathlib
import RequestProject.Erdos287.FixedCertificateTransference

/-!
# Fixed-certificate transference with a separate `N2` stratum (V12, Part G2)

The V11 transference theorem (`Erdos287.Transference.sum_a_P_lower`) splits the dyadic
support into three regions: the certificate-positive region `P`, the sign region
`Ngood`, and the leakage region `U`.  V12 requires the *exceptional* region `N2` to be
kept apart from the sign region `N1`, with its own error term, so that the `N2` repair is
never silently merged into the sign hypothesis.

This file is append-only: nothing in `FixedCertificateTransference.lean` is changed.  It
adds a four-region partition `P ∪ N1 ∪ N2 ∪ U` with **three distinct errors**

* `ET` — total correlation error over the whole support;
* `EL` — leakage error over `U`;
* `E2` — the `N2` error;

and one comparison-margin slack `EM`.  The hypotheses on `N2` are *only* a bound on
`|∑_{N2} w·H|`: no sign information is assumed there.

## Main results

* `sum_a_P_identity4` — the exact four-region partition identity;
* `sum_a_P_lower4` — `∑_{p∈P} a p ≥ (1+C)·B − ET − EL − E2 − EM`;
* `sum_a_P_pos4` — positivity when `ET + EL + E2 + EM ≤ δ·B`, `0 < B` and `δ < 1 + C`;
* `sum_a_P_pos4_fraction` — the "constant-saving" variant: leakage plus `N2` error below
  a fixed fraction of the certificate margin already gives positivity (no logarithmic
  saving is required);
* `transference4_nonvacuous` — the hypotheses are simultaneously satisfiable.

Everything here is finite real algebra; no analytic input is used or asserted.
-/

open scoped BigOperators

namespace Erdos287
namespace Transference4

variable {ι : Type*} [DecidableEq ι]

/-- **Exact four-region partition identity.**  With `w = a − b` and `H = 1` on `P`,

`∑_{p∈P} a p = B + Total − Leak − ∑_{N1} w·H − ∑_{N2} w·H`. -/
theorem sum_a_P_identity4 (P N1 N2 U : Finset ι) (a b w H : ι → ℝ)
    (hw : ∀ n, w n = a n - b n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hPN1 : Disjoint P N1) (hPN2 : Disjoint P N2) (hPU : Disjoint P U)
    (hN1N2 : Disjoint N1 N2) (hN1U : Disjoint N1 U) (hN2U : Disjoint N2 U) :
    ∑ p ∈ P, a p
      = (∑ p ∈ P, b p)
        + (∑ n ∈ (P ∪ N1 ∪ N2 ∪ U), w n * H n)
        - (∑ n ∈ U, w n * H n)
        - (∑ n ∈ N1, w n * H n)
        - (∑ n ∈ N2, w n * H n) := by
  have hPN1N2 : Disjoint (P ∪ N1) N2 := by
    simp [Finset.disjoint_union_left, hPN2, hN1N2]
  have hall : Disjoint (P ∪ N1 ∪ N2) U := by
    simp [Finset.disjoint_union_left, hPU, hN1U, hN2U]
  rw [Finset.sum_union hall, Finset.sum_union hPN1N2, Finset.sum_union hPN1]
  have hP : ∑ n ∈ P, w n * H n = ∑ p ∈ P, a p - ∑ p ∈ P, b p := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [hHP p hp, hw p, mul_one]
  rw [hP]
  ring

/-- **Three-error transference lower bound.**  The sign hypothesis is imposed on `N1`
only; `N2` enters exclusively through its own error `E2`. -/
theorem sum_a_P_lower4 (P N1 N2 U : Finset ι) (a b w H : ι → ℝ) (Cc ET EL E2 EM : ℝ)
    (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN1 : ∀ n ∈ N1, H n ≤ 0)
    (hPN1 : Disjoint P N1) (hPN2 : Disjoint P N2) (hPU : Disjoint P U)
    (hN1N2 : Disjoint N1 N2) (hN1U : Disjoint N1 U) (hN2U : Disjoint N2 U)
    (hTotal : |∑ n ∈ (P ∪ N1 ∪ N2 ∪ U), w n * H n| ≤ ET)
    (hLeak : |∑ n ∈ U, w n * H n| ≤ EL)
    (hN2 : |∑ n ∈ N2, w n * H n| ≤ E2)
    (hMargin : Cc * (∑ p ∈ P, b p) - EM ≤ ∑ n ∈ N1, b n * H n) :
    (1 + Cc) * (∑ p ∈ P, b p) - ET - EL - E2 - EM ≤ ∑ p ∈ P, a p := by
  set B := ∑ p ∈ P, b p with hB
  have hid := sum_a_P_identity4 P N1 N2 U a b w H hw hHP hPN1 hPN2 hPU hN1N2 hN1U hN2U
  have hsplit : ∑ n ∈ N1, w n * H n
      = (∑ n ∈ N1, a n * H n) - ∑ n ∈ N1, b n * H n := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro n _
    rw [hw n]; ring
  have haH : ∑ n ∈ N1, a n * H n ≤ 0 :=
    Finset.sum_nonpos fun n hn => mul_nonpos_of_nonneg_of_nonpos (ha n) (hHN1 n hn)
  have hN1le : ∑ n ∈ N1, w n * H n ≤ -(Cc * B - EM) := by
    rw [hsplit]; linarith
  have hT' : -ET ≤ ∑ n ∈ (P ∪ N1 ∪ N2 ∪ U), w n * H n := (abs_le.1 hTotal).1
  have hL' : ∑ n ∈ U, w n * H n ≤ EL := (abs_le.1 hLeak).2
  have h2' : ∑ n ∈ N2, w n * H n ≤ E2 := (abs_le.1 hN2).2
  rw [hid]
  linarith

/-- **Positive certificate mass with three errors.** -/
theorem sum_a_P_pos4 (P N1 N2 U : Finset ι) (a b w H : ι → ℝ) (Cc ET EL E2 EM delta : ℝ)
    (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN1 : ∀ n ∈ N1, H n ≤ 0)
    (hPN1 : Disjoint P N1) (hPN2 : Disjoint P N2) (hPU : Disjoint P U)
    (hN1N2 : Disjoint N1 N2) (hN1U : Disjoint N1 U) (hN2U : Disjoint N2 U)
    (hTotal : |∑ n ∈ (P ∪ N1 ∪ N2 ∪ U), w n * H n| ≤ ET)
    (hLeak : |∑ n ∈ U, w n * H n| ≤ EL)
    (hN2 : |∑ n ∈ N2, w n * H n| ≤ E2)
    (hMargin : Cc * (∑ p ∈ P, b p) - EM ≤ ∑ n ∈ N1, b n * H n)
    (hBpos : 0 < ∑ p ∈ P, b p)
    (hE : ET + EL + E2 + EM ≤ delta * (∑ p ∈ P, b p))
    (hdelta : delta < 1 + Cc) :
    0 < ∑ p ∈ P, a p ∧
      (1 + Cc - delta) * (∑ p ∈ P, b p) ≤ ∑ p ∈ P, a p := by
  have hlow := sum_a_P_lower4 P N1 N2 U a b w H Cc ET EL E2 EM hw ha hHP hHN1
    hPN1 hPN2 hPU hN1N2 hN1U hN2U hTotal hLeak hN2 hMargin
  set B := ∑ p ∈ P, b p with hB
  have hstep : (1 + Cc - delta) * B ≤ (1 + Cc) * B - ET - EL - E2 - EM := by nlinarith
  have hpos : 0 < (1 + Cc - delta) * B := by nlinarith
  exact ⟨lt_of_lt_of_le hpos (le_trans hstep hlow), le_trans hstep hlow⟩

/-- **Constant-saving variant.**  A *fixed fraction* suffices: if the leakage error, the
`N2` error, the total-correlation error and the margin slack together stay below the
certificate margin `(1 + C)·B`, the prime mass is positive.  No logarithmic saving is
logically required (an arbitrary-log saving is of course sufficient, being a special
case with `delta` arbitrarily small). -/
theorem sum_a_P_pos4_fraction (P N1 N2 U : Finset ι) (a b w H : ι → ℝ) (Cc ET EL E2 EM : ℝ)
    (hw : ∀ n, w n = a n - b n)
    (ha : ∀ n, 0 ≤ a n)
    (hHP : ∀ p ∈ P, H p = 1)
    (hHN1 : ∀ n ∈ N1, H n ≤ 0)
    (hPN1 : Disjoint P N1) (hPN2 : Disjoint P N2) (hPU : Disjoint P U)
    (hN1N2 : Disjoint N1 N2) (hN1U : Disjoint N1 U) (hN2U : Disjoint N2 U)
    (hTotal : |∑ n ∈ (P ∪ N1 ∪ N2 ∪ U), w n * H n| ≤ ET)
    (hLeak : |∑ n ∈ U, w n * H n| ≤ EL)
    (hN2 : |∑ n ∈ N2, w n * H n| ≤ E2)
    (hMargin : Cc * (∑ p ∈ P, b p) - EM ≤ ∑ n ∈ N1, b n * H n)
    (hsmall : ET + EL + E2 + EM < (1 + Cc) * (∑ p ∈ P, b p)) :
    0 < ∑ p ∈ P, a p := by
  have hlow := sum_a_P_lower4 P N1 N2 U a b w H Cc ET EL E2 EM hw ha hHP hHN1
    hPN1 hPN2 hPU hN1N2 hN1U hN2U hTotal hLeak hN2 hMargin
  linarith

/-- Sanity instance: the four-region hypotheses are simultaneously satisfiable in a
nontrivial way, so the theorems above are not vacuous.  Take `P = {0}`, `N1 = {1}`,
`N2 = {2}`, `U = ∅`, `a = b` (so `w = 0`), `b 0 = 1`, `b n = 1/4` otherwise,
`H 0 = 1`, `H n = −1` otherwise, `C = −1/4` and all four errors zero. -/
theorem transference4_nonvacuous :
    ∃ (P N1 N2 U : Finset ℕ) (a b w H : ℕ → ℝ) (Cc ET EL E2 EM : ℝ),
      (∀ n, w n = a n - b n) ∧ (∀ n, 0 ≤ a n) ∧ (∀ p ∈ P, H p = 1) ∧
      (∀ n ∈ N1, H n ≤ 0) ∧
      Disjoint P N1 ∧ Disjoint P N2 ∧ Disjoint P U ∧
      Disjoint N1 N2 ∧ Disjoint N1 U ∧ Disjoint N2 U ∧
      |∑ n ∈ (P ∪ N1 ∪ N2 ∪ U), w n * H n| ≤ ET ∧
      |∑ n ∈ U, w n * H n| ≤ EL ∧
      |∑ n ∈ N2, w n * H n| ≤ E2 ∧
      Cc * (∑ p ∈ P, b p) - EM ≤ ∑ n ∈ N1, b n * H n ∧
      0 < ∑ p ∈ P, b p ∧ ET + EL + E2 + EM < (1 + Cc) * (∑ p ∈ P, b p) := by
  refine ⟨{0}, {1}, {2}, ∅,
    fun n => if n = 0 then 1 else (1 : ℝ) / 4,
    fun n => if n = 0 then 1 else (1 : ℝ) / 4,
    fun _ => 0, fun n => if n = 0 then 1 else -1,
    (-1 : ℝ) / 4, 0, 0, 0, 0, ?_⟩
  refine ⟨by intro n; simp, by intro n; dsimp only; split <;> norm_num, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num

end Transference4
end Erdos287
