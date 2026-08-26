import Mathlib
import RequestProject.TrustedBank.Gate1A.RowConservation

/-!
# Gate 1A — the AVG-JDR closure interface (conditional kernel theorem)

`SOURCE-AVG-JDR` is **OPEN** and is *not* proved (nor assumed) anywhere.  What is banked
here is the purely algebraic implication:

*if* the centered source operator satisfies an energy bound
`∑_{r,m,k} ‖S r m k‖² ≤ targetEnergy`, *and* a source identity
`Ctilde = H · S + negligible` is supplied, *then* the normalized Gate quantity
`∑ ‖Ctilde‖²` obeys the corresponding bound.

The source identity is a hypothesis of every theorem below.  It is **not** asserted:
the authoritative source definitions of `Ctilde^{gen}` are not present in this
repository, and this is recorded as `SOURCE_AVG_JDR_SOURCE_IDENTITY :
SOURCE_FIELD_REQUIRED` in `RequestProject/Status/Delta6Ledger.lean`.
-/

open scoped BigOperators

namespace TrustedBank
namespace Gate1A

variable {σ : Type*} [Fintype σ]

/-- Elementary quadratic inequality `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem normSq_add_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h0 : (0:ℝ) ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- **Exact-identity transfer.**  If `Ctilde = H · S` pointwise, then the total energy
of `Ctilde` is exactly `H²` times that of `S`; in particular an AVG-JDR-type bound on
`S` transfers with the factor `H²`. -/
theorem avgJDR_transfer_exact (S Ct : σ → ℂ) (H : ℝ) (targetEnergy : ℝ)
    (hSource : ∀ i, Ct i = (H : ℂ) * S i)
    (hAVG : ∑ i, ‖S i‖ ^ 2 ≤ targetEnergy) :
    ∑ i, ‖Ct i‖ ^ 2 ≤ H ^ 2 * targetEnergy := by
  have key : ∑ i, ‖Ct i‖ ^ 2 = H ^ 2 * ∑ i, ‖S i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSource i, norm_mul, mul_pow]
    simp [sq_abs]
  rw [key]
  exact mul_le_mul_of_nonneg_left hAVG (sq_nonneg H)

/-- **Transfer with a negligible term.**  If `Ctilde = H · S + negligible` pointwise and
`S` obeys the AVG-JDR energy bound, then `∑ ‖Ctilde‖² ≤ 2H²·targetEnergy + 2·(energy of
the negligible term)`.  No claim is made that either hypothesis holds. -/
theorem avgJDR_transfer (S Ct neg : σ → ℂ) (H : ℝ) (targetEnergy : ℝ)
    (hSource : ∀ i, Ct i = (H : ℂ) * S i + neg i)
    (hAVG : ∑ i, ‖S i‖ ^ 2 ≤ targetEnergy) :
    ∑ i, ‖Ct i‖ ^ 2 ≤ 2 * H ^ 2 * targetEnergy + 2 * ∑ i, ‖neg i‖ ^ 2 := by
  have step : ∀ i : σ, ‖Ct i‖ ^ 2 ≤ 2 * H ^ 2 * ‖S i‖ ^ 2 + 2 * ‖neg i‖ ^ 2 := by
    intro i
    have h := normSq_add_le_two ((H : ℂ) * S i) (neg i)
    rw [hSource i]
    calc ‖(H : ℂ) * S i + neg i‖ ^ 2
        ≤ 2 * ‖(H : ℂ) * S i‖ ^ 2 + 2 * ‖neg i‖ ^ 2 := h
      _ = 2 * H ^ 2 * ‖S i‖ ^ 2 + 2 * ‖neg i‖ ^ 2 := by
          rw [norm_mul, mul_pow]; simp [sq_abs]; ring
  calc ∑ i, ‖Ct i‖ ^ 2
      ≤ ∑ i, (2 * H ^ 2 * ‖S i‖ ^ 2 + 2 * ‖neg i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => step i
    _ = 2 * H ^ 2 * (∑ i, ‖S i‖ ^ 2) + 2 * ∑ i, ‖neg i‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * H ^ 2 * targetEnergy + 2 * ∑ i, ‖neg i‖ ^ 2 := by
        have : (0:ℝ) ≤ 2 * H ^ 2 := by positivity
        nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset σ)) =>
          sq_nonneg ‖neg i‖)]

/-- Specialisation to the shape used in the Gate-1A ledger: with
`targetEnergy = M L^4 / H` (whatever its numerical value), the transferred bound for the
exact identity is `H² · targetEnergy`, i.e. `M H L^4` when `targetEnergy = M L^4 / H`. -/
theorem avgJDR_normalized (S Ct : σ → ℂ) (Mv Lv Hv : ℝ) (hH : Hv ≠ 0)
    (hSource : ∀ i, Ct i = (Hv : ℂ) * S i)
    (hAVG : ∑ i, ‖S i‖ ^ 2 ≤ Mv * Lv ^ 4 / Hv) :
    ∑ i, ‖Ct i‖ ^ 2 ≤ Mv * Hv * Lv ^ 4 := by
  have h := avgJDR_transfer_exact S Ct Hv (Mv * Lv ^ 4 / Hv) hSource hAVG
  have : Hv ^ 2 * (Mv * Lv ^ 4 / Hv) = Mv * Hv * Lv ^ 4 := by
    field_simp
  rwa [this] at h

end Gate1A
end TrustedBank
