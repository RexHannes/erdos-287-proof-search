import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V17 §4: thin support exponent arithmetic

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**Caveat.**  The audited numerical value of the thin support exponent was not supplied to this run.
The exponent therefore enters as a parameter `θ` with the certified support comparison
`ThinSupportCertificate θ : θ < 4/7`.  As a recorded instance, the Route-C exponent
`θ_d = 273/500` satisfies all comparisons.

Kernel-proved (LEAN BANK, support arithmetic only):
* `thresholds_ordered` — `4/7 < 7/12 < 3/5`;
* `support_comparisons` — `θ < 4/7 ⟹ θ < 7/12 ∧ θ < 3/5`;
* `thetaD_comparisons` — `273/500 < 4/7 < 7/12 < 3/5`.

**Firewall** (`level_below_threshold_does_not_construct_provider`): a level below `3/5` does NOT
construct a prime-distribution provider — the provider below is falsifiable and fails for an
error term of size `x`, whatever the level.
-/

namespace Erdos287
namespace ResearchBankV17
namespace ThinSupportLedger

/-- Certified support comparison for the thin exponent `θ`. -/
structure ThinSupportCertificate (θ : ℚ) : Prop where
  lt_four_sevenths : θ < 4 / 7

theorem thresholds_ordered : (4 / 7 : ℚ) < 7 / 12 ∧ (7 / 12 : ℚ) < 3 / 5 := by norm_num

/-- **Support comparisons.** -/
theorem support_comparisons {θ : ℚ} (h : ThinSupportCertificate θ) :
    θ < 4 / 7 ∧ θ < 7 / 12 ∧ θ < 3 / 5 := by
  have := h.lt_four_sevenths
  refine ⟨this, by linarith, by linarith⟩

/-- The recorded Route-C exponent `θ_d = 273/500`. -/
theorem thetaD_comparisons :
    (273 / 500 : ℚ) < 4 / 7 ∧ (4 / 7 : ℚ) < 7 / 12 ∧ (7 / 12 : ℚ) < 3 / 5 := by norm_num

theorem thetaD_certificate : ThinSupportCertificate (273 / 500) := ⟨by norm_num⟩

/-- A prime-distribution provider at level `θ` for an error function `err` (EXTERNAL PROVIDER
shape: power-of-log saving for every `A`). -/
structure PrimeDistributionProvider (θ : ℚ) (err : ℝ → ℝ) : Prop where
  saving : ∀ A : ℕ, ∃ x₀ : ℝ, ∀ x ≥ x₀, |err x| ≤ x / (Real.log x) ^ A

/-- The provider fails for `err x = 2x` (at every level). -/
theorem provider_fails_linear (θ : ℚ) : ¬ PrimeDistributionProvider θ (fun x => 2 * x) := by
  intro h
  obtain ⟨x₀, hx⟩ := h.saving 0
  have := hx (max x₀ 1) (le_max_left _ _)
  have h1 : (1 : ℝ) ≤ max x₀ 1 := le_max_right _ _
  rw [pow_zero, div_one, abs_of_pos (by linarith)] at this
  linarith

/-- **Firewall: level `< 3/5` does NOT construct a prime-distribution provider.** -/
theorem level_below_threshold_does_not_construct_provider {θ : ℚ} (hθ : θ < 3 / 5) :
    ¬ (θ < 3 / 5 → ∀ err : ℝ → ℝ, PrimeDistributionProvider θ err) :=
  fun h => provider_fails_linear θ (h hθ _)

end ThinSupportLedger
end ResearchBankV17
end Erdos287
