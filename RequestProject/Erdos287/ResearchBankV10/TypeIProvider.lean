import RequestProject.Erdos287.ResearchBankV10.Providers
import RequestProject.Erdos287.ResearchBankV10.TypeIRescaling
import RequestProject.Erdos287.ResearchBankV10.TypeIRoughness
import RequestProject.Erdos287.ResearchBankV10.TypeIGroupedCoefficient

/-!
# Erdős #287 — Research Bank V10: the smooth Type-I provider interface and `∑_e T_e`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The repaired Type-I layer is *banked relative to explicit spectral input*.  This module composes
the exact pieces:

* the `e`-rescaling (`TypeIRescaling`) gives each shell term `T_e` the density factor `1/e`;
* the external per-`e` estimate is the hypothesis `RescaledTypeIBound`
  (`|T_e| ≤ K · Y / e` for each shell modulus `e = ∏d`, `|d| = J`), itself to be supplied by the
  external `SmoothTypeIInput` (spectral input ⟹ Type-I bound);
* the shell sum is controlled by the **proved** symmetric-sum bound (`TypeIRoughness`).

Proved:
* `sum_e_T_e_bound` — `∑_{ω(e) = J} |T_e| ≤ K · Y · s₀^J / J!`;
* `sum_e_T_e_bound_exp` — `∑_{ω(e) = J} |T_e| ≤ K · Y · (e·s₀/J)^J`;
* `smoothTypeI_of_spectral` — the Type-I provider, applied to the spectral input, yields the
  Type-I region bound (a direct restatement of the provider's contract; no analytic content is
  created).
-/

namespace Erdos287
namespace ResearchBankV10
namespace TypeIProvider

open Finset TypeIRoughness Providers HBSupportCoverage

/-- **External per-`e` Type-I estimate** after the `e`-rescaling: `|T_e| ≤ K · Y / e`. -/
structure RescaledTypeIBound (P : Finset ℕ) (J : ℕ) (T : Finset ℕ → ℝ) (K Y : ℝ) : Prop where
  bound : ∀ d ∈ P.powersetCard J, |T d| ≤ K * Y * (1 / ((∏ p ∈ d, p : ℕ) : ℝ))

/-- **`∑_e T_e` bound** from the per-`e` estimate and the proved symmetric-sum bound. -/
theorem sum_e_T_e_bound {P : Finset ℕ} {J : ℕ} {T : Finset ℕ → ℝ} {K Y : ℝ} (hK : 0 ≤ K)
    (hY : 0 ≤ Y) (h : RescaledTypeIBound P J T K Y) :
    ∑ d ∈ P.powersetCard J, |T d| ≤ K * Y * ((∑ p ∈ P, (1 / (p : ℝ))) ^ J / J.factorial) := by
  calc ∑ d ∈ P.powersetCard J, |T d|
      ≤ ∑ d ∈ P.powersetCard J, K * Y * (1 / ((∏ p ∈ d, p : ℕ) : ℝ)) :=
        Finset.sum_le_sum h.bound
    _ = K * Y * ∑ d ∈ P.powersetCard J, (1 / ((∏ p ∈ d, p : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ K * Y * ((∑ p ∈ P, (1 / (p : ℝ))) ^ J / J.factorial) := by
        gcongr; exact shell_reciprocal_le P J

/-- The same with the factorial estimate pushed through. -/
theorem sum_e_T_e_bound_exp {P : Finset ℕ} {J : ℕ} (hJ : 1 ≤ J) {T : Finset ℕ → ℝ} {K Y : ℝ}
    (hK : 0 ≤ K) (hY : 0 ≤ Y) (h : RescaledTypeIBound P J T K Y) :
    ∑ d ∈ P.powersetCard J, |T d| ≤ K * Y * (Real.exp 1 * (∑ p ∈ P, (1 / (p : ℝ))) / J) ^ J :=
  (sum_e_T_e_bound hK hY h).trans (by
    gcongr
    exact pow_div_factorial_le_exp_bound (Finset.sum_nonneg fun p _ => by positivity) hJ)

/-- The Type-I provider's contract, applied to the spectral input. -/
theorem smoothTypeI_of_spectral {P : CoverageParams} {E : SupportBox → ℝ → ℝ} {Kl : ℕ → ℝ}
    {κ : ℝ} (hI : SmoothTypeIInput P E Kl κ) (hZ : ZhengKloostermanInput Kl κ) :
    ∀ b, InTypeI P b → LogPowerSaving (E b) :=
  fun b hb => hI.reduction hZ typeICombinatorialFacts_holds b hb

end TypeIProvider
end ResearchBankV10
end Erdos287
