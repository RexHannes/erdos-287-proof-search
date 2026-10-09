import RequestProject.Erdos287.ResearchBankV19.ActualCenteredCompositionProvider
import RequestProject.Erdos287.ResearchBankV19.ZeroFrequencyCompatibility
import RequestProject.Erdos287.ResearchBankV19.E1PeriodicProvider
import RequestProject.Erdos287.ResearchBankV19.E2OuterMultiplier
import RequestProject.Erdos287.ResearchBankV19.OuterCostLedger
import RequestProject.Erdos287.ResearchBankV19.RootClassGram
import RequestProject.Erdos287.ResearchBankV19.OverlapConductor
import RequestProject.Erdos287.ResearchBankV19.NonunitReduction

/-!
# Erdős #287 — Research Bank V19: negative controls (bundle)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`v19_negative_controls` bundles the machine-checked refutations of V19:
1. `Ω(0) = 1` does not fix the zero-frequency main term;
2. independent-copy root assignments do not satisfy the coherent zero-mode theorem;
3. the primitive conductor `E` is not the `q`-period `V`;
4. joint `q/h` dependence is not covered by the E2 scope theorem;
5. the square root does not preserve `σ`;
6. fixed `J` does not make the unweighted conductor sum polylogarithmic;
7. the composition provider is falsifiable (a joint-dependence branch refutes it).
-/

namespace Erdos287
namespace ResearchBankV19
namespace NegativeControls

theorem v19_negative_controls :
    (¬ ∀ (q₁ q₂ : ℕ) (n₁ n₂ a₁ a₂ Δ : ℤ),
        ResearchBankV18.ColourConductor.e (Nat.lcm q₁ q₂) (0 * Δ) = 1 →
          (ZeroFrequencyCompatibility.solutions q₁ q₂ n₁ n₂ a₁ a₂).card = 1) ∧
    (∃ (a a' : ℕ → ℤ) (q₁ q₂ : ℕ), IsCoprime (a q₁) (Nat.gcd q₁ q₂ : ℤ) ∧
      ¬ ∀ n₁ n₂ : ℤ, (a q₁ * n₂ ≡ a' q₂ * n₁ [ZMOD (Nat.gcd q₁ q₂ : ℤ)] ↔
        n₁ ≡ n₂ [ZMOD (Nat.gcd q₁ q₂ : ℤ)])) ∧
    (∃ d : E1Periodic.E1PeriodData, d.E ≠ d.V) ∧
    (∃ (X U : Fin 2 → ℂ), (∀ h, ‖U h‖ ≤ 1) ∧ ‖∑ h, X h‖ = 0 ∧ ‖∑ h, U h * X h‖ = 2) ∧
    ((2 : ℝ) ^ (-(1 : ℝ)) < (2 : ℝ) ^ (-(1 : ℝ) / 2)) ∧
    (¬ ∃ (C : ℝ) (k : ℕ), ∀ Y : ℕ, 2 ≤ Y →
      ∑ D ∈ Finset.Icc 1 Y, ((Nat.divisors D).card : ℝ) ≤ C * Real.log Y ^ k) ∧
    (∀ (N : ℕ → ℝ) (c : ℝ),
      ¬ ActualCenteredCompositionProvider.ActualCenteredSourceCompositionProvider
        [BranchData.jointSample] N c) :=
  ⟨ZeroFrequencyCompatibility.omega_zero_does_not_fix_main_term,
   CoherentRoots.independent_copies_fail,
   E1Periodic.conductor_not_period,
   E2OuterMultiplier.joint_dependence_not_covered,
   OuterCostLedger.sigma_not_preserved (by norm_num) (by norm_num),
   OuterCostLedger.unweighted_divisor_sum_not_polylog,
   ActualCenteredCompositionProvider.provider_falsifiable⟩

end NegativeControls
end ResearchBankV19
end Erdos287
