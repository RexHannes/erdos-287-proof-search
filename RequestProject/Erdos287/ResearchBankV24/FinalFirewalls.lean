import RequestProject.Erdos287.ResearchBankV24.ConditionalAsymptotic287
import RequestProject.Erdos287.ResearchBankV21.DensityCounterfixture
import RequestProject.Erdos287.ResearchBankV21.NormalizedSieveMonotonicity
import RequestProject.Erdos287.ResearchBankV20.ScopeFirewalls
import RequestProject.Erdos287.ResearchBankV20.NoEffectivization

/-!
# Erdős #287 — Research Bank V24 §5: final firewalls

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The nine required negative statements (all kernel-proved):

1. `fw1_spectator_square_not_raw_density` — spectator-square weighting does NOT preserve the raw
   density `1/(p-1)` (mod-11: `4/37 ≠ 1/10`);
2. `fw2_signed_coefficients` — a signed `λ` with a negative coefficient has nonnegative divisor
   sums (and without nonnegative divisor sums monotonicity fails);
3. `fw3_literal_cell_convolution_multiplicity` — the literal cell-indicator convolution has
   multiplicity `2 > 1` (at `143 = 11 · 13`);
4. `fw4_support_below_three_fifths_no_provider` — support exponent `273/500 < 3/5` does NOT
   construct a prime-distribution (Maynard-type) provider;
5. `fw5_colouring_identity_not_distribution` — the exact colouring identity holds, yet the
   source-class distribution provider can FAIL: the identity does not prove analytic
   distribution;
6. `fw6_same_weight_bound_not_V16` — the same-weight principal bound holds for every finite
   model, yet the V16 source-class provider can FAIL: the bound does not re-prove V16;
7. `fw7_score_does_not_construct_baseline` — the Route-C pair baseline is falsifiable, so a
   positive score conditional on it does not construct it;
8. `fw8_conditional_asymptotic_no_explicit_M0` — an eventual statement gives no explicit `M₀`;
9. `fw9_explicit_M0_required_for_splice` — an explicit `M₀` is required before the finite
   splice can yield global #287.
-/

namespace Erdos287
namespace ResearchBankV24
namespace FinalFirewalls

open Finset
open ResearchBankV22.RoundedRoughSieve ResearchBankV22.CompletedPositiveWeight
open ResearchBankV22.IndependentFactorization
open RepairedProvider

/-- 1. Spectator-square weighting does NOT preserve the raw density `1/(p-1)`. -/
theorem fw1_spectator_square_not_raw_density :
    ResearchBankV21.DensityCounterfixture.weightedDensity = 4 / 37 ∧
      ResearchBankV21.DensityCounterfixture.rawDensity = 1 / (11 - 1) ∧
      ResearchBankV21.DensityCounterfixture.weightedDensity ≠
        ResearchBankV21.DensityCounterfixture.rawDensity :=
  let h := ResearchBankV21.DensityCounterfixture.spectator_square_density_not_invariant
  ⟨h.1, h.2.1, h.2.2.2⟩

/-- 2. Signed coefficients need not be nonnegative although the divisor sums are; and the
monotonicity theorem genuinely needs nonnegative divisor sums. -/
theorem fw2_signed_coefficients :
    (ResearchBankV21.NormalizedSieveMonotonicity.signedLam {()} < 0 ∧
      ∀ S, 0 ≤ ResearchBankV21.FiniteSieveSetup.divSum
        ResearchBankV21.NormalizedSieveMonotonicity.signedLam S) ∧
    (ResearchBankV21.FiniteSieveSetup.divSum ResearchBankV21.NormalizedSieveMonotonicity.badLam
        {()} < 0 ∧
      ResearchBankV21.FiniteSieveSetup.normCost ResearchBankV21.NormalizedSieveMonotonicity.badLam
          (fun _ => 1 / 2) <
        ResearchBankV21.FiniteSieveSetup.normCost
          ResearchBankV21.NormalizedSieveMonotonicity.badLam (fun _ => 0)) :=
  ⟨ResearchBankV21.NormalizedSieveMonotonicity.signed_coefficient_nonneg_divSum,
    ResearchBankV21.NormalizedSieveMonotonicity.monotonicity_needs_divSum_nonneg⟩

/-- 3. The literal cell-indicator convolution has multiplicity `2 > 1`. -/
theorem fw3_literal_cell_convolution_multiplicity :
    1 < literalConv literalCellInd literalCellInd 143 := by
  rw [literal_cell_convolution_multiplicity_two]; norm_num

/-- 4. Support below `3/5` does NOT construct a prime-distribution provider. -/
theorem fw4_support_below_three_fifths_no_provider :
    ¬ ((273 / 500 : ℚ) < 3 / 5 → ∀ err : ℝ → ℝ,
      ResearchBankV17.ThinSupportLedger.PrimeDistributionProvider (273 / 500) err) :=
  ResearchBankV20.ScopeFirewalls.support_below_threshold_no_provider

/-- The unit coefficient `1_{A = ∅}`. -/
noncomputable def unitCoeff : Finset ℕ → ℝ := fun A => if A = ∅ then 1 else 0

theorem unitCoeff_source : SourceFactorization unitCoeff ∅ ∅ := by
  refine ⟨unitCoeff, unitCoeff, ?_, ?_, ?_, ?_, ?_⟩
  · intro A; unfold unitCoeff; split_ifs <;> norm_num
  · intro A; unfold unitCoeff; split_ifs <;> norm_num
  · intro A hA; unfold unitCoeff at hA; split_ifs at hA with h
    · rw [h]; exact empty_subset _
    · exact absurd rfl hA
  · intro A hA; unfold unitCoeff at hA; split_ifs at hA with h
    · rw [h]
    · exact absurd rfl hA
  · funext A
    unfold conv unitCoeff
    by_cases hA : A = ∅
    · subst hA; simp
    · rw [if_neg hA]
      refine (sum_eq_zero fun B hB => ?_).symm
      by_cases hB0 : B = ∅
      · subst hB0; simp [hA]
      · simp [hB0]

/-- A linear error functional (evaluation at the empty atom set, scaled by `c M`). -/
noncomputable def evalErr (c : ℕ → ℝ) : ℕ → (Finset ℕ → ℝ) → ℝ := fun M lam => c M * lam ∅

theorem evalErr_not_provider (c : ℕ → ℝ) (hc : ∀ M, 1 ≤ c M) :
    ¬ SourceClassDistributionProvider (fun _ _ => ∅) (fun _ _ => ∅) (evalErr c) := by
  intro hP
  obtain ⟨M₀, hM⟩ := hP.class_bound 0 (1 / 2) (by norm_num)
  have := hM M₀ le_rfl unitCoeff unitCoeff_source
  simp only [evalErr, unitCoeff, if_true, mul_one] at this
  have h1 := hc M₀
  rw [abs_of_pos (by linarith)] at this
  linarith

/-- 5. The exact colouring identity (a theorem, valid for every weight) does NOT prove analytic
distribution: the source-class distribution provider fails for a linear error functional. -/
theorem fw5_colouring_identity_not_distribution :
    ∃ (Us Ur : ℕ → ℕ → Finset ℕ) (DE : ℕ → (Finset ℕ → ℝ) → ℝ),
      ¬ SourceClassDistributionProvider Us Ur DE :=
  ⟨_, _, evalErr fun _ => 1, evalErr_not_provider _ fun _ => le_rfl⟩

/-- 6. The same-weight principal bound (a theorem for every finite model) does NOT re-prove the
V16 analytic source-class theorem: the provider fails for a growing linear error functional. -/
theorem fw6_same_weight_bound_not_V16 :
    ¬ SourceClassDistributionProvider (fun _ _ => ∅) (fun _ _ => ∅)
      (evalErr fun M => (M : ℝ) + 1) :=
  evalErr_not_provider _ fun M => by have : (0 : ℝ) ≤ M := M.cast_nonneg; linarith

/-- 7. A positive score conditional on the pair baseline does NOT construct the baseline: the
baseline provider is falsifiable. -/
theorem fw7_score_does_not_construct_baseline {V : Type} [Fintype V] [DecidableEq V]
    (τ : ResearchBankV16.RouteCConsumer.FixedTupleC V)
    (W : ResearchBankV16.RouteCConsumer.WeightSystem τ) :
    ¬ ResearchBankV16.ConditionalRouteCImplication.RouteCBaselineProvider τ W (fun _ => 0)
      (-100000) 0 :=
  ResearchBankV16.ConditionalRouteCImplication.baseline_provider_falsifiable τ W

/-- 8. The conditional asymptotic theorem does NOT provide an explicit `M₀`. -/
theorem fw8_conditional_asymptotic_no_explicit_M0 (B : ℕ) :
    ∃ Q : ℕ → Prop, (∃ M₀ : ℕ, ∀ M ≥ M₀, Q M) ∧ ¬ ∀ M ≥ B, Q M :=
  ResearchBankV20.NoEffectivization.conditional_asymptotic_gives_no_explicit_M0 B

/-- 9. An explicit `M₀` is required before the finite splice can yield global #287. -/
theorem fw9_explicit_M0_required_for_splice (U : ℕ) :
    ¬ ∀ bad : ℕ → Prop, (∃ M₀, ∀ M ≥ M₀, ¬ bad M) → (∀ M ≤ U, ¬ bad M) → ∀ M, ¬ bad M :=
  (ResearchBankV20.NoEffectivization.splice_needs_explicit_M0 U).2

end FinalFirewalls
end ResearchBankV24
end Erdos287
