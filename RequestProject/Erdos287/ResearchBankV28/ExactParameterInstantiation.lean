import RequestProject.Erdos287.ResearchBankV17.ThinParameters
import RequestProject.Erdos287.ResearchBankV17.ThinConsumer
import RequestProject.Erdos287.ResearchBankV23.PrincipalBudget
import RequestProject.Erdos287.ResearchBankV27.GlobalConductorSum

/-!
# Erdős #287 — Research Bank V28 §10: exact parameter instantiation

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

All values are exact rationals / naturals; no floating point.  The parameters are REUSED from the
frozen banks (no redefinition):

* `K = 2^41252000`, `P = 12K`, `a = 28593810`, `δ = 1/40000` — `ResearchBankV17.ThinParameters`;
* `ϑ = 273/500`, `ρ = 1/1000000`, `ϑ₀ = 545999/1000000` — `ResearchBankV22.PositiveSieveParameters`;
* `A_C = 1000273/273000` — `ResearchBankV16.RouteCParameters`;
* `η = 1/1100`, `σ = 1/19000` — `ResearchBankV27.GlobalConductorSum`.

The audited functional bounds `μ_F > 7147687/10000`, `W_F < 98278402/10000` are CERTIFIED INPUTS
(the frozen `ThinFunctionalCertificate` shape); they are not computed here.

**LEAN BANK.**
* `parameter_values` — the literal values above;
* `principal_slack_reused` — `A_C − 2/ϑ₀ − 1/5000 = 147807727/186322158750 > 0` (V23, reused);
* `norm_transfer_witness_pos` — `8746001/25000000 > 0` (supplied witness value; its derivation
  formula is not part of the frozen banks and is recorded as supplied);
* `thin_margin_check_final` — the frozen exact check `ThinMarginCheck μ_lo W_hi (−423/5)`;
  `90 − 423/5 = 27/5`;
* `score_margin_exact` — `μ_lo − (A_C W_hi + 27/5)/99 − 350 − 1/20 = 11479502057/12285000000 > 0`
  (the `1/20` is the reserved slack of the score ledger);
* `clean_savings` — `347/418000 > 0` and `347/836000 > 0` (V27, reused).
-/

namespace Erdos287
namespace ResearchBankV28
namespace ExactParameterInstantiation

open ResearchBankV16.RouteCParameters

/-- Audited lower bound for `μ_F` (certified input value). -/
def muLo : ℚ := 7147687 / 10000

/-- Audited upper bound for `W_F` (certified input value). -/
def WHi : ℚ := 98278402 / 10000

/-- The off-principal constant used in the final composition: `90 + err = 27/5`. -/
def errFinal : ℚ := -423 / 5

/-- The supplied norm-transfer witness. -/
def normTransferWitness : ℚ := 8746001 / 25000000

/-- **Parameter values** (LEAN BANK). -/
theorem parameter_values :
    ResearchBankV17.ThinParameters.K = 2 ^ 41252000 ∧
    ResearchBankV17.ThinParameters.P = 12 * ResearchBankV17.ThinParameters.K ∧
    ResearchBankV17.ThinParameters.aParam = 28593810 ∧
    ResearchBankV17.ThinParameters.delta = 1 / 40000 ∧
    ResearchBankV22.PositiveSieveParameters.vartheta = 273 / 500 ∧
    ResearchBankV22.PositiveSieveParameters.rho = 1 / 1000000 ∧
    ResearchBankV22.PositiveSieveParameters.vartheta0 = 545999 / 1000000 ∧
    A_C = 1000273 / 273000 ∧
    ResearchBankV27.GlobalConductorSum.eta = 1 / 1100 ∧
    ResearchBankV27.GlobalConductorSum.sigma = 1 / 19000 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ResearchBankV22.PositiveSieveParameters.vartheta0_eq, rfl,
    rfl, rfl⟩
  unfold ResearchBankV17.ThinParameters.K
  rw [ResearchBankV17.ThinParameters.L_def]

/-- **Principal slack** (LEAN BANK, reused from V23). -/
theorem principal_slack_reused :
    A_C - 2 / ResearchBankV22.PositiveSieveParameters.vartheta0 - 1 / 5000 =
        147807727 / 186322158750 ∧ (0 : ℚ) < 147807727 / 186322158750 :=
  ResearchBankV23.PrincipalBudget.principal_slack

/-- **Norm-transfer witness** (LEAN BANK). -/
theorem norm_transfer_witness_pos : normTransferWitness = 8746001 / 25000000 ∧
    (0 : ℚ) < normTransferWitness := by
  unfold normTransferWitness; norm_num

/-- `90 + err = 27/5` (LEAN BANK). -/
theorem baseline_constant : baselineConst + errFinal = 27 / 5 := by
  unfold baselineConst errFinal; norm_num

/-- **The frozen exact thin margin check at the final constants** (LEAN BANK). -/
theorem thin_margin_check_final :
    ResearchBankV17.ThinFunctional.ThinMarginCheck muLo WHi errFinal := by
  unfold ResearchBankV17.ThinFunctional.ThinMarginCheck RouteCMarginCheck threshold
    pairDen baselineConst A_C muLo WHi errFinal
  norm_num

/-- **Exact score margin** (LEAN BANK). -/
theorem score_margin_exact :
    muLo - (A_C * WHi + 27 / 5) / 99 - 350 - 1 / 20 = 11479502057 / 12285000000 ∧
      (0 : ℚ) < 11479502057 / 12285000000 := by
  unfold muLo WHi A_C; norm_num

/-- **Clean savings** (LEAN BANK, reused from V27). -/
theorem clean_savings :
    ResearchBankV27.GlobalConductorSum.eta - 3 * ResearchBankV27.GlobalConductorSum.sigma / 2 =
        347 / 418000 ∧ (0 : ℚ) < 347 / 418000 ∧
    (ResearchBankV27.GlobalConductorSum.eta -
        3 * ResearchBankV27.GlobalConductorSum.sigma / 2) / 2 = 347 / 836000 ∧
      (0 : ℚ) < 347 / 836000 :=
  ⟨ResearchBankV27.GlobalConductorSum.clean_energy_saving.1,
    ResearchBankV27.GlobalConductorSum.clean_energy_saving.2,
    ResearchBankV27.GlobalConductorSum.clean_discrepancy_saving.1,
    ResearchBankV27.GlobalConductorSum.clean_discrepancy_saving.2⟩

end ExactParameterInstantiation
end ResearchBankV28
end Erdos287
