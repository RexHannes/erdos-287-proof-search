import Mathlib
import RequestProject.Erdos287.PhysicalLogPrefactorRepair3221
import RequestProject.Erdos287.SP2ClosureCompiler3221

/-!
# CurrentProgramme §2 — the log-`r` repair bank

`C-EXT-LOGR-REPAIR45`

Append-only.  Nothing in the historical V20/V21/V22/SP-2/V23/V24 banks is modified.

What is banked here:

* the **source-minimal identity**
  `Λ(n) = ∑_{q·r = n} μ(q) · log r`,
  proved from the Mathlib Dirichlet-convolution identity `μ * log = Λ`, together with its
  literal affine specialisation at `n = 2·P + s`;
* the retraction record for the historical normalisation `C_ext = 0`
  (`RETRACTED / INCOMPLETE NORMALISATION`) and the current value `C_ext = 1`;
* the exact exponent arithmetic `C_var = 5`, `C_var − 2·C_ext = 5 − 2 = 3 > 0`;
* the **firewall** `logR_ledger_does_not_give_analytic`: the positive exponent margin is a
  rational-arithmetic fact and does *not* inhabit any analytic transfer interface.

No analytic theorem is asserted here, and no interface is inhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ArithmeticFunction
open scoped BigOperators

namespace Erdos287
namespace CurrentProgramme

/-! ## §2.1  The source-minimal log-`r` identity -/

/-- **`vonMangoldt_eq_sum_moebius_mul_logR`.**  `LEAN_PROVED`.

The source-minimal identity actually used by the Balanced7 packet:
`Λ(n) = ∑_{q·r = n} μ(q) · log r`.
The Möbius factor sits on `q`, the logarithm on the cofactor `r`. -/
theorem vonMangoldt_eq_sum_moebius_mul_logR (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal, (moebius x.1 : ℝ) * Real.log x.2 = Λ n := by
  have h : ((moebius : ArithmeticFunction ℝ) * log) n = Λ n := by
    rw [moebius_mul_log_eq_vonMangoldt]
  rw [ArithmeticFunction.mul_apply] at h
  simpa [ArithmeticFunction.log_apply] using h

/-- **`affine_vonMangoldt_eq_sum_moebius_mul_logR`.**  `LEAN_PROVED`.

The literal affine specialisation `n = 2·P + s` used by the SP-2 packet. -/
theorem affine_vonMangoldt_eq_sum_moebius_mul_logR (P s : ℕ) :
    ∑ x ∈ (2 * P + s).divisorsAntidiagonal, (moebius x.1 : ℝ) * Real.log x.2 =
      Λ (2 * P + s) :=
  vonMangoldt_eq_sum_moebius_mul_logR _

/-! ## §2.2  The `C_ext` retraction record -/

/-- The historical physical log prefactor.  `RETRACTED / INCOMPLETE NORMALISATION`. -/
def cExtRetracted : ℚ := 0

/-- The current physical log prefactor, `C_ext = 1`; definitionally the V24 repaired value. -/
def cExtCurrent : ℚ := V24Prefactor.sp2CextRepaired

theorem cExtCurrent_eq_one : cExtCurrent = 1 := rfl

theorem cExtRetracted_ne_cExtCurrent : cExtRetracted ≠ cExtCurrent := by decide +kernel

/-- **`cExt_retraction_is_a_theorem`.**  `LEAN_PROVED`.

The retraction is not bookkeeping: no rational value satisfies both the old SP-2 prefactor
interface and the repaired one, and the current value satisfies the repaired one. -/
theorem cExt_retraction_is_a_theorem :
    V24Prefactor.SP2PhysicalLogPrefactorRepaired cExtCurrent ∧
      ∀ c : ℚ, ¬ (SP2Closure.PhysicalLogPrefactorSP23221 c ∧
        V24Prefactor.SP2PhysicalLogPrefactorRepaired c) :=
  ⟨V24Prefactor.sp2CextRepaired_spec, V24Prefactor.oldPrefactor_and_repaired_are_incompatible⟩

/-! ## §2.3  The exact exponent arithmetic -/

/-- The variance log exponent of the controlling SP-2 cell, `C_var = 5`. -/
def cVarCurrent : ℚ := V22Ledger.cvar SP2Closure.sp2B0

theorem cVarCurrent_eq_five : cVarCurrent = 5 := SP2Closure.sp2_cvar_eq_five

/-- **`logR_signed_margin`.**  `LEAN_PROVED` (exact rational arithmetic).

`C_var − 2·C_ext = 5 − 2 = 3 > 0`. -/
theorem logR_signed_margin :
    cVarCurrent - 2 * cExtCurrent = 3 ∧ 0 < cVarCurrent - 2 * cExtCurrent := by
  rw [cVarCurrent_eq_five, cExtCurrent_eq_one]
  norm_num

/-- **`logR_net_exponent`.**  `LEAN_PROVED`.

With `C_ext = 1` the net log exponent of the controlling cell is `−5/2 < −1`. -/
theorem logR_net_exponent :
    V22Closure.netLogExponent cVarCurrent cExtCurrent = -5 / 2 ∧
      V22Closure.netLogExponent cVarCurrent cExtCurrent < -1 :=
  ⟨V24Prefactor.q35_netLogExponent_eq_neg_five_halves,
   V24Prefactor.q35_netLogExponent_lt_neg_one⟩

/-! ## §2.4  The firewall -/

/-- An analytic transfer interface: a claimed `bound / log X` saving for a remainder
function `rem`, *carrying* the exponent ledger.  `EXTERNAL`. -/
structure LogRAnalyticTransferInput (rem : ℝ → ℝ) (bound : ℝ) : Prop where
  /-- The exponent ledger that motivates the interface. -/
  ledger : cVarCurrent - 2 * cExtCurrent = 3
  /-- The analytic content, which the ledger does *not* supply. -/
  saving : ∀ X : ℝ, 2 ≤ X → |rem X| ≤ bound / Real.log X

/-- **`logR_ledger_does_not_give_analytic`.**  `LEAN_PROVED`.

The exponent ledger holds, yet the analytic transfer interface is a genuine extra
hypothesis: it fails for an explicit `(rem, bound)` pair.  No analytic theorem may be
inferred from the exponent ledger alone. -/
theorem logR_ledger_does_not_give_analytic :
    (cVarCurrent - 2 * cExtCurrent = 3) ∧
      ∃ (rem : ℝ → ℝ) (bound : ℝ), ¬ LogRAnalyticTransferInput rem bound := by
  refine ⟨logR_signed_margin.1, fun _ => 1, 0, ?_⟩
  intro h
  have h2 : |(1 : ℝ)| ≤ (0 : ℝ) / Real.log 2 := h.saving 2 le_rfl
  rw [abs_one, zero_div] at h2
  linarith

end CurrentProgramme
end Erdos287
