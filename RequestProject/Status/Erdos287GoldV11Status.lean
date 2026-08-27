import RequestProject.Erdos287.PlacedLCBeta
import RequestProject.Erdos287.LogCofactorAsymptotic
import RequestProject.Erdos287.FixedCertificateTransference
import RequestProject.Erdos287.KummerFiniteCompiler
import RequestProject.Erdos287.KummerRootStabilizer
import RequestProject.Erdos287.KummerWeilInterface
import RequestProject.Erdos287.KummerExponentLedger
import RequestProject.Erdos287.FixedCertificateLeakageCompiler

/-!
# Status ledger for the V11 reproof / Leanification run

**Erdős #287 remains OPEN.**  Nothing in this run proves it, and no theorem here or in
the files it imports claims otherwise.

This file prints the axiom dependencies of every theorem added in the run and records
two purely logical facts about the route structure (Part I of the request).

## What is kernel-checked in this run

| Item | Lean name |
| --- | --- |
| repaired placement predicate | `Erdos287.PlacedLCBeta` |
| placement lemma | `Erdos287.Gap2CE.N_le_of_M_le_two_mul` |
| compiler to the banked blocker | `Erdos287.Gap2CE.no_of_placedLCBeta` |
| log-cofactor asymptotic | `Erdos287.logCofactor_asymptotic287` |
| transference kernel | `Erdos287.Transference.sum_a_P_lower` / `sum_a_P_pos` |
| Kummer finite compiler | `Erdos287.Kummer.kummer_bilinear_of_correlation_bounds` |
| root-stabilizer algebra | `Erdos287.Kummer.quadratic_scaling_square_criterion` |
| exponent ledger | `Erdos287.KummerLedger.kummer_savings_bound` |
| leakage compiler | `Erdos287.FixedCertificate.fixedCertificate_leakage_compiler` |

## What is *not* proved (external, and left as explicit antecedents)

* the Weil / interval-completion correlation bound
  (`Erdos287.Kummer.QuadraticKummerCorrelationBound` — an interface, never inhabited);
* the analytic estimate `287-FIXED-CERTIFICATE-LEAKAGE45`
  (`Erdos287.FixedCertificate.LeakageBound` — a hypothesis, never assumed);
* the arithmetic supply `PlacedLCBeta M (Jlog η M)` for large `M`.
-/

namespace Status
namespace Erdos287GoldV11

open Erdos287

/-! ## Part I — route firewall (logical facts only)

The retired routes (`FullFMTypeII_1/6`, generated Ford (7.23) packets, `SOURCE-ADAPTER45`,
the global replacement certificate `C_FM`) are **preserved untouched** elsewhere in the
project; nothing here deletes, weakens or contradicts them.  The only claim made is the
trivial sufficiency below: *if* the fixed-certificate hypotheses hold, the prime-mass
conclusion follows.  No claim of relative logical strength is made. -/

/-- **Route sufficiency (restatement).**  The fixed-certificate leakage route is a
sufficient route to a positive prime-mass lower bound *when its own hypotheses are
present*. -/
theorem fixedCertificateRoute_sufficient
    (d : FixedCertificate.FixedCertificateData) (Cc E delta : ℝ)
    (hLeak : FixedCertificate.LeakageBound d E)
    (hTotal : FixedCertificate.TotalCorrelationBound d E)
    (hMargin : FixedCertificate.ComparisonMargin d Cc E)
    (hBpos : 0 < d.B) (hE : E ≤ delta * d.B) (hdelta : 3 * delta < 1 + Cc) :
    0 < ∑ p ∈ d.P, d.a p :=
  FixedCertificate.fixedCertificate_prime_mass_pos d Cc E delta hLeak hTotal hMargin
    hBpos hE hdelta

/-! ## Axiom prints -/

-- Part A: LCBeta placement repair
#print axioms Erdos287.placedLCBeta_imp_LCBeta
#print axioms Erdos287.lcBeta_witness_below_half
#print axioms Erdos287.Gap2CE.N_le_of_M_le_two_mul
#print axioms Erdos287.Gap2CE.no_of_placedLCBeta
#print axioms Erdos287.Gap2CE.not_placedLCBeta_of_counterexample

-- Part B: the log-cofactor asymptotic
#print axioms Erdos287.log_le_two_sqrt
#print axioms Erdos287.log_sq_lt_self
#print axioms Erdos287.logCofactor_asymptotic287
#print axioms Erdos287.placedLCBeta_of_adjacent_large_prime_factors

-- Part C: fixed-certificate transference
#print axioms Erdos287.Transference.sum_a_P_identity
#print axioms Erdos287.Transference.sum_a_P_lower
#print axioms Erdos287.Transference.sum_a_P_pos
#print axioms Erdos287.Transference.transference_nonvacuous

-- Part D1: the finite Cauchy / correlation compiler
#print axioms Erdos287.Kummer.abs_mul_abs_le_half_add
#print axioms Erdos287.Kummer.exceptional_double_sum_le
#print axioms Erdos287.Kummer.kummer_bilinear_of_correlation_bounds

-- Part D2: root-stabilizer algebra
#print axioms Erdos287.Kummer.quadPoly_comp_scale
#print axioms Erdos287.Kummer.quadPoly_separable
#print axioms Erdos287.Kummer.quadPoly_squarefree
#print axioms Erdos287.Kummer.exists_const_of_scaling_square
#print axioms Erdos287.Kummer.quadratic_scaling_square_criterion
#print axioms Erdos287.Kummer.quadratic_scaling_square_criterion_of_b_ne_zero
#print axioms Erdos287.Kummer.scalingSquareStabilizer_subset
#print axioms Erdos287.Kummer.scalingSquareStabilizer_ncard_le_two
#print axioms Erdos287.Kummer.repeated_root_scaling_square

-- Part D3: Weil / completion interface
#print axioms Erdos287.Kummer.pmExceptional_card_le_two
#print axioms Erdos287.Kummer.pmExceptional_symm
#print axioms Erdos287.Kummer.kummer_bilinear_of_interface
#print axioms Erdos287.Kummer.not_square_of_not_pmExceptional

-- Part E: exponent ledger
#print axioms Erdos287.KummerLedger.exponent_ledger
#print axioms Erdos287.KummerLedger.exponent_ledger_max
#print axioms Erdos287.KummerLedger.exponent_ledger_endpoint_low
#print axioms Erdos287.KummerLedger.exponent_ledger_endpoint_high
#print axioms Erdos287.KummerLedger.exponent_ledger_fails_above_eight
#print axioms Erdos287.KummerLedger.kummer_savings_bound
#print axioms Erdos287.KummerLedger.margin_Y_eq_X

-- Part H: fixed-certificate leakage compiler
#print axioms Erdos287.FixedCertificate.fixedCertificate_leakage_compiler
#print axioms Erdos287.FixedCertificate.fixedCertificate_leakage_compiler_N2
#print axioms Erdos287.FixedCertificate.fixedCertificate_prime_mass_pos

-- Part I: route sufficiency
#print axioms Status.Erdos287GoldV11.fixedCertificateRoute_sufficient

end Erdos287GoldV11
end Status
