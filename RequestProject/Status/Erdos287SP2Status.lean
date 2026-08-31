import Mathlib
import RequestProject.Erdos287.SP2ClosureCompiler3221

/-!
# SP-2 machine status — direct Balanced7 source repair

Append-only.  The V20, V21 and V22 ledgers are untouched; this module records what the
SP-2 forensics pass changed.

Headline changes:

* `BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45` moves from *candidate* to
  `RETRACTED / NOT THE LITERAL SOURCE`.  The file is preserved.
* `BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45` becomes the controlling source dictionary;
  it is still `SOURCE_OPEN` (nobody has transcribed the identification), but the pointwise
  coefficient law it used to *assume* is now **proved** about the literal weight `V_{i,λ}`.
* Consequently the prime-box `L¹` normalisation now needs only the external prime count,
  and the first exact residual moves to the comparison splice.
* `BALANCED7` and `ERDOS287` remain `OPEN`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SP2Status

/-! ## The machine-readable SP-2 ledger -/

/-- The SP-2 status nodes. -/
inductive Node
  | ford723SourceAdapter
  | sp2DirectSourceAdapter
  | sp2FixedCertificateDivisorSum
  | sp2DivisorDepthThreshold
  | sp2AlternatingCoefficient
  | sp2PrimeBoxPointwiseLaw
  | primeBoxCardinalityInput
  | primeBoxL1Normalization
  | badCharacterSafeCount
  | cutoffCompatibility
  | physicalLogPrefactor
  | shortShiftSieveInterface
  | shiuInterface
  | outerTwoPrimeL2
  | twoProjectorClosure
  | inverseSampledHighCondLogVar
  | sixthMoment
  | comparisonSmallCondExceptionalSplice
  | balancedSeven
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The SP-2 status labels. -/
inductive Label
  | retractedNotLiteralSource
  | sourceOpenControlling
  | sourceOpen
  | finitePass
  | provedPass
  | externalAnalyticUninhabited
  | conditional
  | openConditional
  | openStrongerSufficientFallback
  | openNode
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The SP-2 ledger. -/
def ledger : Node → Label
  | ford723SourceAdapter => retractedNotLiteralSource
  | sp2DirectSourceAdapter => sourceOpenControlling
  | sp2FixedCertificateDivisorSum => sourceOpen
  | sp2DivisorDepthThreshold => provedPass
  | sp2AlternatingCoefficient => finitePass
  | sp2PrimeBoxPointwiseLaw => provedPass
  | primeBoxCardinalityInput => externalAnalyticUninhabited
  | primeBoxL1Normalization => conditional
  | badCharacterSafeCount => finitePass
  | cutoffCompatibility => sourceOpen
  | physicalLogPrefactor => sourceOpen
  | shortShiftSieveInterface => externalAnalyticUninhabited
  | shiuInterface => externalAnalyticUninhabited
  | outerTwoPrimeL2 => externalAnalyticUninhabited
  | twoProjectorClosure => conditional
  | inverseSampledHighCondLogVar => openConditional
  | sixthMoment => openStrongerSufficientFallback
  | comparisonSmallCondExceptionalSplice => sourceOpen
  | balancedSeven => openNode
  | erdos287 => openNode

/-- The SP-2 residual order; `0` means "not on the residual list". -/
def residualRank : Node → ℕ
  | comparisonSmallCondExceptionalSplice => 1
  | sp2DirectSourceAdapter => 2
  | physicalLogPrefactor => 3
  | cutoffCompatibility => 4
  | _ => 0

/-- **The Ford-(7.23) adapter is retracted as the literal source, and is not deleted.** -/
theorem fm723_adapter_retracted :
    ledger ford723SourceAdapter = retractedNotLiteralSource ∧
      retractedNotLiteralSource ≠ sourceOpenControlling ∧
      retractedNotLiteralSource ≠ provedPass := by
  decide +kernel

/-- **The SP-2 direct adapter is the controlling source dictionary, still source-open.** -/
theorem sp2_direct_adapter_controlling :
    ledger sp2DirectSourceAdapter = sourceOpenControlling ∧
      sourceOpenControlling ≠ provedPass ∧
      sourceOpenControlling ≠ finitePass := by
  decide +kernel

/-- **What SP-2 actually proved**: the divisor-depth threshold, the alternating
coefficient and the pointwise prime-box law. -/
theorem sp2_proved_layer :
    ledger sp2DivisorDepthThreshold = provedPass ∧
      ledger sp2AlternatingCoefficient = finitePass ∧
      ledger sp2PrimeBoxPointwiseLaw = provedPass ∧
      ledger badCharacterSafeCount = finitePass := by
  decide +kernel

/-- **The frontier has moved to the comparison splice** — and only now, after the
two-projector package's own source pins were resolved or made conditional. -/
theorem sp2_first_exact_residual_is_comparison :
    ledger comparisonSmallCondExceptionalSplice = sourceOpen ∧
      residualRank comparisonSmallCondExceptionalSplice = 1 ∧
      ∀ n : Node, residualRank n = 1 → n = comparisonSmallCondExceptionalSplice := by
  decide +kernel

/-- **Nothing closed.**  The sixth moment is still an open stronger fallback, the
log-variance node is still conditional, and both terminal nodes are open. -/
theorem sp2_terminal_nodes_open :
    ledger balancedSeven = openNode ∧ ledger erdos287 = openNode ∧
      ledger inverseSampledHighCondLogVar = openConditional ∧
      ledger sixthMoment = openStrongerSufficientFallback ∧
      ledger twoProjectorClosure = conditional := by
  decide +kernel

/-- **All external analytic interfaces remain uninhabited under SP-2.** -/
theorem sp2_external_interfaces_uninhabited :
    ledger shiuInterface = externalAnalyticUninhabited ∧
      ledger shortShiftSieveInterface = externalAnalyticUninhabited ∧
      ledger outerTwoPrimeL2 = externalAnalyticUninhabited ∧
      ledger primeBoxCardinalityInput = externalAnalyticUninhabited := by
  decide +kernel

end SP2Status
end Erdos287
