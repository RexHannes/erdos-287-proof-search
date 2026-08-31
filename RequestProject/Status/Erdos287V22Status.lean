import Mathlib
import RequestProject.Erdos287.TwoProjectorPhysicalClosure3221

/-!
# V22 machine status — source forensics safe bank

Append-only.  The V21 ledger (`Erdos287.V21Status`) is **not** modified; this module adds
the V22 nodes and records what the V22 forensics pass actually established.

What changed relative to V21:

* `BADCHAR-D2-RELEDGER45` — the safe `(D+1)²` bad-character count was pushed through the
  log arithmetic, producing the `B0`-dependent variance exponent
  `C_var(B0) = min(5, 15/2 − 2B0, 10 − 4B0)`.  This is a `FINITE PASS`.
* `BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45` — a candidate source dictionary was banked as
  an **uninhabited** interface.  It is a candidate, not the source.
* `BALANCED7-PRIMEBOX-L1-NORMALIZATION45` — still `SOURCE_OPEN`; V22 only supplies the
  conditional compiler from (dictionary + prime count) to the `L¹` bound.
* Everything else keeps its V21 status.

No node moved to a closed state.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V22Status

/-! ## The machine-readable V22 ledger -/

/-- The V22 status nodes. -/
inductive Node
  | v21TwoProjectorAlgebra
  | badCharacterD2Reledger
  | ford723SourceAdapter
  | primeBoxCardinalityInput
  | primeBoxL1Normalization
  | cutoffCompatibility
  | physicalLogPrefactor
  | shortShiftSieveInterface
  | shiuInterface
  | outerTwoPrimeL2
  | twoProjectorPhysicalClosure
  | inverseSampledHighCondLogVar
  | sixthMoment
  | comparison
  | balancedSeven
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The V22 status labels. -/
inductive Label
  | banked
  | finitePass
  | candidateSourceUninhabited
  | externalAnalyticUninhabited
  | sourceOpen
  | conditional
  | openConditional
  | openStrongerSufficientFallback
  | openNode
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The V22 ledger. -/
def ledger : Node → Label
  | v21TwoProjectorAlgebra => banked
  | badCharacterD2Reledger => finitePass
  | ford723SourceAdapter => candidateSourceUninhabited
  | primeBoxCardinalityInput => externalAnalyticUninhabited
  | primeBoxL1Normalization => sourceOpen
  | cutoffCompatibility => sourceOpen
  | physicalLogPrefactor => sourceOpen
  | shortShiftSieveInterface => externalAnalyticUninhabited
  | shiuInterface => externalAnalyticUninhabited
  | outerTwoPrimeL2 => externalAnalyticUninhabited
  | twoProjectorPhysicalClosure => conditional
  | inverseSampledHighCondLogVar => openConditional
  | sixthMoment => openStrongerSufficientFallback
  | comparison => sourceOpen
  | balancedSeven => openNode
  | erdos287 => openNode

/-- The residual order after the V22 pass; `0` means "not on the residual list". -/
def residualRank : Node → ℕ
  | primeBoxL1Normalization => 1
  | cutoffCompatibility => 2
  | physicalLogPrefactor => 3
  | comparison => 4
  | _ => 0

/-- **The `D²` re-ledger is a finite pass and is banked as such.** -/
theorem badCharacter_d2_reledger_finite_pass :
    ledger badCharacterD2Reledger = finitePass ∧ finitePass ≠ sourceOpen ∧
      finitePass ≠ conditional := by
  decide +kernel

/-- **The Ford-(7.23) adapter is a candidate, not a source theorem.** -/
theorem ford723_adapter_is_candidate_only :
    ledger ford723SourceAdapter = candidateSourceUninhabited ∧
      candidateSourceUninhabited ≠ banked ∧
      candidateSourceUninhabited ≠ finitePass := by
  decide +kernel

/-- **The first exact residual is unchanged by V22.** -/
theorem first_exact_residual_v22 :
    ledger primeBoxL1Normalization = sourceOpen ∧
      residualRank primeBoxL1Normalization = 1 ∧
      ∀ n : Node, residualRank n = 1 → n = primeBoxL1Normalization := by
  decide +kernel

/-- **Comparison did not become the frontier.** -/
theorem comparison_still_not_first_residual_v22 :
    ledger comparison = sourceOpen ∧
      residualRank primeBoxL1Normalization < residualRank comparison := by
  decide +kernel

/-- **No V22 node is closed.** -/
theorem terminal_nodes_open_v22 :
    ledger balancedSeven = openNode ∧ ledger erdos287 = openNode ∧
      ledger inverseSampledHighCondLogVar = openConditional ∧
      ledger sixthMoment = openStrongerSufficientFallback := by
  decide +kernel

/-- **All external analytic interfaces remain uninhabited.** -/
theorem external_interfaces_uninhabited_v22 :
    ledger shiuInterface = externalAnalyticUninhabited ∧
      ledger shortShiftSieveInterface = externalAnalyticUninhabited ∧
      ledger outerTwoPrimeL2 = externalAnalyticUninhabited ∧
      ledger primeBoxCardinalityInput = externalAnalyticUninhabited := by
  decide +kernel

end V22Status
end Erdos287
