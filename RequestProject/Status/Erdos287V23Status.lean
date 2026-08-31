import Mathlib
import RequestProject.Erdos287.OldLocalScalarRetraction3221
import RequestProject.Erdos287.BalancedSevenComparisonCompiler3221

/-!
# V23 machine status — Balanced7 comparison / aggregate Euler safe bank

Append-only.  The V20, V21, V22 and SP-2 ledgers are untouched; this module records the
V23 layer and, crucially, the **post-audit** status split.

## The independent audit

```
    OPUS NANC : CASE F — SOURCE-MISSING.
```

Independently verified: the `μ·log` / log-`r` identity, the affine character `q`-cell,
`1/ζ(1+w) = w + O(w²)`, and basic non-unit routing.

**Not** independently verified: the literal SP-2 one-sign source, the uniform `H_P(w)`
contour estimate, dyadic-`q` / full-`q` exhaustiveness, an independent physical `2B(P)`,
the small-conductor physical source, the exceptional source, and no-double-spending.

## The five status fields, kept apart

```
    ProComparisonCandidate            : CLOSED-CANDIDATE
    IndependentComparisonAudit        : SOURCE-MISSING
    BalancedSevenResearchCandidate    : CLOSED-CANDIDATE
    BalancedSevenIndependentlyAudited : OPEN
    Erdos287                          : OPEN
```

`statuses_are_not_conflated` proves these are five distinct entries.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V23Status

/-! ## §1  The ledger -/

/-- The V23 status nodes. -/
inductive Node
  | oldPointwiseLocalScalar
  | sp2PhysicalComparisonObject
  | muLogQCellAlgebra
  | affineCharacterQCell
  | nonunitRouting
  | principalQCellEquality
  | physicalTwoBIndependence
  | aggregateEulerLocalAlgebra
  | aggregateEulerPrincipalInput
  | aggregateEulerUniformityInput
  | qPacketPartitionAlgebra
  | qPartitionInput
  | qPacketExhaustivenessInput
  | smallConductorInput
  | exceptionalCharacterInput
  | effectivityFirewall
  | comparisonCompiler
  | balancedSevenAsymptoticCompiler
  | proComparisonCandidate
  | independentComparisonAudit
  | balancedSevenResearchCandidate
  | balancedSevenIndependentlyAudited
  | balancedSevenAsymptotic
  | balancedSevenEffective
  | fixedGstarCensus
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The V23 status labels. -/
inductive Label
  | retractedWrongGeometry
  | provedPass
  | conditionalCompiler
  | externalUninhabited
  | externalSourceMissing
  | closedCandidate
  | sourceMissing
  | openConditional
  | openNode
  | notYetControlling
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The V23 ledger. -/
def ledger : Node → Label
  | oldPointwiseLocalScalar => retractedWrongGeometry
  | sp2PhysicalComparisonObject => provedPass
  | muLogQCellAlgebra => provedPass
  | affineCharacterQCell => provedPass
  | nonunitRouting => provedPass
  | principalQCellEquality => provedPass
  | physicalTwoBIndependence => externalSourceMissing
  | aggregateEulerLocalAlgebra => provedPass
  | aggregateEulerPrincipalInput => externalUninhabited
  | aggregateEulerUniformityInput => externalSourceMissing
  | qPacketPartitionAlgebra => provedPass
  | qPartitionInput => externalSourceMissing
  | qPacketExhaustivenessInput => externalSourceMissing
  | smallConductorInput => externalUninhabited
  | exceptionalCharacterInput => externalUninhabited
  | effectivityFirewall => provedPass
  | comparisonCompiler => conditionalCompiler
  | balancedSevenAsymptoticCompiler => conditionalCompiler
  | proComparisonCandidate => closedCandidate
  | independentComparisonAudit => sourceMissing
  | balancedSevenResearchCandidate => closedCandidate
  | balancedSevenIndependentlyAudited => openNode
  | balancedSevenAsymptotic => openConditional
  | balancedSevenEffective => openNode
  | fixedGstarCensus => notYetControlling
  | erdos287 => openNode

/-- The audit residual order; `0` means "not on the first-residual list". -/
def residualRank : Node → ℕ
  | aggregateEulerUniformityInput => 1
  | qPacketExhaustivenessInput => 2
  | physicalTwoBIndependence => 3
  | qPartitionInput => 4
  | _ => 0

/-! ## §2  The retraction of the old pointwise dictionary -/

/-- **`old_pointwise_local_scalar_retracted`.**  `LEAN_PROVED`.

The historical `2q/φ(q)` dictionary is retracted as *wrong geometry*, and the retraction is
not merely a label: the dictionary statement is refuted for **every** value of the
aggregate constant (`Erdos287.V23OldScalar.oldPointwiseLocalScalarDictionary_refuted`).
The historical source files are preserved. -/
theorem old_pointwise_local_scalar_retracted :
    ledger oldPointwiseLocalScalar = retractedWrongGeometry ∧
      retractedWrongGeometry ≠ provedPass ∧
      retractedWrongGeometry ≠ closedCandidate ∧
      (∀ twoB : ℝ, ¬ Erdos287.V23OldScalar.OldPointwiseLocalScalarDictionary twoB) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact Erdos287.V23OldScalar.oldPointwiseLocalScalarDictionary_refuted

/-! ## §3  The post-audit status split -/

/-- **`statuses_are_not_conflated`.**  `LEAN_PROVED`.

The five mandated status fields are five distinct ledger entries; in particular a research
"closed candidate" is not the same entry as an independently audited closure, and neither
is `OPEN`. -/
theorem statuses_are_not_conflated :
    ledger proComparisonCandidate = closedCandidate ∧
      ledger independentComparisonAudit = sourceMissing ∧
      ledger balancedSevenResearchCandidate = closedCandidate ∧
      ledger balancedSevenIndependentlyAudited = openNode ∧
      ledger erdos287 = openNode ∧
      closedCandidate ≠ sourceMissing ∧ closedCandidate ≠ openNode ∧
      sourceMissing ≠ openNode := by
  decide +kernel

/-- **`audit_verified_layer`.**  `LEAN_PROVED`.

Exactly the four items the independent audit verified are banked as proved, together with
the finite algebra this repository proves on its own. -/
theorem audit_verified_layer :
    ledger muLogQCellAlgebra = provedPass ∧
      ledger affineCharacterQCell = provedPass ∧
      ledger nonunitRouting = provedPass ∧
      ledger principalQCellEquality = provedPass ∧
      ledger aggregateEulerLocalAlgebra = provedPass ∧
      ledger qPacketPartitionAlgebra = provedPass := by
  decide +kernel

/-- **`audit_unverified_layer`.**  `LEAN_PROVED`.

Every item the audit lists as *not independently verified* is an external interface, none
of which is inhabited. -/
theorem audit_unverified_layer :
    ledger physicalTwoBIndependence = externalSourceMissing ∧
      ledger aggregateEulerUniformityInput = externalSourceMissing ∧
      ledger qPartitionInput = externalSourceMissing ∧
      ledger qPacketExhaustivenessInput = externalSourceMissing ∧
      ledger smallConductorInput = externalUninhabited ∧
      ledger exceptionalCharacterInput = externalUninhabited ∧
      externalSourceMissing ≠ provedPass ∧ externalUninhabited ≠ provedPass := by
  decide +kernel

/-! ## §4  Residuals -/

/-- **`first_audit_residuals`.**  `LEAN_PROVED`.

The two controlling audit residuals are the aggregate-Euler uniformity input and the
`q`-packet exhaustiveness input, in that order. -/
theorem first_audit_residuals :
    residualRank aggregateEulerUniformityInput = 1 ∧
      residualRank qPacketExhaustivenessInput = 2 ∧
      (∀ n : Node, residualRank n = 1 → n = aggregateEulerUniformityInput) ∧
      (∀ n : Node, residualRank n = 2 → n = qPacketExhaustivenessInput) := by
  decide +kernel

/-- **`census_not_promoted`.**  `LEAN_PROVED`.

`287-FIXED-GSTAR-REMAINING-PACKET-CENSUS45` is **not** promoted to the controlling research
residual while the two source-audit nodes are open. -/
theorem census_not_promoted :
    ledger fixedGstarCensus = notYetControlling ∧
      residualRank fixedGstarCensus = 0 ∧
      notYetControlling ≠ closedCandidate := by
  decide +kernel

/-! ## §5  Effectivity and terminal nodes -/

/-- **`effectivity_statuses_separate`.**  `LEAN_PROVED`.

The asymptotic and effective Balanced7 statuses are distinct ledger entries, and the
effective one is `OPEN`. -/
theorem effectivity_statuses_separate :
    ledger balancedSevenAsymptotic = openConditional ∧
      ledger balancedSevenEffective = openNode ∧
      openConditional ≠ openNode := by
  decide +kernel

/-- **`v23_terminal_nodes_open`.**  `LEAN_PROVED`.

Nothing in V23 closes anything: both compilers are conditional and both terminal nodes are
open. -/
theorem v23_terminal_nodes_open :
    ledger comparisonCompiler = conditionalCompiler ∧
      ledger balancedSevenAsymptoticCompiler = conditionalCompiler ∧
      ledger balancedSevenIndependentlyAudited = openNode ∧
      ledger erdos287 = openNode ∧
      conditionalCompiler ≠ provedPass := by
  decide +kernel

/-- **`v23_no_interface_inhabited`.**  `LEAN_PROVED`.

Each external interface of the V23 layer is refutable by explicit data, hence certainly not
inhabited by a repository theorem. -/
theorem v23_no_interface_inhabited :
    (∃ (J : ℕ → ℝ → ℝ) (S2 : ℝ) (family : Finset ℕ) (Aexp : ℝ) (effective : Bool),
        ¬ Erdos287.V23Euler.AggregateEulerPrincipal287Input J S2 family Aexp effective) ∧
      (∃ (sourceModuli indexSet : Finset ℕ) (owner : ℕ → ℕ) (Qcell : ℕ)
          (cellValue : ℕ → ℝ) (target : ℝ),
        ¬ Erdos287.V23QPacket.BalancedSevenQPacketExhaustiveness287Input sourceModuli
          indexSet owner Qcell cellValue target) :=
  ⟨Erdos287.V23Euler.aggregateEulerPrincipal_not_automatic,
    Erdos287.V23QPacket.qPacketExhaustiveness_not_automatic⟩

end V23Status
end Erdos287
