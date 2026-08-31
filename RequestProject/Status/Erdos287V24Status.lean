import Mathlib
import RequestProject.Erdos287.EulerUniformityLayer3221
import RequestProject.Erdos287.SP2LiteralPhysicalSource3221
import RequestProject.Erdos287.BalancedSevenFullQCompiler3221

/-!
# V24 machine status — full-`q` Balanced7 provider-exhaustiveness safe bank

Append-only.  The V20, V21, V22, SP-2 and V23 ledgers are untouched; this module records
the V24 layer.

## What changed in V24

```
    SP2PhysicalLogPrefactorOld  (C_ext = 0) : RETRACTED / INCOMPLETE NORMALIZATION
    3221-PHYSICAL-LOG-PREFAC45  (C_ext = 1) : REPAIRED
    BALANCED7-EULER-UNIFORMITY45            : RESEARCH PASS  (external, uninhabited)
    BALANCED7-QPACKET-STRUCTURAL-PARTITION45: PASS  (finite, kernel-checked)
    Q = X^{3/5} hard cell                   : RESEARCH CLOSURE CANDIDATE
    AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45    : OPEN  (first exact residual)
    AFFINE287-SP2-SMALLR-SWITCHED-TYPEI45   : OPEN
    other hard dyadic cells                 : OPEN / UNCENSUSED
    BALANCED7-QPACKET-PROVIDER-EXHAUSTIVENESS45 : OPEN / FAILS as a global claim
    SP2-BALANCED7-FULL-Q45                  : OPEN (conditional compiler only)
    ERDOS287                                : OPEN
```

The post-Balanced7 census is **not** activated, and it is explicitly *not* recorded that the
future packet universe is a finite `Ω`-list: bounded fragmentation templates and parametric
polytopal families may be required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V24Status

/-! ## §1  The ledger -/

/-- The V24 status nodes. -/
inductive Node
  | oldPhysicalLogPrefactor
  | repairedPhysicalLogPrefactor
  | q35LocalCapacity
  | literalPhysicalSource
  | eulerLocalAlgebra
  | eulerUniformityInput
  | qPacketStructuralPartition
  | hardDyadicQ35Cell
  | hardDyadicOtherCells
  | smallQTypeIAdapter
  | smallRSwitchedTypeI
  | qPacketProviderExhaustiveness
  | sp2BalancedSevenFullQ
  | balancedSevenAsymptotic
  | balancedSevenEffective
  | postBalancedSevenCensus
  | packetUniverseFiniteOmegaList
  | fcl
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The V24 status labels. -/
inductive Label
  | retractedIncompleteNormalization
  | provedPass
  | researchPass
  | researchClosureCandidate
  | externalUninhabited
  | openUncensused
  | openFail
  | openConditional
  | openNode
  | notReached
  | notEstablished
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The V24 ledger. -/
def ledger : Node → Label
  | oldPhysicalLogPrefactor => retractedIncompleteNormalization
  | repairedPhysicalLogPrefactor => provedPass
  | q35LocalCapacity => provedPass
  | literalPhysicalSource => provedPass
  | eulerLocalAlgebra => provedPass
  | eulerUniformityInput => researchPass
  | qPacketStructuralPartition => provedPass
  | hardDyadicQ35Cell => researchClosureCandidate
  | hardDyadicOtherCells => openUncensused
  | smallQTypeIAdapter => externalUninhabited
  | smallRSwitchedTypeI => externalUninhabited
  | qPacketProviderExhaustiveness => openFail
  | sp2BalancedSevenFullQ => openConditional
  | balancedSevenAsymptotic => openConditional
  | balancedSevenEffective => openNode
  | postBalancedSevenCensus => notReached
  | packetUniverseFiniteOmegaList => notEstablished
  | fcl => openNode
  | erdos287 => openNode

/-- The exact residual order; `0` means "not on the residual list". -/
def residualRank : Node → ℕ
  | smallQTypeIAdapter => 1
  | smallRSwitchedTypeI => 2
  | hardDyadicOtherCells => 3
  | qPacketProviderExhaustiveness => 4
  | _ => 0

/-! ## §2  The prefactor repair -/

/-- **`v24_prefactor_repaired`.**  `LEAN_PROVED`.

The old `C_ext = 0` physical log prefactor is retracted as an incomplete normalisation, and
the retraction is a theorem: no exponent satisfies both interfaces. -/
theorem v24_prefactor_repaired :
    ledger oldPhysicalLogPrefactor = retractedIncompleteNormalization ∧
      ledger repairedPhysicalLogPrefactor = provedPass ∧
      retractedIncompleteNormalization ≠ provedPass ∧
      (∀ cext : ℚ, ¬ (Erdos287.SP2Closure.PhysicalLogPrefactorSP23221 cext ∧
        Erdos287.V24Prefactor.SP2PhysicalLogPrefactorRepaired cext)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact Erdos287.V24Prefactor.oldPrefactor_and_repaired_are_incompatible

/-- **`v24_q35_local_numerology`.**  `LEAN_PROVED`.

With `C_ext = 1` the `Q = X^{3/5}` cell has net log exponent `−5/2` and signed margin `3`. -/
theorem v24_q35_local_numerology :
    Erdos287.V22Closure.netLogExponent (Erdos287.V22Ledger.cvar Erdos287.SP2Closure.sp2B0)
        Erdos287.V24Prefactor.sp2CextRepaired = -5 / 2 ∧
      Erdos287.V22Ledger.cvar Erdos287.SP2Closure.sp2B0 -
        2 * Erdos287.V24Prefactor.sp2CextRepaired = 3 :=
  ⟨Erdos287.V24Prefactor.q35_netLogExponent_eq_neg_five_halves,
   Erdos287.V24Prefactor.q35_signed_log_margin.1⟩

/-! ## §3  Finite passes and external inputs -/

/-- **`v24_finite_layer_proved`.**  `LEAN_PROVED`.

The finite layers of V24 — the structural `q`-partition, the Euler local-factor algebra,
the literal physical source and the repaired prefactor — are banked as proved. -/
theorem v24_finite_layer_proved :
    ledger qPacketStructuralPartition = provedPass ∧
      ledger eulerLocalAlgebra = provedPass ∧
      ledger literalPhysicalSource = provedPass ∧
      ledger repairedPhysicalLogPrefactor = provedPass ∧
      ledger q35LocalCapacity = provedPass := by
  decide +kernel

/-- **`v24_external_layer_uninhabited`.**  `LEAN_PROVED`.

The aggregate-Euler uniformity input and both small-sector Type-I adapters are external
interfaces, none of them inhabited, and `researchPass` is not `provedPass`. -/
theorem v24_external_layer_uninhabited :
    ledger eulerUniformityInput = researchPass ∧
      ledger smallQTypeIAdapter = externalUninhabited ∧
      ledger smallRSwitchedTypeI = externalUninhabited ∧
      researchPass ≠ provedPass ∧ externalUninhabited ≠ provedPass := by
  decide +kernel

/-! ## §4  The provider census -/

/-- **`v24_provider_exhaustiveness_fails`.**  `LEAN_PROVED`.

`BALANCED7-QPACKET-PROVIDER-EXHAUSTIVENESS45` is recorded as failing *as a global claim*,
and this is a theorem: the hard dyadic census leaves admissible cells unowned, so the
exhaustiveness interface is refuted, and consequently the full-`q` antecedent bundle is
satisfied by no parameter set. -/
theorem v24_provider_exhaustiveness_fails :
    ledger qPacketProviderExhaustiveness = openFail ∧
      ledger hardDyadicOtherCells = openUncensused ∧
      ¬ Erdos287.V24Hard.HardDyadicProviderExhaustiveness287Input ∧
      (∀ prm : Erdos287.V24FullQCompiler.FullQParams,
        ¬ Erdos287.V24FullQCompiler.BalancedSevenAllQProviderInputs prm) := by
  refine ⟨by decide +kernel, by decide +kernel,
    Erdos287.V24Hard.hardDyadicExhaustiveness_not_automatic, ?_⟩
  exact Erdos287.V24FullQCompiler.allQProviderInputs_currently_unavailable

/-- **`v24_q35_is_one_cell_only`.**  `LEAN_PROVED`.

The `Q = X^{3/5}` cell is a research closure candidate for **one** dyadic cell; a packet
record exists only for the exponent `3/5`. -/
theorem v24_q35_is_one_cell_only :
    ledger hardDyadicQ35Cell = researchClosureCandidate ∧
      researchClosureCandidate ≠ provedPass ∧
      (∀ e : ℚ, Erdos287.V24Hard.HardDyadicBalancedSevenPacket e → e =
        Erdos287.V24FullQ.q35Exponent) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact fun e h => Erdos287.V24Hard.hardDyadic_owner_only_q35 h

/-! ## §5  Residuals -/

/-- **`v24_first_exact_residual`.**  `LEAN_PROVED`.

The first exact residual is `AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45`, followed by the
switched SmallR adapter, the uncensused hard dyadic cells, and provider exhaustiveness. -/
theorem v24_first_exact_residual :
    residualRank smallQTypeIAdapter = 1 ∧
      residualRank smallRSwitchedTypeI = 2 ∧
      residualRank hardDyadicOtherCells = 3 ∧
      residualRank qPacketProviderExhaustiveness = 4 ∧
      (∀ n : Node, residualRank n = 1 → n = smallQTypeIAdapter) := by
  decide +kernel

/-- **`v24_census_not_activated`.**  `LEAN_PROVED`.

The post-Balanced7 census is not reached, is not on the residual list, and it is **not**
recorded that the future packet universe is a finite `Ω`-list. -/
theorem v24_census_not_activated :
    ledger postBalancedSevenCensus = notReached ∧
      residualRank postBalancedSevenCensus = 0 ∧
      ledger packetUniverseFiniteOmegaList = notEstablished ∧
      notEstablished ≠ provedPass ∧ notReached ≠ researchClosureCandidate := by
  decide +kernel

/-! ## §6  Terminal nodes -/

/-- **`v24_effectivity_separate`.**  `LEAN_PROVED`.

Asymptotic and effective Balanced7 remain distinct entries, and the effective one is open;
moreover an ineffective exceptional treatment supplies no explicit threshold. -/
theorem v24_effectivity_separate :
    ledger balancedSevenAsymptotic = openConditional ∧
      ledger balancedSevenEffective = openNode ∧
      openConditional ≠ openNode ∧
      (∀ R : Erdos287.V23LowCond.BalancedSevenStatusRecord,
        Erdos287.V23LowCond.WellFormedStatus R → R.exceptionalIneffective = true →
          R.explicitThreshold = none ∧ R.effectiveClosed = false) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact fun R hw hine => Erdos287.V24FullQCompiler.fullQ_status_stays_open R hw hine

/-- **`v24_fullQ_and_erdos287_open`.**  `LEAN_PROVED`.

`SP2-BALANCED7-FULL-Q45`, the FCL node and Erdős #287 are all recorded OPEN. -/
theorem v24_fullQ_and_erdos287_open :
    ledger sp2BalancedSevenFullQ = openConditional ∧
      ledger fcl = openNode ∧
      ledger erdos287 = openNode ∧
      openNode ≠ provedPass ∧ openConditional ≠ provedPass ∧
      openNode ≠ researchClosureCandidate := by
  decide +kernel

end V24Status
end Erdos287
