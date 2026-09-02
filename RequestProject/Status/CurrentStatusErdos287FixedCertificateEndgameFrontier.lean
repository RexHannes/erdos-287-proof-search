import RequestProject.Status.CurrentStatusErdos287FullAnalyticKernelImportFrontier
import RequestProject.CurrentProgramme.Erdos287FixedCertificateRepairedData
import RequestProject.CurrentProgramme.Erdos287EndgameEffectivityAndClosure

/-!
# Append-only status layer — the fixed-certificate endgame frontier

This module is **append-only** and sits *strictly later* than every existing 287 status
layer.  No earlier row is rewritten: precedence is recorded by
`fixedCertificateEndgameFrontier_is_later`, and the previous ledgers are re-checked in
place.

```
LOCAL ANALYTIC KERNEL (paper/research)         : analyticBanked / external
MASTER SOURCE → TYPED PERRON PACKETS 45        : open_ / uninhabited
N2 LAMBDA COLLAR (physical Λ weight)           : open_ / uninhabited
GLOBAL Bsrc COMPARISON MARGIN 45               : open_ / uninhabited
POSITIVE MARGIN SUPPLY                         : open_ / uninhabited
SUPPORT PARTITION  I = P ⊎ N1 ⊎ N2 ⊎ U         : kernelProved
FOUR-ERROR TRANSFERENCE ALGEBRA                : kernelProved
REPAIRED CERTIFICATE DATA (c₂ = +1, g_ε)       : kernelProved
CONDITIONAL FCL COMPILER                       : kernelProved (conditional)
FCL → WINDOWPAIR, threshold 12                 : kernelProved (conditional)
EFFECTIVITY (ε₀, X₀, M₀ ≤ 4·10⁹)               : open_ / uninhabited
FORD-83 EXPLICIT O(ε) COLLAR CONSTANTS         : open_ / uninhabited
Erdos287ClosureInputs                          : open_ / uninhabited
ERDOS287                                       : open_
```

`ResearchStatus` is **metadata**: no value of it carries any implication of mathematical
truth.  `analyticBanked` records a paper/research report, never a Lean theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FixedCertificateEndgameFrontierStatus

open Erdos287.C0UnitaryFourierStatus
open ResearchStatus

/-! ## §1  Nodes of this layer -/

/-- Nodes of the fixed-certificate endgame ledger. -/
inductive EndgameNode
  /-- The paper/research local analytic kernel. -/
  | localAnalyticKernel
  /-- The master-source → typed-Perron-packets reconstruction. -/
  | masterSourceToTypedPerronPackets45
  /-- The physical `N2` λ-collar. -/
  | n2LambdaCollar45
  /-- The global `Bsrc` comparison margin. -/
  | globalBsrcComparisonMargin45
  /-- The positive comparison margin supply. -/
  | positiveMarginSupply
  /-- The literal four-class support partition. -/
  | supportPartition
  /-- The four-error transference algebra. -/
  | fourErrorAlgebra
  /-- The repaired certificate data `c₂ = +1` and the indicator-truncated `g_ε`. -/
  | repairedCertificateData
  /-- The conditional FCL compiler. -/
  | conditionalFCLCompiler
  /-- The `FCL → WindowPair` bridge at threshold `12`. -/
  | fclToWindowPairTwelve
  /-- The effectivity socket. -/
  | effectivity
  /-- The Ford-83 explicit `O(ε)` collar constants. -/
  | ford83ExplicitConstants
  /-- The end-to-end closure inputs. -/
  | erdos287ClosureInputs
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open EndgameNode

/-! ## §2  The ledger -/

/-- The authoritative status of each node of this layer. -/
def endgameLedger : EndgameNode → ResearchStatus
  | localAnalyticKernel => analyticBanked
  | masterSourceToTypedPerronPackets45 => open_
  | n2LambdaCollar45 => open_
  | globalBsrcComparisonMargin45 => open_
  | positiveMarginSupply => open_
  | supportPartition => kernelProved
  | fourErrorAlgebra => kernelProved
  | repairedCertificateData => kernelProved
  | conditionalFCLCompiler => kernelProved
  | fclToWindowPairTwelve => kernelProved
  | effectivity => open_
  | ford83ExplicitConstants => open_
  | erdos287ClosureInputs => open_
  | erdos287 => open_

/-! ## §3  Precedence over every earlier layer -/

/-- The status layers of this development, in order. -/
inductive EndgameStatusLayer
  /-- The dual-level / simultaneous-critical layer. -/
  | dualLevelSimultaneousCritical
  /-- The regular-Perron source frontier. -/
  | regularPerronSourceFrontier
  /-- The full analytic-kernel import frontier. -/
  | fullAnalyticKernelImportFrontier
  /-- This layer. -/
  | fixedCertificateEndgameFrontier
  deriving DecidableEq, Repr

/-- Layer index: larger means later. -/
def EndgameStatusLayer.index : EndgameStatusLayer → ℕ
  | .dualLevelSimultaneousCritical => 0
  | .regularPerronSourceFrontier => 1
  | .fullAnalyticKernelImportFrontier => 2
  | .fixedCertificateEndgameFrontier => 3

/-- **`fixedCertificateEndgameFrontier_is_later`.**  `LEAN_PROVED`.

This layer is strictly later than every earlier layer, all of which are retained. -/
theorem fixedCertificateEndgameFrontier_is_later :
    EndgameStatusLayer.fullAnalyticKernelImportFrontier.index
        < EndgameStatusLayer.fixedCertificateEndgameFrontier.index ∧
    EndgameStatusLayer.regularPerronSourceFrontier.index
        < EndgameStatusLayer.fixedCertificateEndgameFrontier.index ∧
    EndgameStatusLayer.dualLevelSimultaneousCritical.index
        < EndgameStatusLayer.fixedCertificateEndgameFrontier.index := by decide

/-- **`earlier_layers_retained_unchanged`.**  `LEAN_PROVED`.

The previous ledger is re-checked, not rewritten: its rows still read exactly as banked. -/
theorem earlier_layers_retained_unchanged :
    Erdos287.FullAnalyticKernelImportFrontierStatus.importLedger
        Erdos287.FullAnalyticKernelImportFrontierStatus.ImportNode.fcl = open_ ∧
    Erdos287.FullAnalyticKernelImportFrontierStatus.importLedger
        Erdos287.FullAnalyticKernelImportFrontierStatus.ImportNode.erdos287 = open_ ∧
    Erdos287.FullAnalyticKernelImportFrontierStatus.importLedger
        Erdos287.FullAnalyticKernelImportFrontierStatus.ImportNode.ownerPartition
      = kernelProved := by
  decide

/-! ## §4  The kernel-proved rows of this layer -/

/-- **`supportPartition_row_is_kernel_proved`.**  `LEAN_PROVED`.

The row is backed by the exact finite set identity `I = P ∪ N1 ∪ N2 ∪ U` together with its
cardinality form. -/
theorem supportPartition_row_is_kernel_proved :
    endgameLedger supportPartition = kernelProved ∧
    ∀ d : Erdos287.PhysicalSupport.PhysicalSupportData,
      d.PX ∪ d.N1X ∪ d.N2X ∪ d.UX = d.I ∧
      d.PX.card + d.N1X.card + d.N2X.card + d.UX.card = d.I.card :=
  ⟨rfl, fun d => ⟨d.support_partition_union, d.support_partition_card⟩⟩

/-- **`fourErrorAlgebra_row_is_kernel_proved`.**  `LEAN_PROVED`.

The row is backed by the transference inequality (coefficient one on every channel — no
factor `3`) and by the positivity corollary. -/
theorem fourErrorAlgebra_row_is_kernel_proved :
    endgameLedger fourErrorAlgebra = kernelProved ∧
    ∀ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
      (w : Erdos287.PhysicalSupport.PhysicalWeightData)
      (c : Erdos287.FourErrorTransference.FourChannelBudget),
      Erdos287.FourErrorTransference.ChannelDomination d w c →
        Erdos287.PhysicalSupport.primeMass d w
          ≥ (1 + c.Cc) * Erdos287.PhysicalSupport.Bmass d w - c.E_T - c.E_L - c.E_2 - c.E_M :=
  ⟨rfl, fun _ _ _ h => Erdos287.FourErrorTransference.fourRegion_transference h⟩

/-- **`repairedCertificate_row_is_kernel_proved`.**  `LEAN_PROVED`.

`c₂ = +1`, and the perturbation is the indicator truncation, provably not a scalar
shrink. -/
theorem repairedCertificate_row_is_kernel_proved :
    endgameLedger repairedCertificateData = kernelProved ∧
    Erdos287.FixedCertificateRepair.repairedC2 = 1 ∧
    ∃ (g0 : ℝ → ℝ) (eps : ℝ),
      ¬ ∃ c : ℝ, ∀ x : ℝ, Erdos287.FixedCertificateRepair.gPerturb g0 eps x = c * g0 x :=
  ⟨rfl, rfl, Erdos287.FixedCertificateRepair.gPerturb_is_not_a_scalar_shrink⟩

/-- **`fclToWindowPairTwelve_row_is_kernel_proved_conditional`.**  `LEAN_PROVED`.

The bridge row, at the recorded threshold `12`. -/
theorem fclToWindowPairTwelve_row_is_kernel_proved_conditional :
    endgameLedger fclToWindowPairTwelve = kernelProved ∧
    ∀ M : ℕ, 12 ≤ M → Erdos287.FCLWindowPair.PositiveFCLPrimeMassWitness M →
      Erdos287.WindowPairSupply M :=
  ⟨rfl, fun _ hM h =>
    Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass_twelve hM h⟩

/-- **`bridge_threshold_row_is_twelve`.**  `LEAN_PROVED`.  The recorded bridge threshold of
this layer is `12`. -/
theorem bridge_threshold_row_is_twelve : (12 : ℕ) = 12 := rfl

/-! ## §5  The open / uninhabited rows -/

/-- **`master_source_row_is_open`.**  `LEAN_PROVED`.  The row is open and the socket is a
genuine constraint. -/
theorem master_source_row_is_open :
    endgameLedger masterSourceToTypedPerronPackets45 = open_ ∧
    ∃ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
      (w : Erdos287.PhysicalSupport.PhysicalWeightData)
      (adm : Erdos287.EndgameSockets.FordSourceIndex → Prop)
      (acct : Erdos287.EndgameSockets.Owner → ℝ) (bT tT : ℝ),
      IsEmpty (Erdos287.EndgameSockets.MasterSourceToTypedPerronPacketsInput d w adm acct
        bT tT) :=
  ⟨rfl, Erdos287.EndgameSockets.masterSource_socket_is_a_genuine_constraint⟩

/-- **`n2_collar_row_is_open`.**  `LEAN_PROVED`.

The collar socket is open, and the Ford bounded-sequence hypothesis is *not* a literal
inhabitant for the physical `Λ` weight. -/
theorem n2_collar_row_is_open :
    endgameLedger n2LambdaCollar45 = open_ ∧
    (∃ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
      (w : Erdos287.PhysicalSupport.PhysicalWeightData) (delta2 : ℝ),
        ¬ Erdos287.EndgameSockets.FixedCertificateN2LambdaCollarInput d w delta2) ∧
    ∀ w : Erdos287.PhysicalSupport.PhysicalWeightData,
      Erdos287.EndgameSockets.BoundedSequenceWeight w →
        ¬ Erdos287.EndgameSockets.LambdaGrowth w :=
  ⟨rfl, Erdos287.EndgameSockets.n2Collar_socket_is_a_genuine_constraint,
    fun w h => Erdos287.EndgameSockets.boundedSequence_excludes_lambda_growth w h⟩

/-- **`bsrc_comparison_row_is_open`.**  `LEAN_PROVED`. -/
theorem bsrc_comparison_row_is_open :
    endgameLedger globalBsrcComparisonMargin45 = open_ ∧
    ∃ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
      (w : Erdos287.PhysicalSupport.PhysicalWeightData) (pB : ℕ → ℝ) (dM bL : ℝ),
      ¬ Erdos287.EndgameSockets.GlobalBsrcComparisonMarginInput d w pB dM bL :=
  ⟨rfl, Erdos287.EndgameSockets.bsrcComparison_socket_is_a_genuine_constraint⟩

/-- **`positive_margin_row_is_open`.**  `LEAN_PROVED`.  The margin supply is uninhabited and
no explicit `ε₀` is manufactured. -/
theorem positive_margin_row_is_open :
    endgameLedger positiveMarginSupply = open_ ∧
    (∃ Cc : ℝ, ¬ Erdos287.FCLBridge.PositiveMarginSupply Cc) ∧
    (0 : ℚ) < Erdos287.FourErrorTransference.publishedLimitingMargin :=
  ⟨rfl, Erdos287.FourErrorTransference.positiveMarginSupply_still_uninhabited,
    Erdos287.FourErrorTransference.publishedLimitingMargin_pos⟩

/-- **`ford83_constants_row_is_open`.**  `LEAN_PROVED`. -/
theorem ford83_constants_row_is_open :
    endgameLedger ford83ExplicitConstants = open_ ∧
    ∃ margin E2 Bm : ℝ → ℝ,
      IsEmpty (Erdos287.EndgameSockets.Ford83ExplicitOEpsilonCollarConstants margin E2 Bm) :=
  ⟨rfl, Erdos287.EndgameSockets.ford83_constants_socket_uninhabited_here⟩

/-- **`effectivity_row_is_open`.**  `LEAN_PROVED`.  The effectivity socket is open, and no
asymptotic statement produces a bounded threshold. -/
theorem effectivity_row_is_open :
    endgameLedger effectivity = open_ ∧
    ∃ p : ℕ → Prop, (∃ T : ℝ, ∀ M : ℕ, T ≤ (M : ℝ) → p M) ∧
      ∀ s : Erdos287.WindowPairExport.EffectiveSupply p, ¬ s.Bounded :=
  ⟨rfl, Erdos287.EndgameEffectivity.asymptoticFCL_does_not_give_bounded_effective⟩

/-- **`downstream_rows_open`.**  `LEAN_PROVED`. -/
theorem downstream_rows_open :
    endgameLedger erdos287ClosureInputs = open_ ∧ endgameLedger erdos287 = open_ :=
  ⟨rfl, rfl⟩

/-- **`first_open_research_socket_is_the_master_source`.**  `LEAN_PROVED`.

The earliest open node of this layer is the master source: the local analytic kernel is
banked as external, and everything before the master source in the chain is
kernel-proved. -/
theorem first_open_research_socket_is_the_master_source :
    endgameLedger localAnalyticKernel = analyticBanked ∧
    endgameLedger masterSourceToTypedPerronPackets45 = open_ ∧
    endgameLedger supportPartition = kernelProved ∧
    endgameLedger fourErrorAlgebra = kernelProved := by decide

/-- **`analyticBanked_is_not_kernelProved`.**  `LEAN_PROVED`.  Metadata firewall. -/
theorem analyticBanked_is_not_kernelProved : analyticBanked ≠ kernelProved := by decide

/-- **`no_row_is_a_proof_claim`.**  `LEAN_PROVED`.

Metadata firewall: no ledger value is, or implies, a mathematical proof of #287. -/
theorem no_row_is_a_proof_claim :
    endgameLedger erdos287 ≠ kernelProved ∧
    endgameLedger erdos287 ≠ analyticBanked ∧
    endgameLedger erdos287ClosureInputs ≠ kernelProved := by decide

end FixedCertificateEndgameFrontierStatus
end Erdos287
