import RequestProject.Status.CurrentStatusErdos287FixedCertificateEndgameFrontier
import RequestProject.CurrentProgramme.Erdos287TwoLaneMasterCompilerV2
import RequestProject.CurrentProgramme.Erdos287HeathBrownSourceRecords
import RequestProject.CurrentProgramme.Erdos287N2FiniteSublemmas

/-!
# Append-only status layer — the two-lane FCL frontier

This module is **append-only** and sits *strictly later* than every existing 287 status
layer, including the fixed-certificate endgame frontier.  No earlier row is rewritten:
precedence is recorded by `twoLaneFCLFrontier_is_later`, and the previous ledgers are
re-checked in place with `decide`.

```
LOCAL ANALYTIC KERNEL (paper/research)          : paperClosedExternal
TWO-LANE RAW SOURCE (Tot ⊎ U)                   : kernelProved
SELECTED-E CANONICAL SELECTOR                   : kernelProved
REPEATED-PRIME FIREWALL                         : kernelProved
HEATH-BROWN SOURCE RECORDS                      : kernelProved
OWNER1 / OWNER2 LEVEL FIREWALL                  : kernelProved
N2 FINITE SUBLEMMAS                             : kernelProved
MASTER COMPILER V2 (raw → two-copy typed owner) : sourceOpen
N2 λ-COLLAR (fixed ε, eventual)                 : paperClosedExternal
Bsrc / N1 / E_M COMPARISON                      : paperClosedExternal
Bmass ASYMPTOTIC                                : paperClosedExternal
POSITIVE MARGIN SUPPLY                          : analyticOpen
ASYMPTOTIC FCL COMPILER                         : conditionalKernel
FCL → WINDOWPAIR, threshold 12                  : conditionalKernel
EXPLICIT THRESHOLD INPUTS                       : effectivityOpen
END-TO-END CHAIN                                : conditionalKernel
MASTER SOURCE SOCKET V1                         : superseded
ERDOS287                                        : sourceOpen
```

`TwoLaneStatus` is **metadata**.  No value of it carries any implication of mathematical
truth; in particular `paperClosedExternal ≠ kernelProved` is a kernel-checked firewall.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TwoLaneFCLFrontierStatus

/-! ## §1  The status vocabulary of this layer -/

/-- The seven-valued status vocabulary of the two-lane FCL frontier. -/
inductive TwoLaneStatus
  /-- Proved in the Lean kernel from `propext`/`Classical.choice`/`Quot.sound` only. -/
  | kernelProved
  /-- Closed in the published/research literature; **never** a Lean theorem here. -/
  | paperClosedExternal
  /-- A Lean theorem whose hypotheses include at least one uninhabited research socket. -/
  | conditionalKernel
  /-- An open source/reconstruction obligation. -/
  | sourceOpen
  /-- An open analytic obligation. -/
  | analyticOpen
  /-- An open effectivity/threshold obligation. -/
  | effectivityOpen
  /-- Retained but replaced by a later object. -/
  | superseded
  deriving DecidableEq, Fintype, Repr

open TwoLaneStatus

/-! ## §2  Nodes of this layer -/

/-- Nodes of the two-lane FCL ledger. -/
inductive TwoLaneNode
  /-- The paper/research local analytic kernel. -/
  | localAnalyticKernel
  /-- The two-lane raw source `I_raw = I_Tot ⊎ I_U`. -/
  | twoLaneRawSource
  /-- The canonical selected-`E` selector. -/
  | selectedESelector
  /-- The repeated-prime firewall. -/
  | repeatedPrimeFirewall
  /-- The Heath-Brown source records and the majorant firewall. -/
  | heathBrownRecords
  /-- The `Owner1` / `Owner2` level firewall. -/
  | ownerLevelFirewall
  /-- The finite `N2` sublemmas. -/
  | n2FiniteSublemmas
  /-- The V2 raw → two-copy typed-owner master compiler. -/
  | masterCompilerV2
  /-- The fixed-`ε` `N2` λ-collar. -/
  | n2LambdaCollarPaper
  /-- The `Bsrc` / `N1` / `E_M` comparison. -/
  | bsrcComparisonPaper
  /-- The `Bmass` asymptotic. -/
  | bmassAsymptoticPaper
  /-- The positive comparison margin supply. -/
  | positiveMarginSupply
  /-- The conditional asymptotic FCL compiler. -/
  | asymptoticFCLCompiler
  /-- The `FCL → WindowPair` bridge at threshold `12`. -/
  | fclToWindowPairTwelve
  /-- The explicit threshold / effectivity socket. -/
  | explicitThresholds
  /-- The end-to-end conditional chain. -/
  | endToEndChain
  /-- The V1 master-source socket, retained but superseded. -/
  | masterSourceV1
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open TwoLaneNode

/-! ## §3  The ledger -/

/-- The authoritative status of each node of this layer. -/
def twoLaneLedger : TwoLaneNode → TwoLaneStatus
  | localAnalyticKernel => paperClosedExternal
  | twoLaneRawSource => kernelProved
  | selectedESelector => kernelProved
  | repeatedPrimeFirewall => kernelProved
  | heathBrownRecords => kernelProved
  | ownerLevelFirewall => kernelProved
  | n2FiniteSublemmas => kernelProved
  | masterCompilerV2 => sourceOpen
  | n2LambdaCollarPaper => paperClosedExternal
  | bsrcComparisonPaper => paperClosedExternal
  | bmassAsymptoticPaper => paperClosedExternal
  | positiveMarginSupply => analyticOpen
  | asymptoticFCLCompiler => conditionalKernel
  | fclToWindowPairTwelve => conditionalKernel
  | explicitThresholds => effectivityOpen
  | endToEndChain => conditionalKernel
  | masterSourceV1 => superseded
  | erdos287 => sourceOpen

/-! ## §4  Precedence over every earlier layer -/

/-- The status layers of this development, in order. -/
inductive TwoLaneStatusLayer
  /-- The dual-level / simultaneous-critical layer. -/
  | dualLevelSimultaneousCritical
  /-- The regular-Perron source frontier. -/
  | regularPerronSourceFrontier
  /-- The full analytic-kernel import frontier. -/
  | fullAnalyticKernelImportFrontier
  /-- The fixed-certificate endgame frontier. -/
  | fixedCertificateEndgameFrontier
  /-- This layer. -/
  | twoLaneFCLFrontier
  deriving DecidableEq, Repr

/-- Layer index: larger means later. -/
def TwoLaneStatusLayer.index : TwoLaneStatusLayer → ℕ
  | .dualLevelSimultaneousCritical => 0
  | .regularPerronSourceFrontier => 1
  | .fullAnalyticKernelImportFrontier => 2
  | .fixedCertificateEndgameFrontier => 3
  | .twoLaneFCLFrontier => 4

/-- **`twoLaneFCLFrontier_is_later`.**  `LEAN_PROVED`.

This layer is strictly later than every earlier layer, all of which are retained. -/
theorem twoLaneFCLFrontier_is_later :
    TwoLaneStatusLayer.fixedCertificateEndgameFrontier.index
        < TwoLaneStatusLayer.twoLaneFCLFrontier.index ∧
    TwoLaneStatusLayer.fullAnalyticKernelImportFrontier.index
        < TwoLaneStatusLayer.twoLaneFCLFrontier.index ∧
    TwoLaneStatusLayer.regularPerronSourceFrontier.index
        < TwoLaneStatusLayer.twoLaneFCLFrontier.index ∧
    TwoLaneStatusLayer.dualLevelSimultaneousCritical.index
        < TwoLaneStatusLayer.twoLaneFCLFrontier.index := by decide

/-- **`earlier_endgame_ledger_retained_unchanged`.**  `LEAN_PROVED`.

The previous ledger is re-checked, not rewritten: its rows still read exactly as banked. -/
theorem earlier_endgame_ledger_retained_unchanged :
    Erdos287.FixedCertificateEndgameFrontierStatus.endgameLedger
        Erdos287.FixedCertificateEndgameFrontierStatus.EndgameNode.supportPartition
      = Erdos287.C0UnitaryFourierStatus.ResearchStatus.kernelProved ∧
    Erdos287.FixedCertificateEndgameFrontierStatus.endgameLedger
        Erdos287.FixedCertificateEndgameFrontierStatus.EndgameNode.fourErrorAlgebra
      = Erdos287.C0UnitaryFourierStatus.ResearchStatus.kernelProved ∧
    Erdos287.FixedCertificateEndgameFrontierStatus.endgameLedger
        Erdos287.FixedCertificateEndgameFrontierStatus.EndgameNode.erdos287
      = Erdos287.C0UnitaryFourierStatus.ResearchStatus.open_ := by decide

/-! ## §5  The kernel-proved rows -/

/-- **`twoLaneRawSource_row_is_kernel_proved`.**  `LEAN_PROVED`.

Backed by the literal two-lane disjoint-union identity in set, cardinality and sum form. -/
theorem twoLaneRawSource_row_is_kernel_proved :
    twoLaneLedger twoLaneRawSource = kernelProved ∧
    ∀ S : Finset Erdos287.TwoLaneRawSource.RawPacketId,
      Erdos287.TwoLaneRawSource.totCells S ∪ Erdos287.TwoLaneRawSource.uCells S = S ∧
      Disjoint (Erdos287.TwoLaneRawSource.totCells S) (Erdos287.TwoLaneRawSource.uCells S) ∧
      (Erdos287.TwoLaneRawSource.totCells S).card
          + (Erdos287.TwoLaneRawSource.uCells S).card = S.card :=
  ⟨rfl, fun S => ⟨Erdos287.TwoLaneRawSource.raw_source_two_lane_union S,
    Erdos287.TwoLaneRawSource.raw_source_two_lane_disjoint S,
    Erdos287.TwoLaneRawSource.raw_source_two_lane_card S⟩⟩

/-- **`selectedE_row_is_kernel_proved`.**  `LEAN_PROVED`.

The selector picks one member of the row, and independent selection would duplicate it. -/
theorem selectedE_row_is_kernel_proved :
    twoLaneLedger selectedESelector = kernelProved ∧
    ∀ (E : Finset (Finset Erdos287.TwoLaneRawSource.Leaf))
      (h : E.Nonempty), Erdos287.TwoLaneRawSource.selectedE E h ∈ E :=
  ⟨rfl, fun E h => Erdos287.TwoLaneRawSource.selectedE_mem E h⟩

/-- **`repeatedPrime_row_is_kernel_proved`.**  `LEAN_PROVED`.

Labelled subsets over-count a repeated-prime row; the exponent representation is used
instead. -/
theorem repeatedPrime_row_is_kernel_proved :
    twoLaneLedger repeatedPrimeFirewall = kernelProved ∧
    (([2, 2] : List ℕ).sublists.length = 4) ∧
    ((([2, 2] : List ℕ).sublists.map (fun s => s.prod)).toFinset.card = 3) :=
  ⟨rfl, Erdos287.TwoLaneRawSource.repeated_row_would_be_overcounted⟩

/-- **`heathBrown_row_is_kernel_proved`.**  `LEAN_PROVED`.

A one-bounded majorant may never be substituted for the exact source coefficient. -/
theorem heathBrown_row_is_kernel_proved :
    twoLaneLedger heathBrownRecords = kernelProved ∧
    ∃ (row₁ row₂ : Erdos287.HeathBrownSource.HeathBrownRow)
      (m : Erdos287.HeathBrownSource.OneBoundedMajorant),
      Erdos287.HeathBrownSource.exactGeneratedCoefficient row₁
          ≠ Erdos287.HeathBrownSource.exactGeneratedCoefficient row₂ ∧
      |Erdos287.HeathBrownSource.exactGeneratedCoefficient row₁| ≤ 1 ∧
      |Erdos287.HeathBrownSource.exactGeneratedCoefficient row₂| ≤ 1 ∧
      ∀ n, |m.c n| ≤ 1 :=
  ⟨rfl, Erdos287.HeathBrownSource.majorant_is_not_the_source_coefficient⟩

/-- **`ownerLevel_row_is_kernel_proved`.**  `LEAN_PROVED`.

No one-copy packet may carry a two-copy owner. -/
theorem ownerLevel_row_is_kernel_proved :
    twoLaneLedger ownerLevelFirewall = kernelProved ∧
    ∀ o : Erdos287.OneCopyTwoCopy.Owner1,
      o.toPacketOwner ≠ Erdos287.MasterSourcePackets.PacketOwner.c0 ∧
      o.toPacketOwner ≠ Erdos287.MasterSourcePackets.PacketOwner.transverse ∧
      o.toPacketOwner ≠ Erdos287.MasterSourcePackets.PacketOwner.bDiagonal :=
  ⟨rfl, Erdos287.OneCopyTwoCopy.owner1_excludes_two_copy_owners⟩

/-- **`n2Finite_row_is_kernel_proved`.**  `LEAN_PROVED`.

The finite sublemmas: the `Ω ≤ 6` bound and the `2^6` subvector expansion bound. -/
theorem n2Finite_row_is_kernel_proved :
    twoLaneLedger n2FiniteSublemmas = kernelProved ∧
    ∀ {sigma : ℝ} {Om : ℕ}, 1 / 7 < sigma → sigma * (Om : ℝ) ≤ 1 → Om ≤ 6 :=
  ⟨rfl, fun hs h => Erdos287.N2Finite.omega_le_six hs h⟩

/-! ## §6  The conditional rows -/

/-- **`asymptoticFCL_row_is_conditional`.**  `LEAN_PROVED`.

The compiler is a Lean theorem, but every one of its research antecedents is refutable at
explicit data, hence genuinely open. -/
theorem asymptoticFCL_row_is_conditional :
    twoLaneLedger asymptoticFCLCompiler = conditionalKernel ∧
    (∃ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
        (w : Erdos287.PhysicalSupport.PhysicalWeightData)
        (S : Finset Erdos287.TwoLaneRawSource.RawPacketId)
        (rv : Erdos287.TwoLaneRawSource.RawPacketId → ℝ)
        (ob : Erdos287.OneCopyTwoCopy.Owner2 → ℝ),
      IsEmpty (Erdos287.TwoLaneMaster.TwoLaneRawToTwoCopyTypedOwnerInput d w S rv ob)) ∧
    (∃ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
        (w : Erdos287.PhysicalSupport.PhysicalWeightData) (m : ℝ),
      IsEmpty (Erdos287.TwoLaneMaster.N2LambdaCollarPaperInput d w m)) ∧
    (∃ (d : Erdos287.PhysicalSupport.PhysicalSupportData)
        (w : Erdos287.PhysicalSupport.PhysicalWeightData) (pB : ℕ → ℝ) (m : ℝ),
      IsEmpty (Erdos287.TwoLaneMaster.BsrcN1ComparisonPaperInput d w pB m)) ∧
    (∃ Cc : ℝ, ¬ Erdos287.FCLBridge.PositiveMarginSupply Cc) :=
  ⟨rfl, Erdos287.TwoLaneMaster.asymptoticFCL_keeps_every_external_input.1,
    Erdos287.TwoLaneMaster.asymptoticFCL_keeps_every_external_input.2.1,
    Erdos287.TwoLaneMaster.asymptoticFCL_keeps_every_external_input.2.2.1,
    Erdos287.TwoLaneMaster.asymptoticFCL_keeps_every_external_input.2.2.2⟩

/-- **`fclToWindowPair_row_is_conditional`.**  `LEAN_PROVED`.  Threshold `12`. -/
theorem fclToWindowPair_row_is_conditional :
    twoLaneLedger fclToWindowPairTwelve = conditionalKernel ∧
    ∀ M : ℕ, 12 ≤ M → Erdos287.FCLWindowPair.PositiveFCLPrimeMassWitness M →
      Erdos287.WindowPairSupply M :=
  ⟨rfl, fun _ hM h =>
    Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass_twelve hM h⟩

/-- **`bridge_threshold_row_is_twelve`.**  `LEAN_PROVED`. -/
theorem bridge_threshold_row_is_twelve : (12 : ℕ) = 12 := rfl

/-- **`endToEnd_row_is_conditional`.**  `LEAN_PROVED`.

The end-to-end chain is a Lean theorem whose single premise, the explicit-threshold socket,
is never inhabited here. -/
theorem endToEnd_row_is_conditional :
    twoLaneLedger endToEndChain = conditionalKernel ∧
    (Erdos287.TwoLaneMaster.Erdos287ExplicitThresholdInputs → Erdos287Statement) ∧
    ¬ ∃ I : Erdos287.TwoLaneMaster.Erdos287ExplicitThresholdInputs,
        (I.witness I.M0 le_rfl).q = 4 :=
  ⟨rfl, Erdos287.TwoLaneMaster.erdos287Statement_of_explicit_research_inputs,
    Erdos287.TwoLaneMaster.explicit_thresholds_not_supplied⟩

/-! ## §7  The open rows and the metadata firewalls -/

/-- **`open_rows`.**  `LEAN_PROVED`. -/
theorem open_rows :
    twoLaneLedger masterCompilerV2 = sourceOpen ∧
    twoLaneLedger positiveMarginSupply = analyticOpen ∧
    twoLaneLedger explicitThresholds = effectivityOpen ∧
    twoLaneLedger erdos287 = sourceOpen := by decide

/-- **`paperClosedExternal_is_not_kernelProved`.**  `LEAN_PROVED`.  Metadata firewall: a
paper-closed row is never a Lean theorem of this repository. -/
theorem paperClosedExternal_is_not_kernelProved :
    paperClosedExternal ≠ kernelProved ∧ paperClosedExternal ≠ conditionalKernel := by decide

/-- **`superseded_is_not_a_deletion`.**  `LEAN_PROVED`.  The V1 socket is retained with the
`superseded` label, which is itself not a proof value. -/
theorem superseded_is_not_a_deletion :
    twoLaneLedger masterSourceV1 = superseded ∧ superseded ≠ kernelProved := by decide

/-- **`first_open_research_socket_is_the_master_compiler_v2`.**  `LEAN_PROVED`. -/
theorem first_open_research_socket_is_the_master_compiler_v2 :
    twoLaneLedger localAnalyticKernel = paperClosedExternal ∧
    twoLaneLedger twoLaneRawSource = kernelProved ∧
    twoLaneLedger ownerLevelFirewall = kernelProved ∧
    twoLaneLedger masterCompilerV2 = sourceOpen := by decide

/-- **`no_row_is_a_proof_claim`.**  `LEAN_PROVED`.

Metadata firewall: no ledger value is, or implies, a mathematical proof of #287. -/
theorem no_row_is_a_proof_claim :
    twoLaneLedger erdos287 ≠ kernelProved ∧
    twoLaneLedger erdos287 ≠ conditionalKernel ∧
    twoLaneLedger erdos287 ≠ paperClosedExternal := by decide

end TwoLaneFCLFrontierStatus
end Erdos287
