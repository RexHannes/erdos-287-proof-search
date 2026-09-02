import RequestProject.Status.CurrentStatusErdos287RegularPerronSourceFrontier
import RequestProject.CurrentProgramme.Erdos287FullSourceAnalyticKernelInput
import RequestProject.CurrentProgramme.Erdos287MasterSourceTypedPerronPackets
import RequestProject.CurrentProgramme.Erdos287OneBoundedSourceFactor
import RequestProject.CurrentProgramme.Erdos287DeterminantOneCompiler
import RequestProject.CurrentProgramme.Erdos287TwoCopyRouterAndOmega
import RequestProject.CurrentProgramme.Erdos287FullAnalyticKernelFCLChannels

/-!
# Append-only status layer — the full analytic-kernel import frontier

This module is **append-only** and sits *strictly later* than
`regularPerronSourceFrontier`, which is retained unchanged; precedence is
recorded by `fullAnalyticKernelImportFrontier_is_later`, and the earlier rows
are re-checked, never rewritten.

```
K0-SP2 SOURCE PARTITION                        : kernelProved (finite combinatorics)
UNIFORM FRAGMENTATION SOURCE COMPILER          : kernelProved (source / combinatorial)
MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45        : kernelProved (source / formal compiler)
OWNER PARTITION (6 owners)                     : kernelProved
DE-REGULARISATION IDENTITY                     : kernelProved
ONE-BOUNDED SOURCE FACTOR (algebraic part)     : kernelProved
DETERMINANT-ONE COMPILER                       : kernelProved (finite arithmetic)
TWO-COPY ROUTER                                : kernelProved
PROOF-LOCAL SHARED-GCD Ω PARTITION             : kernelProved
REGULAR PERRON ANALYTIC ESTIMATE               : analyticBanked / externalPaperInput
FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45            : analyticBanked / externalPaperInput
PHYSICAL FIXED-CERTIFICATE SOURCE PIN          : conditionalSourcePin (OPEN, uninhabited)
FCL ERROR CHANNELS (combination identity)      : kernelProved
FCL                                            : open_        ← FIRST OPEN NODE
FCL → WINDOWPAIR conditional bridge            : kernelProved (conditional)
EFFECTIVE WINDOWPAIR SUPPLY                    : open_ / uninhabited
Erdos287ClosureInputs                          : open_ / uninhabited
ERDOS287                                       : open_
```

`ResearchStatus` is **metadata**: no value of it carries any implication of
mathematical truth.  In particular `analyticBanked` records a paper/research
report, **not** a Lean theorem: the corresponding typed structure
`FullSourceLocalAnalyticKernelInput` is left uninhabited, and every downstream
theorem carries it as an explicit hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FullAnalyticKernelImportFrontierStatus

open Erdos287.C0UnitaryFourierStatus
open ResearchStatus

/-! ## §1  Nodes of this layer -/

/-- Nodes of the full analytic-kernel import ledger. -/
inductive ImportNode
  /-- The exact four-way K0-SP2 source partition. -/
  | k0SP2SourcePartition
  /-- The uniform fragmentation source compiler. -/
  | uniformFragmentationSourceCompiler
  /-- The master-source → typed-Perron-packets source/formal compiler. -/
  | masterSourceToTypedPerronPackets45
  /-- The six-owner partition of the typed packets. -/
  | ownerPartition
  /-- The exact de-regularisation identity. -/
  | deRegularisationIdentity
  /-- The algebraic part of the one-bounded source factorisation. -/
  | oneBoundedSourceFactor
  /-- The determinant-one source compiler. -/
  | determinantOneCompiler
  /-- The two-copy router. -/
  | twoCopyRouter
  /-- The proof-local shared-gcd `Ω` partition. -/
  | proofLocalOmega
  /-- The regular Perron analytic estimate (paper/external). -/
  | regularPerronAnalyticEstimate
  /-- The full source-local analytic kernel (paper/external). -/
  | fullSourceLocalAnalyticKernel45
  /-- The literal physical fixed-certificate source pin. -/
  | physicalFixedCertificateSourcePin
  /-- The four FCL error channels: combination identity only. -/
  | fclErrorChannels
  /-- The FCL positivity input. -/
  | fcl
  /-- The conditional FCL → WindowPair bridge. -/
  | fclToWindowPairBridge
  /-- The effective window-pair supply. -/
  | effectiveWindowPairSupply
  /-- The end-to-end closure inputs. -/
  | erdos287ClosureInputs
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open ImportNode

/-! ## §2  The ledger -/

/-- The authoritative status of each node of this layer. -/
def importLedger : ImportNode → ResearchStatus
  | k0SP2SourcePartition => kernelProved
  | uniformFragmentationSourceCompiler => kernelProved
  | masterSourceToTypedPerronPackets45 => kernelProved
  | ownerPartition => kernelProved
  | deRegularisationIdentity => kernelProved
  | oneBoundedSourceFactor => kernelProved
  | determinantOneCompiler => kernelProved
  | twoCopyRouter => kernelProved
  | proofLocalOmega => kernelProved
  | regularPerronAnalyticEstimate => analyticBanked
  | fullSourceLocalAnalyticKernel45 => analyticBanked
  | physicalFixedCertificateSourcePin => conditionalSourcePin
  | fclErrorChannels => kernelProved
  | fcl => open_
  | fclToWindowPairBridge => kernelProved
  | effectiveWindowPairSupply => open_
  | erdos287ClosureInputs => open_
  | erdos287 => open_

/-! ## §3  Precedence over the earlier frontier -/

/-- The status layers of this development, in order. -/
inductive StatusLayer
  /-- The dual-level / simultaneous-critical layer. -/
  | dualLevelSimultaneousCritical
  /-- The regular-Perron source frontier. -/
  | regularPerronSourceFrontier
  /-- This layer. -/
  | fullAnalyticKernelImportFrontier
  deriving DecidableEq, Repr

/-- Layer index: larger means later. -/
def StatusLayer.index : StatusLayer → ℕ
  | .dualLevelSimultaneousCritical => 0
  | .regularPerronSourceFrontier => 1
  | .fullAnalyticKernelImportFrontier => 2

/-- **`fullAnalyticKernelImportFrontier_is_later`.**  `LEAN_PROVED`.

This layer is strictly later than both earlier layers, which are retained. -/
theorem fullAnalyticKernelImportFrontier_is_later :
    StatusLayer.regularPerronSourceFrontier.index
        < StatusLayer.fullAnalyticKernelImportFrontier.index ∧
    StatusLayer.dualLevelSimultaneousCritical.index
        < StatusLayer.fullAnalyticKernelImportFrontier.index := by decide

/-- **`earlier_layer_retained_unchanged`.**  `LEAN_PROVED`.

The regular-Perron ledger is re-checked, not rewritten: its rows still read exactly as
banked. -/
theorem earlier_layer_retained_unchanged :
    Erdos287.RegularPerronSourceFrontierStatus.regularPerronLedger
        Erdos287.RegularPerronSourceFrontierStatus.RegularPerronNode.k0SP2SourcePartition
      = kernelProved ∧
    Erdos287.RegularPerronSourceFrontierStatus.regularPerronLedger
        Erdos287.RegularPerronSourceFrontierStatus.RegularPerronNode.erdos287 = open_ := by
  decide

/-! ## §4  The kernel-proved rows of this layer -/

/-- **`masterSource_compiler_row_is_kernel_proved`.**  `LEAN_PROVED`.

The compiler row is backed by the linearity of the dependency chain and by the exact
de-regularisation identity. -/
theorem masterSource_compiler_row_is_kernel_proved :
    importLedger masterSourceToTypedPerronPackets45 = kernelProved ∧
    (∀ s t : Erdos287.MasterSourcePackets.CompilerStage,
      s.next = some t → s.index + 1 = t.index) :=
  ⟨rfl, Erdos287.MasterSourcePackets.chain_is_linear⟩

/-- **`deRegularisation_row_is_kernel_proved`.**  `LEAN_PROVED`. -/
theorem deRegularisation_row_is_kernel_proved :
    importLedger deRegularisationIdentity = kernelProved ∧
    ∀ (P : Erdos287.K0SP2Source.K0SP2Params) (W : ℕ → ℂ) (D : Bool → ℕ → ℂ) (L : ℕ),
      Erdos287.K0SP2Source.sectorExpr P W D (P.classRegular L)
        = Erdos287.K0SP2Source.sourceExpr P W D
          - Erdos287.K0SP2Source.sectorExpr P W D P.classRepeatedB7
          - Erdos287.K0SP2Source.sectorExpr P W D (P.classLargePP L)
          - Erdos287.K0SP2Source.sectorExpr P W D (P.classDistinctB7 L) :=
  ⟨rfl, fun P W D L =>
    Erdos287.MasterSourcePackets.K0SP2Params.deRegularisation_identity P W D L⟩

/-- **`owner_partition_row_is_kernel_proved`.**  `LEAN_PROVED`.

The owner row is backed by: exactly six owners, one owner per packet, no packet with two
owners, and exact owner-wise reassembly. -/
theorem owner_partition_row_is_kernel_proved :
    importLedger ownerPartition = kernelProved ∧
    Fintype.card Erdos287.MasterSourcePackets.PacketOwner = 6 ∧
    ∀ {ι : Type} [DecidableEq ι] (F : Erdos287.MasterSourcePackets.PacketFamily ι)
      (val : ι → ℂ),
      ∑ o : Erdos287.MasterSourcePackets.PacketOwner, ∑ i ∈ F.fibre o, val i
        = ∑ i ∈ F.cells, val i :=
  ⟨rfl, Erdos287.MasterSourcePackets.owner_type_is_exactly_six,
    fun F val => F.owner_accounts_reassemble val⟩

/-- **`det1_row_is_kernel_proved`.**  `LEAN_PROVED`. -/
theorem det1_row_is_kernel_proved :
    importLedger determinantOneCompiler = kernelProved ∧
    ∀ r a b₀ q₀ s t : ℤ, r * q₀ - 2 * a * b₀ = s →
      r * (q₀ + 2 * a * t) - 2 * a * (b₀ + r * t) = s :=
  ⟨rfl, fun r a b₀ q₀ s t h => Erdos287.DeterminantOne.det1_shift r a b₀ q₀ s t h⟩

/-- **`router_row_is_kernel_proved`.**  `LEAN_PROVED`. -/
theorem router_row_is_kernel_proved :
    importLedger twoCopyRouter = kernelProved ∧
    ∀ c : Erdos287.TwoCopyRouter.TwoCopyConfig,
      Erdos287.TwoCopyRouter.route c = Erdos287.TwoCopyRouter.RouterTag.c0 ∨
      Erdos287.TwoCopyRouter.route c = Erdos287.TwoCopyRouter.RouterTag.transverse ∨
      Erdos287.TwoCopyRouter.route c = Erdos287.TwoCopyRouter.RouterTag.bDiagonal :=
  ⟨rfl, Erdos287.TwoCopyRouter.router_exhaustive⟩

/-- **`omega_row_is_kernel_proved`.**  `LEAN_PROVED`. -/
theorem omega_row_is_kernel_proved :
    importLedger proofLocalOmega = kernelProved ∧
    ∀ (K : ℕ) (c : Erdos287.TwoCopyRouter.TwoCopyConfig),
      Erdos287.TwoCopyRouter.gcdClass (Nat.gcd c.g₁ c.g₂) ≤ K →
      ∑ H ∈ Finset.range (K + 1), Erdos287.TwoCopyRouter.omegaOfConfig H c = 1 :=
  ⟨rfl, fun K c h => Erdos287.TwoCopyRouter.omega_partition_two_copy K c h⟩

/-- **`oneBounded_row_is_kernel_proved`.**  `LEAN_PROVED`. -/
theorem oneBounded_row_is_kernel_proved :
    importLedger oneBoundedSourceFactor = kernelProved ∧
    ∀ (d : Erdos287.OneBoundedFactor.SourceFactorData) (a b : ℕ),
      ‖d.Afactor a‖ ≤ 1 ∧ ‖d.Bfactor b‖ ≤ 1 :=
  ⟨rfl, fun d a b => ⟨d.norm_Afactor_le_one a, d.norm_Bfactor_le_one b⟩⟩

/-- **`fclChannels_row_is_kernel_proved`.**  `LEAN_PROVED`.

Only the exact combination identity is banked for the four channels. -/
theorem fclChannels_row_is_kernel_proved :
    importLedger fclErrorChannels = kernelProved ∧
    ∀ ch : Erdos287.FullAnalyticKernelFCL.FCLErrorChannels,
      ch.total = ch.E_T + ch.E_L + ch.E_2 + ch.E_M :=
  ⟨rfl, fun ch => ch.total_identity⟩

/-- **`fclToWindowPair_row_is_kernel_proved_conditional`.**  `LEAN_PROVED`.

Reused verbatim from `windowPairSupply_of_positiveFCLMass`; the row is *conditional* on
the unconstructed FCL positivity witness. -/
theorem fclToWindowPair_row_is_kernel_proved_conditional :
    importLedger fclToWindowPairBridge = kernelProved ∧
    ∀ M : ℕ, 20 ≤ M → Erdos287.FCLWindowPair.PositiveFCLPrimeMassWitness M →
      Erdos287.WindowPairSupply M :=
  ⟨rfl, fun _ hM h => Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass hM h⟩

/-! ## §5  The banked-analytic and open rows -/

/-- **`analytic_rows_are_external`.**  `LEAN_PROVED`.

The two analytic rows are `analyticBanked`, i.e. paper/external.  The corresponding typed
input is **not** inhabited: it is refutable at explicit data, so no Lean theorem of this
repository supplies it. -/
theorem analytic_rows_are_external :
    importLedger regularPerronAnalyticEstimate = analyticBanked ∧
    importLedger fullSourceLocalAnalyticKernel45 = analyticBanked ∧
    ∃ (X : ℝ) (v : Erdos287.FullAnalyticKernel.OwnerValues),
      ¬ Erdos287.FullAnalyticKernel.FullSourceLocalAnalyticKernelInput X v :=
  ⟨rfl, rfl, Erdos287.FullAnalyticKernel.analyticInput_is_a_genuine_constraint⟩

/-- **`analyticBanked_is_not_kernelProved`.**  `LEAN_PROVED`.

Metadata firewall: `analyticBanked` is a different value from `kernelProved`; banking a
paper result never upgrades a row to a Lean theorem. -/
theorem analyticBanked_is_not_kernelProved : analyticBanked ≠ kernelProved := by decide

/-- **`source_pin_row_is_open`.**  `LEAN_PROVED`.

The literal physical certificate source pin is open and uninhabited. -/
theorem source_pin_row_is_open :
    importLedger physicalFixedCertificateSourcePin = conditionalSourcePin ∧
    ∃ s : Erdos287.FullAnalyticKernelFCL.PhysicalCertificateSource,
      ¬ Erdos287.FullAnalyticKernelFCL.PhysicalSourcePinned s :=
  ⟨rfl, Erdos287.FullAnalyticKernelFCL.physicalSourcePin_not_automatic⟩

/-- **`first_open_node_is_the_literal_fcl_source_input`.**  `LEAN_PROVED`.

The earliest open node of this layer is the literal FCL / source / effectivity input —
**not** the regular-Perron analytics, which are banked as external. -/
theorem first_open_node_is_the_literal_fcl_source_input :
    importLedger fcl = open_ ∧
    importLedger physicalFixedCertificateSourcePin ≠ kernelProved ∧
    importLedger regularPerronAnalyticEstimate ≠ open_ := by
  refine ⟨rfl, by decide, by decide⟩

/-- **`downstream_rows_open`.**  `LEAN_PROVED`. -/
theorem downstream_rows_open :
    importLedger effectiveWindowPairSupply = open_ ∧
    importLedger erdos287ClosureInputs = open_ ∧
    importLedger erdos287 = open_ := by
  refine ⟨rfl, rfl, rfl⟩

/-- **`no_row_is_a_proof_claim`.**  `LEAN_PROVED`.

Metadata firewall: no ledger value is, or implies, a mathematical proof of #287. -/
theorem no_row_is_a_proof_claim :
    importLedger erdos287 ≠ kernelProved ∧
    importLedger erdos287 ≠ analyticBanked := by decide

end FullAnalyticKernelImportFrontierStatus
end Erdos287
