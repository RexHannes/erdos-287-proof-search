import RequestProject.Status.CurrentStatusErdos287SimultaneousCritical
import RequestProject.CurrentProgramme.Erdos287K0SP2FourClassPartition
import RequestProject.CurrentProgramme.Erdos287RepeatedBalanced7FiniteArithmetic
import RequestProject.CurrentProgramme.Erdos287RegularTemplateReassembly
import RequestProject.CurrentProgramme.Erdos287Balanced7ScopeAndCauchyFirewall
import RequestProject.CurrentProgramme.Erdos287FCLWindowPairBridge

/-!
# Append-only status layer — the regular-Perron source frontier

This module is **append-only** and sits *later* than
`dualLevelSimultaneousCritical`.  No earlier layer is edited, renamed or deleted;
precedence is recorded by `regularPerronSourceFrontier_is_later`, and the earlier
rows are re-checked, never rewritten.

```
K0-SP2 SOURCE PARTITION                       : kernelProved (finite combinatorics)
UNIFORM-FRAGMENTATION-SOURCECOMPILER45        : kernelProved (source / combinatorial)
REPEATED-BALANCED7 DEPTH-3 ARITHMETIC         : kernelProved
DIRECT BALANCED7 ANALYTIC OWNER               : analyticBanked (paper/external)
287-K0-SP2-REGULAR-PERRON-SMOOTH-MOBIUS-
  CORRELATION45                               : open_        ← FIRST OPEN ANALYTIC NODE
FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45           : open_
FCL                                           : open_
FCL → WINDOWPAIR conditional bridge           : kernelProved (conditional)
EFFECTIVE WINDOWPAIR SUPPLY                   : open_ / uninhabited
Erdos287ClosureInputs                         : open_ / uninhabited
ERDOS287                                      : open_
```

`ResearchStatus` is **metadata**: no value of it carries any implication of
mathematical truth.  The `kernelProved` rows of this layer are exactly the finite
arithmetic / finite combinatorial rows listed in §4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace RegularPerronSourceFrontierStatus

open Erdos287.C0UnitaryFourierStatus
open ResearchStatus

/-! ## §1  Nodes of this layer -/

/-- Nodes of the regular-Perron source-frontier ledger. -/
inductive RegularPerronNode
  /-- The exact four-way K0-SP2 source partition. -/
  | k0SP2SourcePartition
  /-- The uniform fragmentation source compiler (source / combinatorial content). -/
  | uniformFragmentationSourceCompiler45
  /-- The repeated-Balanced7 depth-3 divisor arithmetic and its coefficient table. -/
  | repeatedBalanced7DepthThree
  /-- The direct (distinct) Balanced7 analytic owner — paper/external. -/
  | directBalanced7AnalyticOwner
  /-- The regular Perron parent interface (definition only). -/
  | regularPerronParentInterface
  /-- The finite template reassembly identity. -/
  | templateReassembly
  /-- The exact remaining analytic object. -/
  | regularPerronSmoothMobiusCorrelation45
  /-- The full source-local analytic kernel. -/
  | fullSourceLocalAnalyticKernel45
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

open RegularPerronNode

/-! ## §2  The ledger -/

/-- The authoritative status of each node of this layer. -/
def regularPerronLedger : RegularPerronNode → ResearchStatus
  | k0SP2SourcePartition => kernelProved
  | uniformFragmentationSourceCompiler45 => kernelProved
  | repeatedBalanced7DepthThree => kernelProved
  | directBalanced7AnalyticOwner => analyticBanked
  | regularPerronParentInterface => conditionalSourcePin
  | templateReassembly => kernelProved
  | regularPerronSmoothMobiusCorrelation45 => open_
  | fullSourceLocalAnalyticKernel45 => open_
  | fcl => open_
  | fclToWindowPairBridge => kernelProved
  | effectiveWindowPairSupply => open_
  | erdos287ClosureInputs => open_
  | erdos287 => open_

/-! ## §3  Precedence over the earlier frontier -/

/-- The status layers of this development, in order. -/
inductive StatusLayer
  /-- The earlier dual-level / simultaneous-critical layer. -/
  | dualLevelSimultaneousCritical
  /-- This layer. -/
  | regularPerronSourceFrontier
  deriving DecidableEq, Repr

/-- Layer index: larger means later. -/
def StatusLayer.index : StatusLayer → ℕ
  | .dualLevelSimultaneousCritical => 0
  | .regularPerronSourceFrontier => 1

/-- **`regularPerronSourceFrontier_is_later`.**  `LEAN_PROVED`.

This layer is later than `dualLevelSimultaneousCritical`; the earlier layer is retained,
not deleted, and is superseded only by precedence. -/
theorem regularPerronSourceFrontier_is_later :
    StatusLayer.dualLevelSimultaneousCritical.index
      < StatusLayer.regularPerronSourceFrontier.index := by decide

/-- **`historical_layers_retained`.**  `LEAN_PROVED`.

The earlier ledger is re-checked unchanged: its rows still read exactly as banked. -/
theorem historical_layers_retained :
    Erdos287.SimultaneousCriticalStatus.dualLevelLedger
        Erdos287.SimultaneousCriticalStatus.DualLevelNode.singleCarrier45 = superseded := by
  decide

/-! ## §4  The kernel-proved rows of this layer -/

/-- **`k0SP2_partition_row_is_kernel_proved`.**  `LEAN_PROVED`.

The `k0SP2SourcePartition` row is backed by `k0SP2_fourClass_partition_exact`. -/
theorem k0SP2_partition_row_is_kernel_proved :
    regularPerronLedger k0SP2SourcePartition = kernelProved ∧
    ∀ (P : Erdos287.K0SP2Source.K0SP2Params) (L : ℕ),
      P.classRepeatedB7 ∪ P.classLargePP L ∪ P.classDistinctB7 L ∪ P.classRegular L
        = P.sourceSet :=
  ⟨rfl, fun P L => (Erdos287.K0SP2Source.k0SP2_fourClass_partition_exact P L).2.2.2.2.2.2.1⟩

/-- **`repeatedBalanced7_row_is_kernel_proved`.**  `LEAN_PROVED`.

The depth-3 coefficient row is backed by `depthMoebius_three_eq_neg_choose`. -/
theorem repeatedBalanced7_row_is_kernel_proved :
    regularPerronLedger repeatedBalanced7DepthThree = kernelProved ∧
    ∀ n : ℕ, Squarefree n → 1 ≤ n.primeFactors.card →
      Erdos287.RepeatedBalanced7.depthMoebius n 3
        = -(((n.primeFactors.card - 1).choose 3 : ℕ) : ℤ) :=
  ⟨rfl, fun _ hn hr => Erdos287.RepeatedBalanced7.depthMoebius_three_eq_neg_choose hn hr⟩

/-- **`fclToWindowPair_row_is_kernel_proved_conditional`.**  `LEAN_PROVED`.

The bridge row is backed by `windowPairSupply_of_positiveFCLMass`, which is *conditional*
on the (unconstructed) FCL positivity witness. -/
theorem fclToWindowPair_row_is_kernel_proved_conditional :
    regularPerronLedger fclToWindowPairBridge = kernelProved ∧
    ∀ M : ℕ, 20 ≤ M → Erdos287.FCLWindowPair.PositiveFCLPrimeMassWitness M →
      Erdos287.WindowPairSupply M :=
  ⟨rfl, fun _ hM h => Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass hM h⟩

/-! ## §5  The open rows -/

/-- **`first_open_analytic_node`.**  `LEAN_PROVED`.

The authoritative first open analytic node of this layer is
`287-K0-SP2-REGULAR-PERRON-SMOOTH-MOBIUS-CORRELATION45`. -/
theorem first_open_analytic_node :
    regularPerronLedger regularPerronSmoothMobiusCorrelation45 = open_ ∧
    regularPerronLedger fullSourceLocalAnalyticKernel45 = open_ ∧
    regularPerronLedger fcl = open_ := by
  refine ⟨rfl, rfl, rfl⟩

/-- **`erdos287_row_open`.**  `LEAN_PROVED`.  Erdős #287 is recorded `open_`. -/
theorem erdos287_row_open :
    regularPerronLedger erdos287 = open_ ∧
    regularPerronLedger erdos287ClosureInputs = open_ ∧
    regularPerronLedger effectiveWindowPairSupply = open_ := by
  refine ⟨rfl, rfl, rfl⟩

/-- **`no_row_is_a_proof_claim`.**  `LEAN_PROVED`.

Metadata firewall: no ledger value is, or implies, a mathematical proof of #287. -/
theorem no_row_is_a_proof_claim :
    regularPerronLedger erdos287 ≠ kernelProved := by decide

end RegularPerronSourceFrontierStatus
end Erdos287
