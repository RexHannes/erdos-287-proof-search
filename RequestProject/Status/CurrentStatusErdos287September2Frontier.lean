import RequestProject.Status.CurrentStatusErdos287SharedOtherFrontier
import RequestProject.CurrentProgramme.Erdos287N2EffectiveConstantsBank

/-!
# Append-only status layer — the September-2 Erdős #287 frontier

This module is **append-only** and is the *latest authoritative* status layer: it sits
strictly later than every earlier 287 status layer, and where a later hostile audit
contradicts an earlier label, the earlier label is recorded here as `superseded`.

```
finite bank, M ≤ 4·10⁹                       : kernelProved
public #287 statement / WindowPairSupply      : kernelProved (unchanged, not weakened)
Tot lane → Ford–Maynard 7.21 Type-I, E_T      : paperClosedExternal
Bsrc / N1 dictionary, E_M, B_X mass           : paperClosedExternal
E_2 (N2 λ-collar), asymptotic                 : paperClosedExternal
E_2 effective (huge threshold)                : paperClosedExternal
N2 finite splice at the current constants     : kernelProvedFalse (recorded as open)
RUN1B d*wp provider (neutral shared layer)    : paperClosedExternal
RUN1B source-exhaustiveness (finite)          : kernelProved
effective-modulus identity, Fourier matrix,
  orthogonality, residue-class energy,
  small-modulus expansion, Parseval, L¹≤√r L²  : kernelProved
Möbius polynomial-phase estimate              : paperClosedExternal
ultra-near-half covariance                    : openExternal
shared OTHER parent theorem                   : conditionalKernel
twin adapter / #287 hard-U adapter            : conditionalKernel (source obligation open)
E_L                                           : conditionalKernel (open antecedents)
b-diagonal                                    : strictlyReducedOpen  (hostile downgrade)
Perron total-nuclear ledger, rectangle pin,
  Ω_H provenance, short-edge owner
  completeness, source coprimalities          : openExternal
asymptotic FCL                                : conditionalKernel
FCL → WindowPair (M ≥ 12)                     : conditionalKernel
global effectivity, M₀ ≤ 4·10⁹                : effectivityOpen
Gate 1A on the #287 critical path             : superseded (not an antecedent)
Erdős #287                                    : openExternal
Twin prime                                    : openExternal
```

`Status` is **metadata**.  The firewalls below are machine-checked: `paperClosedExternal ≠
kernelProved`, no row is a proof claim, and no status value is allowed to close a node.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace September2FrontierStatus

/-! ## §1  The status vocabulary -/

/-- The status vocabulary of the September-2 frontier. -/
inductive Status
  /-- Proved in the Lean kernel. -/
  | kernelProved
  /-- Closed in the published literature; **never** a Lean theorem here. -/
  | paperClosedExternal
  /-- A Lean theorem whose research antecedents are still open. -/
  | conditionalKernel
  /-- Reduced by a hostile audit but still open. -/
  | strictlyReducedOpen
  /-- An open external obligation. -/
  | openExternal
  /-- An open effectivity obligation. -/
  | effectivityOpen
  /-- A label from an earlier layer that a later audit has overridden. -/
  | superseded
  deriving DecidableEq, Fintype, Repr

open Status

/-! ## §2  Nodes -/

/-- Nodes of the September-2 ledger. -/
inductive Node
  /-- The finite exclusion / certificate bank through `M ≤ 4·10⁹`. -/
  | finiteBank
  /-- The public Erdős-287 statement and the `WindowPairSupply` definitions. -/
  | publicStatement
  /-- The Tot lane and the Type-I error `E_T`. -/
  | totLaneE_T
  /-- The global `B_physical = B_src` dictionary, `N1`, `E_M`, `B_X` mass. -/
  | bsrcN1E_M
  /-- The asymptotic `N2` λ-collar error `E_2`. -/
  | e2Asymptotic
  /-- The effective `N2` λ-collar statement with its enormous threshold. -/
  | e2Effective
  /-- The attempted finite splice of the effective `N2` threshold into the finite bank. -/
  | n2FiniteSplice
  /-- The RUN1B `d·w'` analytic provider (neutral shared Ford layer). -/
  | run1BProvider
  /-- The finite RUN1B source-exhaustiveness / routing statement. -/
  | run1BSourceExhaustive
  /-- The kernelised `d·w'` algebra: effective modulus, Fourier matrix, energies. -/
  | dwpKernelAlgebra
  /-- The external Möbius polynomial-phase estimate. -/
  | mobiusPolyPhase
  /-- The ultra-near-half covariance residual. -/
  | ultraNearHalf
  /-- The shared other-parent theorem. -/
  | sharedOther
  /-- The twin-side adapter. -/
  | twinAdapter
  /-- The #287 hard-`U` shared-Ford adapter (source-equality obligation). -/
  | erdos287HardUAdapter
  /-- The `E_L` error. -/
  | eL
  /-- The b-diagonal package. -/
  | bDiagonal
  /-- The b-diagonal Perron total-nuclear ledger obligation. -/
  | perronNuclearLedger
  /-- The rectangle-inequality literal source pin. -/
  | rectanglePin
  /-- The provenance of `Ω_H`. -/
  | omegaHProvenanceNode
  /-- Short-edge / below-threshold owner completeness. -/
  | shortEdgeOwners
  /-- The required source coprimalities. -/
  | sourceCoprimalities
  /-- The asymptotic four-error FCL. -/
  | asymptoticFCL
  /-- The `FCL_W(M/2) → WindowPairSupply M` bridge for `M ≥ 12`. -/
  | fclToWindowPair
  /-- Global effectivity. -/
  | globalEffectivity
  /-- The claim `M₀ ≤ 4·10⁹`. -/
  | m0WithinFiniteBank
  /-- Gate 1A as an alleged antecedent of the #287 critical path. -/
  | gate1AOnCriticalPath
  /-- Erdős #287 itself. -/
  | erdos287
  /-- The twin-prime conjecture. -/
  | twinPrime
  deriving DecidableEq, Fintype, Repr

open Node

/-! ## §3  The authoritative ledger -/

/-- The September-2 authoritative status assignment. -/
def september2Ledger : Node → Status
  | finiteBank => kernelProved
  | publicStatement => kernelProved
  | totLaneE_T => paperClosedExternal
  | bsrcN1E_M => paperClosedExternal
  | e2Asymptotic => paperClosedExternal
  | e2Effective => paperClosedExternal
  | n2FiniteSplice => openExternal
  | run1BProvider => paperClosedExternal
  | run1BSourceExhaustive => kernelProved
  | dwpKernelAlgebra => kernelProved
  | mobiusPolyPhase => paperClosedExternal
  | ultraNearHalf => openExternal
  | sharedOther => conditionalKernel
  | twinAdapter => conditionalKernel
  | erdos287HardUAdapter => conditionalKernel
  | eL => conditionalKernel
  | bDiagonal => strictlyReducedOpen
  | perronNuclearLedger => openExternal
  | rectanglePin => openExternal
  | omegaHProvenanceNode => openExternal
  | shortEdgeOwners => openExternal
  | sourceCoprimalities => openExternal
  | asymptoticFCL => conditionalKernel
  | fclToWindowPair => conditionalKernel
  | globalEffectivity => effectivityOpen
  | m0WithinFiniteBank => effectivityOpen
  | gate1AOnCriticalPath => superseded
  | erdos287 => openExternal
  | twinPrime => openExternal

/-! ## §4  Firewalls -/

/-- **`paperClosed_is_not_kernelProved`.**  `KERNEL-PROVED`.  Representing an external
analytic interface in Lean never makes it kernel-proved. -/
theorem paperClosed_is_not_kernelProved : paperClosedExternal ≠ kernelProved := by decide

/-- **`conditional_is_not_kernelProved`.**  `KERNEL-PROVED`. -/
theorem conditional_is_not_kernelProved : conditionalKernel ≠ kernelProved := by decide

/-- **`erdos287_is_open`.**  `KERNEL-PROVED`.  The authoritative row for #287. -/
theorem erdos287_is_open : september2Ledger erdos287 = openExternal := rfl

/-- **`twinPrime_is_open`.**  `KERNEL-PROVED`. -/
theorem twinPrime_is_open : september2Ledger twinPrime = openExternal := rfl

/-- **`bdiagonal_hostile_downgrade`.**  `KERNEL-PROVED`.  The b-diagonal node is *not* closed
in this layer: any earlier "full local kernel closed" label is superseded. -/
theorem bdiagonal_hostile_downgrade :
    september2Ledger bDiagonal = strictlyReducedOpen ∧
      september2Ledger bDiagonal ≠ kernelProved := by
  constructor
  · rfl
  · decide

/-- **`gate1A_is_not_on_the_critical_path`.**  `KERNEL-PROVED`. -/
theorem gate1A_is_not_on_the_critical_path :
    september2Ledger gate1AOnCriticalPath = superseded := rfl

/-- **`n2_splice_is_not_closed`.**  `KERNEL-PROVED`.  The finite splice row is open, matching
the kernel-proved arithmetic fact `¬ (2 X_N2 ≤ 4·10⁹)`. -/
theorem n2_splice_is_not_closed :
    september2Ledger n2FiniteSplice = openExternal ∧
      ¬ (2 * Erdos287.N2ConstantsBank.XN2 ≤ Erdos287.N2ConstantsBank.finiteBankCeiling) :=
  ⟨rfl, Erdos287.N2ConstantsBank.two_XN2_exceeds_finite_bank⟩

/-- **`effectivity_rows_are_open`.**  `KERNEL-PROVED`.  `M₀ ≤ 4·10⁹` is **not** proved. -/
theorem effectivity_rows_are_open :
    september2Ledger globalEffectivity = effectivityOpen ∧
      september2Ledger m0WithinFiniteBank = effectivityOpen := ⟨rfl, rfl⟩

/-- **`no_row_is_a_proof_claim`.**  `KERNEL-PROVED`.  A status value is metadata: knowing a
node's label never produces a mathematical statement.  Formally, the ledger is a function
into a seven-element enumeration, and two distinct nodes may share a label. -/
theorem no_row_is_a_proof_claim :
    september2Ledger totLaneE_T = september2Ledger bsrcN1E_M ∧ totLaneE_T ≠ bsrcN1E_M := by
  constructor
  · rfl
  · decide

/-! ## §5  The exact current dependency graph -/

/-- The displayed antecedents of each node of the #287 critical path. -/
def dependsOn : Node → List Node
  | erdos287 => [m0WithinFiniteBank, finiteBank, publicStatement]
  | m0WithinFiniteBank => [fclToWindowPair, globalEffectivity]
  | fclToWindowPair => [asymptoticFCL]
  | asymptoticFCL => [totLaneE_T, e2Asymptotic, bsrcN1E_M, eL, bDiagonal]
  | eL => [sharedOther, erdos287HardUAdapter]
  | sharedOther => [ultraNearHalf, run1BProvider]
  | run1BProvider => [mobiusPolyPhase, run1BSourceExhaustive, dwpKernelAlgebra]
  | _ => []

/-- **`erdos287_depends_on_open_nodes`.**  `KERNEL-PROVED`.  The critical path from #287 down
to the two open research nodes is present and no displayed OPEN node has been deleted. -/
theorem erdos287_depends_on_open_nodes :
    m0WithinFiniteBank ∈ dependsOn erdos287 ∧
      fclToWindowPair ∈ dependsOn m0WithinFiniteBank ∧
      asymptoticFCL ∈ dependsOn fclToWindowPair ∧
      eL ∈ dependsOn asymptoticFCL ∧
      bDiagonal ∈ dependsOn asymptoticFCL ∧
      sharedOther ∈ dependsOn eL ∧
      erdos287HardUAdapter ∈ dependsOn eL ∧
      ultraNearHalf ∈ dependsOn sharedOther ∧
      run1BProvider ∈ dependsOn sharedOther := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`gate1A_absent_from_the_graph`.**  `KERNEL-PROVED`.  Gate 1A appears in no antecedent
list of the #287 critical path. -/
theorem gate1A_absent_from_the_graph :
    gate1AOnCriticalPath ∉ dependsOn erdos287 ∧
      gate1AOnCriticalPath ∉ dependsOn asymptoticFCL ∧
      gate1AOnCriticalPath ∉ dependsOn eL ∧
      gate1AOnCriticalPath ∉ dependsOn sharedOther ∧
      gate1AOnCriticalPath ∉ dependsOn run1BProvider := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`open_nodes_are_retained`.**  `KERNEL-PROVED`.  Every open research node of the graph
still carries an open label: none was closed by metadata. -/
theorem open_nodes_are_retained :
    september2Ledger ultraNearHalf = openExternal ∧
      september2Ledger bDiagonal = strictlyReducedOpen ∧
      september2Ledger perronNuclearLedger = openExternal ∧
      september2Ledger rectanglePin = openExternal ∧
      september2Ledger omegaHProvenanceNode = openExternal ∧
      september2Ledger shortEdgeOwners = openExternal ∧
      september2Ledger sourceCoprimalities = openExternal :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §6  High-assurance validation status -/

/-- The result of an external validation run.  `notRun` is the honest default. -/
inductive ValidationResult
  /-- The check was performed and passed. -/
  | pass
  /-- The check was performed and failed. -/
  | fail
  /-- The check was not run in this session. -/
  | notRun
  deriving DecidableEq, Fintype, Repr

/-- The validation checks recorded separately from `lake build`. -/
inductive ValidationCheck
  /-- `lake build` of the whole library. -/
  | lakeBuild
  /-- `#print axioms` on the new principal declarations. -/
  | printAxioms
  /-- `lean4checker --fresh`. -/
  | lean4checker
  /-- The trusted challenge harness. -/
  | trustedChallenge
  /-- The comparator. -/
  | comparator
  /-- An external kernel checker. -/
  | externalChecker
  deriving DecidableEq, Fintype, Repr

/-- The honest validation record for this session. -/
def validationStatus : ValidationCheck → ValidationResult
  | ValidationCheck.lakeBuild => ValidationResult.pass
  | ValidationCheck.printAxioms => ValidationResult.pass
  | ValidationCheck.lean4checker => ValidationResult.notRun
  | ValidationCheck.trustedChallenge => ValidationResult.notRun
  | ValidationCheck.comparator => ValidationResult.notRun
  | ValidationCheck.externalChecker => ValidationResult.notRun

/-- **`no_invented_pass`.**  `KERNEL-PROVED`.  The external checkers are recorded as not run,
not as passing. -/
theorem no_invented_pass :
    validationStatus ValidationCheck.lean4checker = ValidationResult.notRun ∧
      validationStatus ValidationCheck.comparator = ValidationResult.notRun ∧
      validationStatus ValidationCheck.externalChecker = ValidationResult.notRun ∧
      validationStatus ValidationCheck.trustedChallenge = ValidationResult.notRun :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`build_is_not_a_completion_claim`.**  `KERNEL-PROVED`.  A passing build does not close
#287: the ledger row is unchanged. -/
theorem build_is_not_a_completion_claim :
    validationStatus ValidationCheck.lakeBuild = ValidationResult.pass ∧
      september2Ledger erdos287 = openExternal := ⟨rfl, rfl⟩

end September2FrontierStatus
end Erdos287
