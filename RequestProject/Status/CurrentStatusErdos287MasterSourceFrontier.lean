import RequestProject.CurrentProgramme.Erdos287SourceCoverageCompiler
import RequestProject.CurrentProgramme.Erdos287TypedSourcePacketCompiler
import RequestProject.CurrentProgramme.Erdos287PerronInterfaceCounterguard
import RequestProject.Status.SemanticFirewallsErdos287
import RequestProject.Status.CurrentAuthoritativeStatusErdos287
import RequestProject.Status.Erdos287EndToEndStatus
import RequestProject.Status.PublicTreeReconciliation20260901

/-!
# Erdős #287 — master-source frontier status layer (append-only, controlling metadata)

This is a **later** status layer.  It does not rewrite, weaken or contradict any earlier
status file: earlier simultaneous-critical and local-closure candidate layers remain
historical records, and the precedence rule of
`RequestProject/Status/CurrentAuthoritativeStatusErdos287.lean` continues to apply — later
layers govern *labels*, never mathematical content.

It records the verdict of the current source-census hostile audit:

* the **first frontier** is `UNPROJECTED-MASTER-PHYSICAL-SOURCE-REALISATION45`: OPEN;
* the **next** node is `MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45`: OPEN;
* `PROOFOMEGA-ABSTRACT-PARTITION45` and `PROOFOMEGA-LOCAL-FINITENESS45`: kernel-proved
  (as abstract certificates), while `UNPROJECTED-SOURCE-OMEGA-INSERTION45` is OPEN;
* `PERRON-SINGLE-CONTOUR-L1-45`: kernel-proved analytic lemma;
* `PERRON-COMPLETE-TYPED-SOURCEPACKET-COMPILER45`: kernel-proved **conditional** compiler;
* `PERRON-CURRENT-INTERFACE-SUFFICIENCY45`: **FAIL**, with a finite countermodel;
* `BDIAGONAL-DELTAXQA-HILBERT-UNITARYFOURIER45`: kernel-proved abstract finite kernel,
  while the physical b-diagonal dictionary is OPEN;
* `FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45`: OPEN; `WindowPairSupply` for all large `M`: OPEN;
  **ERDŐS #287: OPEN**.

Superseded old claims are recorded in §4 (superseded ≠ false).  No theorem named `erdos287`
is added anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace MasterSourceFrontier

/-! ## §1  Node classification -/

/-- Admissible statuses of a frontier node. -/
inductive FrontierStatus
  /-- A kernel-checked theorem with no undischarged mathematical hypothesis. -/
  | kernelProved
  /-- A kernel-checked *conditional* compiler: analytic/physical inputs remain hypotheses. -/
  | kernelProvedConditional
  /-- A structure interface that is deliberately left uninhabited. -/
  | uninhabitedInterface
  /-- Refuted as stated, with an explicit countermodel. -/
  | failCountermodel
  /-- Open: neither proved here nor reduced to anything proved here. -/
  | open_
  deriving DecidableEq, Fintype, Repr

/-- The nodes classified by this layer. -/
inductive FrontierNode
  /-- `UNPROJECTED-MASTER-PHYSICAL-SOURCE-REALISATION45`. -/
  | masterPhysicalSourceRealisation
  /-- `MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45`. -/
  | masterSourceToTypedPerronPackets
  /-- `PROOFOMEGA-ABSTRACT-PARTITION45`. -/
  | proofOmegaAbstractPartition
  /-- `PROOFOMEGA-LOCAL-FINITENESS45`. -/
  | proofOmegaLocalFiniteness
  /-- `UNPROJECTED-SOURCE-OMEGA-INSERTION45`. -/
  | unprojectedSourceOmegaInsertion
  /-- `PERRON-SINGLE-CONTOUR-L1-45`. -/
  | perronSingleContourL1
  /-- `PERRON-COMPLETE-TYPED-SOURCEPACKET-COMPILER45`. -/
  | perronTypedPacketCompiler
  /-- `PERRON-CURRENT-INTERFACE-SUFFICIENCY45`. -/
  | perronCurrentInterfaceSufficiency
  /-- `BDIAGONAL-DELTAXQA-HILBERT-UNITARYFOURIER45`. -/
  | bDiagonalDeltaQAbstract
  /-- The physical b-diagonal nuclear dictionary. -/
  | bDiagonalPhysicalDictionary
  /-- The `C0` source-realisation bridge. -/
  | c0SourceRealisationBridge
  /-- The transverse source-realisation bridge. -/
  | transverseSourceRealisationBridge
  /-- Abstract owner-map bookkeeping. -/
  | abstractOwnerMap
  /-- Physical 100% source coverage. -/
  | physicalSourceCoverage100
  /-- `FULL-SOURCE-LOCAL-ANALYTIC-KERNEL45`. -/
  | fullSourceLocalAnalyticKernel
  /-- `WindowPairSupply` for all large `M`. -/
  | windowPairSupplyLargeM
  /-- Erdős #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- **The controlling status table of this layer.** -/
def status : FrontierNode → FrontierStatus
  | .masterPhysicalSourceRealisation => .open_
  | .masterSourceToTypedPerronPackets => .open_
  | .proofOmegaAbstractPartition => .kernelProved
  | .proofOmegaLocalFiniteness => .kernelProved
  | .unprojectedSourceOmegaInsertion => .open_
  | .perronSingleContourL1 => .kernelProved
  | .perronTypedPacketCompiler => .kernelProvedConditional
  | .perronCurrentInterfaceSufficiency => .failCountermodel
  | .bDiagonalDeltaQAbstract => .kernelProved
  | .bDiagonalPhysicalDictionary => .uninhabitedInterface
  | .c0SourceRealisationBridge => .uninhabitedInterface
  | .transverseSourceRealisationBridge => .uninhabitedInterface
  | .abstractOwnerMap => .kernelProved
  | .physicalSourceCoverage100 => .uninhabitedInterface
  | .fullSourceLocalAnalyticKernel => .open_
  | .windowPairSupplyLargeM => .open_
  | .erdos287 => .open_

/-- **Erdős #287 is open in this layer.** -/
theorem erdos287_open : status .erdos287 = .open_ := by decide +kernel

/-- **The current first frontier** is the unprojected master physical source realisation,
and it is open. -/
theorem first_frontier_open : status .masterPhysicalSourceRealisation = .open_ := by
  decide +kernel

/-- **The next research frontier** — master source to typed Perron packets — is open. -/
theorem next_frontier_open : status .masterSourceToTypedPerronPackets = .open_ := by
  decide +kernel

/-- The full-source local analytic kernel is **not** closed. -/
theorem fullSourceLocalAnalyticKernel_open :
    status .fullSourceLocalAnalyticKernel = .open_ := by decide +kernel

/-- `WindowPairSupply` for all large `M` remains open. -/
theorem windowPairSupply_open : status .windowPairSupplyLargeM = .open_ := by decide +kernel

/-- Status labels are pairwise distinct: a conditional compiler is not a theorem, an
uninhabited interface is not a proof, and a countermodel is not a status of success. -/
theorem status_labels_distinct :
    FrontierStatus.kernelProvedConditional ≠ FrontierStatus.kernelProved ∧
      FrontierStatus.uninhabitedInterface ≠ FrontierStatus.kernelProved ∧
      FrontierStatus.failCountermodel ≠ FrontierStatus.kernelProved ∧
      FrontierStatus.open_ ≠ FrontierStatus.kernelProved := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Exactly five nodes of this layer are unconditionally kernel-proved. -/
theorem kernelProved_node_count :
    (Finset.univ.filter (fun n : FrontierNode => status n = .kernelProved)).card = 5 := by
  decide +kernel

/-- Exactly six nodes of this layer are open. -/
theorem open_node_count :
    (Finset.univ.filter (fun n : FrontierNode => status n = .open_)).card = 6 := by
  decide +kernel

/-! ## §2  The status table is backed by the kernel where it claims to be -/

/-- The `PROOFOMEGA-ABSTRACT-PARTITION45` row is backed by an actual theorem: the exact
insertion identity for an abstract partition certificate. -/
theorem backing_proofOmegaAbstractPartition (I : Finset ℕ) (weight kernel : ℕ → ℂ) :
    MasterSource.unprojectedSource I weight kernel
      = ∑ k ∈ ProofOmega.trivialPartition.scales,
          ProofOmega.projectedSource I ProofOmega.trivialPartition.weight k weight kernel :=
  ProofOmega.unprojectedSource_eq_sum_projectedSource_of_partition I
    ProofOmega.trivialPartition weight kernel

/-- The `PROOFOMEGA-LOCAL-FINITENESS45` row is backed by the concrete finite theorem. -/
theorem backing_proofOmegaLocalFiniteness (g N : ℕ) :
    (ProofOmega.contributingScales g N).card ≤ 3 :=
  ProofOmega.dyadicLocalFiniteness g N

/-- The `PERRON-SINGLE-CONTOUR-L1-45` row is backed by the exact integral identity. -/
theorem backing_perronSingleContour (c T : ℝ) (hc : 0 < c) :
    (∫ t in (-T)..T, (Real.sqrt (c ^ 2 + t ^ 2))⁻¹) = 2 * Real.arsinh (T / c) :=
  PerronContour.singleContour_integral_eq_arsinh c T hc

/-- The `PERRON-CURRENT-INTERFACE-SUFFICIENCY45` FAIL row is backed by the countermodel. -/
theorem backing_perronInterfaceFail :
    ¬ ∃ G : ℝ, ∀ (n : ℕ) (mass : ℕ → ℝ),
        (∀ i ∈ Finset.range n, |mass i| ≤ 1) → ∑ i ∈ Finset.range n, mass i ≤ G :=
  PerronCounterguard.no_global_total_from_perContour_bound

/-- The `BDIAGONAL-DELTAXQA` row is backed by the abstract finite Fourier kernel. -/
theorem backing_bDiagonalDeltaQAbstract {n : ℕ} [NeZero n] {u : ZMod n} (hu : IsUnit u)
    (D Q : Finset (ZMod n)) (hD : ∀ d ∈ D, IsUnit d) (hQ : ∀ q ∈ Q, IsUnit q)
    (A B : ZMod n → ℂ) :
    ‖∑ d ∈ D, ∑ q ∈ Q, A d * B q * ZMod.stdAddChar (d * u * q⁻¹)‖ ^ 2
      ≤ (n : ℝ) * (∑ d ∈ D, ‖A d‖ ^ 2) * (∑ q ∈ Q, ‖B q‖ ^ 2) :=
  BDiagonalDeltaQ.deltaQ_unitaryFourier_bound hu D Q hD hQ A B

/-- The uninhabited rows are backed by emptiness theorems at the countermodel spec. -/
theorem backing_uninhabited_rows :
    ¬ Nonempty (MasterSource.MasterPhysicalSourceRealisation
        MasterSource.vanishingWeightSpec) ∧
      ¬ Nonempty (PhysicalDictionary.C0SourceRealisationBridge
        MasterSource.vanishingWeightSpec) ∧
      ¬ Nonempty (PhysicalDictionary.TransverseSourceRealisationBridge
        MasterSource.vanishingWeightSpec) ∧
      ¬ Nonempty (SourceCoverage.PhysicalSourceCoverage100
        MasterSource.vanishingWeightSpec) :=
  ⟨MasterSource.no_realisation_vanishingWeightSpec,
    PhysicalDictionary.c0SourceRealisationBridge_open,
    PhysicalDictionary.transverseSourceRealisationBridge_open,
    SourceCoverage.physicalSourceCoverage100_open⟩

/-! ## §3  End-to-end firewall against `Erdos287ClosureInputs` -/

/-- The new master-source frontier modules, as a finite ledger. -/
inductive FrontierModule
  /-- The master source interface. -/
  | masterSourceInterface
  /-- The proof-local Ω partition module. -/
  | proofOmegaPartition
  /-- The single Perron contour module. -/
  | perronSingleContour
  /-- The typed source-packet compiler. -/
  | typedSourcePacketCompiler
  /-- The Perron interface counterguard. -/
  | perronInterfaceCounterguard
  /-- The abstract `Δ × q` b-diagonal kernel. -/
  | bDiagonalDeltaQAbstract
  /-- The physical dictionary interfaces. -/
  | physicalDictionaryInterfaces
  /-- The source coverage compiler. -/
  | sourceCoverageCompiler
  deriving DecidableEq, Fintype, Repr

/-- **Metadata.**  No module of this frontier pass constructs an `Erdos287ClosureInputs`
inhabitant.  This is bookkeeping, and is deliberately labelled as such: the mathematical
guards are the emptiness theorems of §2 and the compiler visibility below. -/
def constructsClosureInputs : FrontierModule → Bool := fun _ => false

/-- **Ledger.**  All eight new modules are recorded as *not* constructing a closure-inputs
inhabitant. -/
theorem no_frontier_module_constructs_closureInputs :
    (∀ m : FrontierModule, constructsClosureInputs m = false) ∧
      Fintype.card FrontierModule = 8 := by
  refine ⟨fun _ => rfl, by decide +kernel⟩

/-- The end-to-end compiler is unchanged and reconfirmed. -/
theorem reconfirm_endToEnd_frontier (I : Erdos287ClosureInputs) : Erdos287Statement :=
  no_Erdos287Counterexample_of_closure I

/-- **The `supply` field stays visible**: an inhabitant of the closure inputs is exactly a
window-pair supply above its own threshold, and this pass supplies none. -/
theorem closureInputs_supply_still_visible (I : Erdos287ClosureInputs) :
    ∀ M : ℕ, I.M0 ≤ M → WindowPairSupply M := I.supply

/-- **No new route to the statement.**  The frontier work of this pass is compatible with
the statement node still being open: the classification records `erdos287` as `open_` while
every proved node of this layer is an abstract or conditional kernel result. -/
theorem frontier_work_does_not_close_statement :
    status .erdos287 = .open_ ∧
      status .masterPhysicalSourceRealisation = .open_ ∧
      status .bDiagonalPhysicalDictionary = .uninhabitedInterface ∧
      status .perronTypedPacketCompiler = .kernelProvedConditional := by
  decide +kernel

/-! ## §4  Supersession ledger (superseded ≠ false) -/

/-- Old claims this layer re-labels. -/
inductive OldClaim
  /-- "PERRON-CONDITION-REMOVAL CLOSED". -/
  | perronConditionRemovalClosed
  /-- "b-diagonal physical closure". -/
  | bDiagonalPhysicalClosure
  deriving DecidableEq, Fintype, Repr

/-- The controlling re-labelling. -/
inductive ClaimVerdict
  /-- Not supported by the current public physical input; the conditional compiler
  survives. -/
  | notSupportedConditionalSurvives
  /-- The abstract kernel survives; the physical dictionary is open. -/
  | abstractSurvivesPhysicalOpen
  deriving DecidableEq, Fintype, Repr

/-- The verdict attached to each old claim by this (controlling) layer. -/
def oldClaimVerdict : OldClaim → ClaimVerdict
  | .perronConditionRemovalClosed => .notSupportedConditionalSurvives
  | .bDiagonalPhysicalClosure => .abstractSurvivesPhysicalOpen

/-- Neither old claim is re-labelled as closed, and the two verdicts are distinct. -/
theorem oldClaims_relabelled :
    oldClaimVerdict .perronConditionRemovalClosed = .notSupportedConditionalSurvives ∧
      oldClaimVerdict .bDiagonalPhysicalClosure = .abstractSurvivesPhysicalOpen ∧
      ClaimVerdict.notSupportedConditionalSurvives ≠ ClaimVerdict.abstractSurvivesPhysicalOpen := by
  refine ⟨rfl, rfl, ?_⟩; decide +kernel

/-- **Superseded ≠ false.**  The surviving content of the two re-labelled claims is
explicit: the typed packet compiler and the abstract `Δ × q` kernel are both still
kernel-proved in this layer. -/
theorem superseded_claims_retain_content :
    status .perronTypedPacketCompiler = .kernelProvedConditional ∧
      status .bDiagonalDeltaQAbstract = .kernelProved := by
  decide +kernel

/-! ## §5  Preserved semantic hygiene (imported, not duplicated)

The `Gap2CE` one-way firewall, the exact public problem predicate, the classification of
`WindowPairSupply` as a *sufficient compiler input*, the three-level `C0` status, the
four-object Ω distinction and the Type-II naming split all live in the imported modules
`Status/SemanticFirewallsErdos287.lean`, `Status/CurrentAuthoritativeStatusErdos287.lean`
and `Status/PublicTreeReconciliation20260901.lean`.  They are reused here, not restated.

The only genuinely *new* semantic distinction introduced by this pass is the one between a
proof-local Ω partition and the historical `Ω_H` objects; it is recorded below. -/

/-- **Proof-local Ω is a new object.**  The proof-local partition of this pass is an
abstract certificate on an arbitrary type; nothing identifies it with any historical
`Ω_H` object, and the only property used of it is the exact partition of unity. -/
theorem proofOmega_is_abstract_certificate (P : ProofOmega.DyadicPartition ℕ) (x : ℕ) :
    ∑ k ∈ P.scales, P.weight k x = 1 := P.partition_of_unity x

end MasterSourceFrontier
end Erdos287
