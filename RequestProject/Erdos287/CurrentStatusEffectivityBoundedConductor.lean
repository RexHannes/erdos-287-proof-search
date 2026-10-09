import Mathlib
import RequestProject.Erdos287.CurrentStatusEffectivityEarly4490
import RequestProject.Erdos287.CompensatedMeasure
import RequestProject.Erdos287.HyperbolaInterfaces
import RequestProject.Erdos287.CompensatedSummationByParts
import RequestProject.Erdos287.AdjacentInterfaceFirewall
import RequestProject.Erdos287.ResidueCollapse
import RequestProject.Erdos287.InternalProductFibre
import RequestProject.Erdos287.SmallEllCRT
import RequestProject.Erdos287.HalfOpenProgressionCompiler
import RequestProject.Erdos287.SmallEllMeanCovariance
import RequestProject.Erdos287.CompensationLoop
import RequestProject.Erdos287.BoundedConductorFrontier
import RequestProject.Erdos287.RankThreeOperator
import RequestProject.Erdos287.RankThreeProjection
import RequestProject.Erdos287.ConductorComplementLedger
import RequestProject.Erdos287.AnnihilatorFamily
import RequestProject.Erdos287.DensityCompensationRestoration

/-!
# Erdős #287 effectivity — status after the bounded-conductor sync (§23)

INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.
**No public Erdős problem number is claimed here; public-problem-id provenance is `PENDING`.**

This module **extends** the earlier aggregators (`CurrentStatusEffectivity`,
`...LongFibre`, `...Multiplicity`, `...Early4490`).  Nothing earlier is rewritten or deleted:
the EARLY_4490 bank remains a valid ancestor, and its statements are untouched.

```
EARLY_4490 old rational-jet coordinate : SUPERSEDED AS CURRENT ROOT (still valid ancestor)
compensated interface                  : KERNEL-PROVED exact identity
ℓ ≤ 5000 CRT compiler                  : KERNEL-PROVED
ℓ ≤ 1000 cancellation                  : KERNEL-PROVED
1000 < ℓ ≤ 5000 finite kernel          : CURRENT k = 1 OPEN FRONTIER
positive finite-kernel wrapper         : RETIRED_NONCLOSING
rank three                             : STRICTLY_REDUCED
Ω(k) = 2                               : OPEN
Ω(k) = 1                               : OPEN
Early4490                              : OPEN / STRICTLY REDUCED
proper gamma                           : OPEN
S_live                                 : OPEN
R_012                                  : OPEN
signed floor                           : OPEN
Maynard                                : NOT_ENTERED
final splice                           : OPEN
public-problem-id provenance           : PENDING
```

The live frontier coordinate is `BOUNDED_CONDUCTOR_SIGNED_OUTER_Z`, i.e. the analytic goal
`Erdos287.Effectivity.FixedConductorCharacterBound`, which is **not** inhabited anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §23.1  The current evidence taxonomy (§1) -/

/-- The full current evidence taxonomy.  This *extends* the earlier `Evidence` type
(which is kept intact for the ancestor banks) by the three tags `externalAnalytic`,
`falseClaim` and `superseded`. -/
inductive EvidenceCurrent
  /-- entire proof reconstructed in the kernel -/
  | kernelProved
  /-- backed by a checked finite certificate / data object -/
  | certificateBacked
  /-- quoted external analytic input, not formally reconstructed -/
  | externalAnalytic
  /-- proved only under an explicitly stated analytic hypothesis -/
  | conditionalAnalytic
  /-- open -/
  | openNode
  /-- a method retired because it cannot close the target -/
  | retiredNonclosing
  /-- refuted -/
  | falseClaim
  /-- correct but no longer the current root coordinate -/
  | superseded
  /-- not entered into the programme -/
  | notEntered
  deriving DecidableEq, Repr

/-- Evidence classes that count as *closed* for bookkeeping purposes. -/
def EvidenceCurrent.isClosed : EvidenceCurrent → Bool
  | .kernelProved => true
  | .certificateBacked => true
  | .externalAnalytic => false
  | .conditionalAnalytic => false
  | .openNode => false
  | .retiredNonclosing => false
  | .falseClaim => false
  | .superseded => false
  | .notEntered => false

/-- The ancestor taxonomy embeds into the current one. -/
def EvidenceCurrent.ofAncestor : Evidence → EvidenceCurrent
  | .kernelProved => .kernelProved
  | .certificateBacked => .certificateBacked
  | .conditionalAnalytic => .conditionalAnalytic
  | .retiredNonclosingMethod => .retiredNonclosing
  | .openNode => .openNode
  | .notEntered => .notEntered

/-- **`evidence_embedding_preserves_closure`.**  `KERNEL-PROVED`.  The embedding of the
ancestor taxonomy does not turn an open ancestor node into a closed current node. -/
theorem evidence_embedding_preserves_closure (e : Evidence) :
    (EvidenceCurrent.ofAncestor e).isClosed = e.isClosed := by
  cases e <;> rfl

/-! ## §23.2  Checkpoint tag -/

/-- Checkpoint identifier for the data recorded in this module.  Any consumer of the
rank-three owner lists below must check this tag: the lists are a snapshot, not a theorem. -/
structure Checkpoint where
  /-- ISO date of the snapshot -/
  date : String
  /-- version label -/
  version : String
  deriving DecidableEq, Repr

/-- The checkpoint of the present bounded-conductor sync. -/
def boundedConductorCheckpoint : Checkpoint :=
  { date := "2026-09-08", version := "BOUNDED_CONDUCTOR_SYNC_v1" }

/-- **`checkpoint_tag_recorded`.**  Bookkeeping: the snapshot below is tagged. -/
theorem checkpoint_tag_recorded :
    boundedConductorCheckpoint.date = "2026-09-08" ∧
      boundedConductorCheckpoint.version = "BOUNDED_CONDUCTOR_SYNC_v1" :=
  ⟨rfl, rfl⟩

/-! ## §23.3  The tracked nodes of the bounded-conductor frontier -/

/-- The nodes tracked after the bounded-conductor sync. -/
inductive BoundedConductorNode
  /-- the whole EARLY_4490 rational-jet bank, as an ancestor -/
  | early4490BankAncestor
  /-- EARLY_4490 viewed as the *root* coordinate -/
  | early4490AsCurrentRoot
  /-- the compensated counting measure `G, Ĝ, Ê` -/
  | compensatedMeasure
  /-- the odd-convolution identity for the selected β-weight -/
  | oddConvolutionIdentity
  /-- exact hyperbola reparametrisations -/
  | hyperbolaInterfaces
  /-- the four-term compensated summation by parts -/
  | compensatedSummationByParts
  /-- the adjacent-interface exact identity -/
  | adjacentInterfaceIdentity
  /-- the "adjacent shell only" route -/
  | adjacentShellOnlyRoute
  /-- the complete residue-class collapse -/
  | residueClassCollapse
  /-- absence of the top diagonal `s = z` -/
  | topDiagonalAbsent
  /-- the `E = 5000` cutoff-preserving shift sieve -/
  | truncatedShiftSieve
  /-- the internal product fibre `ℓ = d·t` -/
  | internalProductFibre
  /-- the firewall `internal ℓ ≠ conductor f` -/
  | internalEllFirewall
  /-- the complete small-`ℓ` local formula -/
  | smallEllLocalFormula
  /-- the CRT expansion and its atom count -/
  | crtExpansion
  /-- the bound `3^ω − 2^ω ≤ 65` for odd squarefree `ℓ ≤ 5000` -/
  | crtAtomBound
  /-- the exact half-open progression compiler -/
  | halfOpenProgressionCompiler
  /-- the small-`ℓ` local mean `−μ(ℓ)β(ℓ)/ℓ` -/
  | smallEllLocalMean
  /-- the complete-period covariance and its quadratic form -/
  | completePeriodCovariance
  /-- the exact `k = 1` density/compensation source identity -/
  | densityCompensationIdentity
  /-- the exact atomwise cancellation for `ℓ ≤ 1000` -/
  | loopCancellationSmallEll
  /-- the returned finite-conductor kernel for `1000 < ℓ ≤ 5000` -/
  | returnedFiniteConductorKernel
  /-- the exact-loop firewall -/
  | exactLoopFirewall
  /-- the positive finite-kernel wrapper -/
  | positiveFiniteKernelWrapper
  /-- the bounded-conductor `k = 1` analytic target -/
  | boundedConductorK1Target
  /-- the fixed-conductor character/DFT bound -/
  | fixedConductorCharacterBound
  /-- the rank-three operator algebra -/
  | rankThreeOperatorAlgebra
  /-- the primitive projection interfaces -/
  | rankThreeProjection
  /-- the numeric rank-three owner closures -/
  | rankThreeNumericOwners
  /-- the conductor/complement ledger architecture -/
  | conductorComplementLedger
  /-- the annihilator-family mechanism -/
  | annihilatorFamily
  /-- the finite census of certified annihilator pairs -/
  | annihilatorCensus
  /-- rank three as a whole -/
  | rankThreeSlab
  /-- `Ω(k) = 2` -/
  | omegaTwo
  /-- `Ω(k) = 1` -/
  | omegaOne
  /-- the EARLY_4490 reduction leaf -/
  | early4490Leaf
  /-- proper gamma -/
  | properGamma
  /-- `S_live` -/
  | sLive
  /-- `R_012` -/
  | r012
  /-- the signed floor -/
  | signedFloor
  /-- Maynard-type input -/
  | maynard
  /-- the final splice -/
  | finalSplice
  /-- the effectivity leaf as a whole -/
  | effectivityLeaf
  /-- provenance of a public problem identifier -/
  | publicProblemIdProvenance
  deriving DecidableEq, Repr

/-- The evidence class of each tracked node at the current checkpoint. -/
def boundedConductorEvidence : BoundedConductorNode → EvidenceCurrent
  | .early4490BankAncestor => .certificateBacked
  | .early4490AsCurrentRoot => .superseded
  | .compensatedMeasure => .kernelProved
  | .oddConvolutionIdentity => .kernelProved
  | .hyperbolaInterfaces => .kernelProved
  | .compensatedSummationByParts => .kernelProved
  | .adjacentInterfaceIdentity => .kernelProved
  | .adjacentShellOnlyRoute => .retiredNonclosing
  | .residueClassCollapse => .kernelProved
  | .topDiagonalAbsent => .kernelProved
  | .truncatedShiftSieve => .kernelProved
  | .internalProductFibre => .kernelProved
  | .internalEllFirewall => .kernelProved
  | .smallEllLocalFormula => .kernelProved
  | .crtExpansion => .kernelProved
  | .crtAtomBound => .kernelProved
  | .halfOpenProgressionCompiler => .kernelProved
  | .smallEllLocalMean => .kernelProved
  | .completePeriodCovariance => .kernelProved
  | .densityCompensationIdentity => .kernelProved
  | .loopCancellationSmallEll => .kernelProved
  | .returnedFiniteConductorKernel => .openNode
  | .exactLoopFirewall => .kernelProved
  | .positiveFiniteKernelWrapper => .retiredNonclosing
  | .boundedConductorK1Target => .openNode
  | .fixedConductorCharacterBound => .openNode
  | .rankThreeOperatorAlgebra => .kernelProved
  | .rankThreeProjection => .kernelProved
  | .rankThreeNumericOwners => .certificateBacked
  | .conductorComplementLedger => .kernelProved
  | .annihilatorFamily => .kernelProved
  | .annihilatorCensus => .certificateBacked
  | .rankThreeSlab => .openNode
  | .omegaTwo => .openNode
  | .omegaOne => .openNode
  | .early4490Leaf => .openNode
  | .properGamma => .openNode
  | .sLive => .openNode
  | .r012 => .openNode
  | .signedFloor => .openNode
  | .maynard => .notEntered
  | .finalSplice => .openNode
  | .effectivityLeaf => .openNode
  | .publicProblemIdProvenance => .openNode

/-- The nodes that must remain unclosed after this run. -/
def boundedConductorOpenNodes : List BoundedConductorNode :=
  [.returnedFiniteConductorKernel, .boundedConductorK1Target, .fixedConductorCharacterBound,
   .rankThreeSlab, .omegaTwo, .omegaOne, .early4490Leaf, .properGamma, .sLive, .r012,
   .signedFloor, .maynard, .finalSplice, .effectivityLeaf, .publicProblemIdProvenance,
   .adjacentShellOnlyRoute, .positiveFiniteKernelWrapper, .early4490AsCurrentRoot]

/-- **`boundedConductor_open_frontier`.**  `KERNEL-PROVED`.  No node of the current open
frontier is tagged `kernelProved` or `certificateBacked`; in particular none is closed.
The public-problem-id provenance is recorded as unresolved and Maynard as `NOT_ENTERED`. -/
theorem boundedConductor_open_frontier :
    (∀ n ∈ boundedConductorOpenNodes,
        boundedConductorEvidence n ≠ EvidenceCurrent.kernelProved ∧
          boundedConductorEvidence n ≠ EvidenceCurrent.certificateBacked ∧
          (boundedConductorEvidence n).isClosed = false) ∧
      boundedConductorEvidence .maynard = EvidenceCurrent.notEntered ∧
      boundedConductorEvidence .publicProblemIdProvenance = EvidenceCurrent.openNode ∧
      boundedConductorEvidence .effectivityLeaf = EvidenceCurrent.openNode := by
  refine ⟨by decide, rfl, rfl, rfl⟩

/-- **`early4490_preserved_as_ancestor`.**  `KERNEL-PROVED`.  The EARLY_4490 bank is preserved:
it keeps its certificate-backed status as an ancestor, while only its role as *current root
coordinate* is `SUPERSEDED`. -/
theorem early4490_preserved_as_ancestor :
    boundedConductorEvidence .early4490BankAncestor = EvidenceCurrent.certificateBacked ∧
      boundedConductorEvidence .early4490AsCurrentRoot = EvidenceCurrent.superseded ∧
      boundedConductorEvidence .early4490Leaf = EvidenceCurrent.openNode :=
  ⟨rfl, rfl, rfl⟩

/-- **`current_k1_frontier_is_bounded_conductor`.**  `KERNEL-PROVED` bookkeeping: the current
`k = 1` frontier is the bounded-conductor signed outer-`z` estimate, the `ℓ ≤ 1000` layer is
kernel-cancelled, and the `1000 < ℓ ≤ 5000` layer is the open node. -/
theorem current_k1_frontier_is_bounded_conductor :
    boundedConductorEvidence .loopCancellationSmallEll = EvidenceCurrent.kernelProved ∧
      boundedConductorEvidence .returnedFiniteConductorKernel = EvidenceCurrent.openNode ∧
      boundedConductorEvidence .exactLoopFirewall = EvidenceCurrent.kernelProved ∧
      boundedConductorEvidence .positiveFiniteKernelWrapper =
        EvidenceCurrent.retiredNonclosing :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §23.4  Rank-three owner data (§22), tagged by checkpoint -/

/-- A snapshot of the rank-three owner bookkeeping.  This is **data**, tagged by a
checkpoint; no whole-slab analytic inequality is kernel-promoted. -/
structure RankThreeSnapshot where
  /-- the checkpoint this snapshot belongs to -/
  checkpoint : Checkpoint
  /-- the `k`-owners closed by certificate at this checkpoint -/
  closedOwners : List ℕ
  /-- the `k`-owners still remaining at this checkpoint -/
  remainingOwners : List ℕ
  /-- the evidence tag carried by the closed list -/
  evidence : EvidenceCurrent
  deriving DecidableEq, Repr

/-- The current rank-three snapshot.  The closed list is `CERTIFICATE_BACKED`. -/
def rankThreeSnapshot : RankThreeSnapshot where
  checkpoint := boundedConductorCheckpoint
  closedOwners := [105, 165, 195, 231, 255, 273, 285, 345, 357, 385]
  remainingOwners := [15015, 5005, 3003, 2145, 1365, 1155]
  evidence := EvidenceCurrent.certificateBacked

/-- **`rankThree_snapshot_is_certificate_backed`.**  The rank-three owner lists are carried as
certificate-backed data at a tagged checkpoint, never as kernel-proved whole-slab
inequalities, and the closed and remaining lists are disjoint. -/
theorem rankThree_snapshot_is_certificate_backed :
    rankThreeSnapshot.evidence = EvidenceCurrent.certificateBacked ∧
      rankThreeSnapshot.checkpoint = boundedConductorCheckpoint ∧
      (∀ k ∈ rankThreeSnapshot.closedOwners, k ∉ rankThreeSnapshot.remainingOwners) := by
  refine ⟨rfl, rfl, by decide⟩

/-- **`rankThree_strictly_reduced`.**  Bookkeeping: rank three is strictly reduced but the slab
as a whole is still open. -/
theorem rankThree_strictly_reduced :
    rankThreeSnapshot.closedOwners ≠ [] ∧
      rankThreeSnapshot.remainingOwners ≠ [] ∧
      boundedConductorEvidence .rankThreeSlab = EvidenceCurrent.openNode := by
  refine ⟨by decide, by decide, rfl⟩

/-! ## §23.5  The open frontier is not inhabited -/

/-- **`frontier_targets_not_inhabited`.**  `KERNEL-PROVED`.  The two open analytic interfaces
are recorded as open nodes; nothing in this bank inhabits them.  (Formally: the status
function tags them `openNode`; the propositions themselves appear only as hypotheses of the
conditional theorem `character_bound_implies_k1_owner_bound`.) -/
theorem frontier_targets_not_inhabited :
    boundedConductorEvidence .boundedConductorK1Target = EvidenceCurrent.openNode ∧
      boundedConductorEvidence .fixedConductorCharacterBound = EvidenceCurrent.openNode :=
  ⟨rfl, rfl⟩

/-! ## §23.6  Axiom audit (§26) -/

section AxiomAudit

#print axioms compensated_summation_by_parts
#print axioms residue_class_collapse
#print axioms top_diagonal_absent
#print axioms internal_product_fibre_identity
#print axioms Kell_crt_expansion
#print axioms crt_atoms_le_65
#print axioms smallEll_local_mean
#print axioms gram_quadratic_form
#print axioms loop_cancellation_le_1000
#print axioms reassembly_exact_loop
#print axioms returnedKernel_not_identically_zero
#print axioms character_bound_implies_k1_owner_bound
#print axioms DeltaOp_discrepancy_identity
#print axioms rankThree_extremum_finitely_many_cells
#print axioms owner_sources_pairwise_disjoint
#print axioms certified_pair_annihilates
#print axioms Ttilde_split
#print axioms DX_term_not_removable
#print axioms boundedConductor_open_frontier

end AxiomAudit

end Effectivity
end Erdos287
