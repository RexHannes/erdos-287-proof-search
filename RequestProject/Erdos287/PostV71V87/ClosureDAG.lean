import RequestProject.Erdos287.PostV71V87.RegressionFixtures
import RequestProject.Erdos287.PostV71V87.AnalyticProviders
import RequestProject.Erdos287.PostV71V87.MinorRepair
import RequestProject.Erdos287.PostV71V87.EndpointCRT
import RequestProject.Erdos287.PostV71V87.Positional
import RequestProject.Erdos287.PostV71V87.RepairedRecurrence
import RequestProject.Erdos287.PostV71V87.Physical
import RequestProject.Erdos287.PostV71V87.Firewalls

/-!
# Erdős #287 (post-V71 → V87) — machine-checkable closure DAG

Every node of the audited bank carries

* a status: `bankedExact` (proved unconditionally in Lean), `conditional` (proved in Lean
  from an explicit, never-inhabited provider), `retired` (proved, but not a closure route), or
  `open` (no proof; either a provider interface or an unformalised claim);
* the Lean declaration it refers to (double-backtick name literals, so a renamed or missing declaration
  breaks the build), or `none` for claims that have no formal statement;
* its list of direct dependencies.

The structural invariants below are checked by `decide` (kernel reduction, no
`native_decide`):

* `dag_acyclic`        — every edge strictly decreases the rank;
* `dag_exact_closed`   — a banked-exact node depends only on banked-exact nodes;
* `dag_exact_support`  — the whole transitive support of a banked-exact node is banked exact;
* `dag_conditional_has_open` — every conditional node transitively depends on an open node;
* `dag_no_retired_use` — no exact or conditional node transitively depends on a retired node;
* `dag_erdos287_open`, `dag_erdos287_no_decl` — the Erdős #287 node is `open`, with no Lean
  declaration claiming it;
* `dag_erdos287_inputs_not_exact`, `dag_erdos287_open_support` — no direct input of the
  Erdős #287 node is banked exact, and its support contains exactly the open nodes
  `crossScaleSync`, `finiteExclusion`, `proximity`, `intermediateScales`.
-/

namespace Erdos287.PostV71V87.DAG

/-- Status of a node in the closure DAG. -/
inductive Status
  | bankedExact
  | conditional
  | retired
  | open
  deriving DecidableEq, Repr

/-- Nodes of the post-V71 → V87 bank. -/
inductive Node
  -- model
  | exactWordModel
  | counterexampleEquiv
  | surrogateSeparation
  -- V83 (retired minor route)
  | minorRelation
  | minorDenominator
  | fixedDepthCompression
  | fixedDepthNotExact
  | integerDetIntegral
  | minorRouteClosure
  -- V84/V85 positional
  | topLayerTwo
  | singletonRejection
  | conditionedRowRejection
  | positionalChain
  | qTwoLeD
  -- V84/V85 analytic providers and consequences
  | providerFixedSupply
  | providerUniformSupply
  | fixedModulusSaturation
  | fixedBaseGrowth
  | uniformModulusSaturation
  | growingBaseGrowth
  | maximalCarrierUniform
  -- V86 endpoint-anchored CRT
  | endpointCRT
  | qPairBound
  | smallCeilingUnique
  | lowStartChamber
  | dyadicSaturation
  | ceilingAnnulus
  | ownerDisjoint
  | roughPartAggregate
  -- V87 reciprocal image / minimal grid
  | chebyshevImported
  | srecBlockBound
  | logSrecBound
  | shellFingerprint
  | entropyInequality
  | entropyInversion
  | repairedRecurrence
  -- physical consequences
  | internalMultiples
  | guardPattern
  | disjointGuards
  | carrierReserve
  | carrierOverlap
  | carrierUnion
  -- high-shell / terminal firewalls
  | highShellTrivial
  | providerHighShell
  | highShellEmptyRow
  | intermediateScales
  | nearbyTransition
  | polylogWindowFirewall
  -- open frontier
  | proximity
  | crossScaleSync
  | finiteExclusion
  | tailClosure
  | erdos287ConditionalOnSync
  | erdos287
  deriving DecidableEq, Repr, Fintype

open Node Status

/-- Status assignment. -/
def status : Node → Status
  | exactWordModel | counterexampleEquiv | surrogateSeparation => bankedExact
  | minorRelation | minorDenominator | fixedDepthCompression | fixedDepthNotExact
  | integerDetIntegral => bankedExact
  | minorRouteClosure => retired
  | topLayerTwo | singletonRejection | conditionedRowRejection | positionalChain
  | qTwoLeD => bankedExact
  | providerFixedSupply | providerUniformSupply => .open
  | fixedModulusSaturation | fixedBaseGrowth | uniformModulusSaturation | growingBaseGrowth
  | maximalCarrierUniform => conditional
  | endpointCRT | qPairBound | smallCeilingUnique | lowStartChamber | dyadicSaturation
  | ceilingAnnulus | ownerDisjoint => bankedExact
  | roughPartAggregate => .open
  | chebyshevImported | srecBlockBound | logSrecBound | shellFingerprint | entropyInequality
  | entropyInversion | repairedRecurrence => bankedExact
  | internalMultiples | guardPattern | disjointGuards | carrierReserve | carrierOverlap
  | carrierUnion => bankedExact
  | highShellTrivial => bankedExact
  | providerHighShell => .open
  | highShellEmptyRow => conditional
  | intermediateScales | nearbyTransition => .open
  | polylogWindowFirewall => bankedExact
  | proximity | crossScaleSync | finiteExclusion => .open
  | tailClosure | erdos287ConditionalOnSync => conditional
  | erdos287 => .open

/-- Lean declaration backing each node (`none` = no formal statement exists). -/
def decl : Node → Option Lean.Name
  | exactWordModel => some ``ExactWord
  | counterexampleEquiv => some ``ExactWord.toCounterexample
  | surrogateSeparation => some ``reg_surrogate_not_exact
  | minorRelation => some ``MinorData.actual_sub_target
  | minorDenominator => some ``MinorData.den_actual
  | fixedDepthCompression => some ``fixed_depth_compression
  | fixedDepthNotExact => some ``fixed_depth_not_exact_mass
  | integerDetIntegral => some ``integer_det_integral
  | minorRouteClosure => none
  | topLayerTwo => some ``ExactWord.two_le_layer_card
  | singletonRejection => some ``ExactWord.not_active_of_lt_two_mul
  | conditionedRowRejection => some ``ExactWord.conditioned_row_rejection
  | positionalChain => some ``ExactWord.positional_chain
  | qTwoLeD => some ``ExactWord.Q_two_le_D
  | providerFixedSupply => some ``FixedModulusDyadicSupply
  | providerUniformSupply => some ``UniformDyadicSupply
  | fixedModulusSaturation => some ``fixed_modulus_saturation
  | fixedBaseGrowth => some ``fixed_base_primary_growth
  | uniformModulusSaturation => some ``uniform_modulus_saturation
  | growingBaseGrowth => some ``growing_base_primary_growth
  | maximalCarrierUniform => some ``maximal_carrier_of_uniform
  | endpointCRT => some ``Word.endpoint_anchored_crt
  | qPairBound => some ``Word.Q_mul_Q_gt_D
  | smallCeilingUnique => some ``Word.card_small_ceilings_le_one
  | lowStartChamber => some ``Word.low_start_chamber
  | dyadicSaturation => some ``ExactWord.dyadic_two_sided_saturation
  | ceilingAnnulus => some ``ExactWord.ceiling_annulus
  | ownerDisjoint => some ``Word.owner_disjoint
  | roughPartAggregate => none
  | chebyshevImported => some ``chebyshev_upper
  | srecBlockBound => some ``Srec_block_bound
  | logSrecBound => some ``log_Srec_le
  | shellFingerprint => some ``ExactWord.shell_fingerprint
  | entropyInequality => some ``entropy_inequality
  | entropyInversion => some ``entropy_inversion
  | repairedRecurrence => some ``repaired_recurrence
  | internalMultiples => some ``Word.card_internalMultiples_ge
  | guardPattern => some ``Word.guard_at_internal_qstar
  | disjointGuards => some ``many_disjoint_guards
  | carrierReserve => some ``Word.carrier_reserve
  | carrierOverlap => some ``Word.carrier_overlap_le_four
  | carrierUnion => some ``ExactWord.carrier_union_lower
  | highShellTrivial => some ``highShell_trivial
  | providerHighShell => some ``HighShellExtinction
  | highShellEmptyRow => some ``highShell_some_empty_row
  | intermediateScales => some ``IntermediateScaleControl287
  | nearbyTransition => some ``NearbyTransition287
  | polylogWindowFirewall => some ``polylog_window_not_excluded
  | proximity => some ``Proximity287
  | crossScaleSync => some ``CrossScaleSynchronization287
  | finiteExclusion => some ``FiniteExclusionBelow
  | tailClosure => some ``tail_closure_of_crossScale
  | erdos287ConditionalOnSync => some ``erdos287_of_crossScale_and_finite
  | erdos287 => none

/-- Direct dependencies. -/
def deps : Node → List Node
  | exactWordModel => []
  | counterexampleEquiv => [exactWordModel]
  | surrogateSeparation => [exactWordModel, fixedDepthNotExact]
  | minorRelation => []
  | minorDenominator => [minorRelation]
  | fixedDepthCompression => [minorDenominator]
  | fixedDepthNotExact => [fixedDepthCompression]
  | integerDetIntegral => []
  | minorRouteClosure => [fixedDepthCompression, fixedDepthNotExact]
  | topLayerTwo => [exactWordModel]
  | singletonRejection => [topLayerTwo]
  | conditionedRowRejection => [topLayerTwo]
  | positionalChain => [exactWordModel, singletonRejection]
  | qTwoLeD => [topLayerTwo]
  | providerFixedSupply => []
  | providerUniformSupply => []
  | fixedModulusSaturation => [providerFixedSupply, positionalChain]
  | fixedBaseGrowth => [fixedModulusSaturation]
  | uniformModulusSaturation => [providerUniformSupply, positionalChain]
  | growingBaseGrowth => [uniformModulusSaturation]
  | maximalCarrierUniform => [growingBaseGrowth, topLayerTwo]
  | endpointCRT => [exactWordModel]
  | qPairBound => [endpointCRT]
  | smallCeilingUnique => [qPairBound]
  | lowStartChamber => [endpointCRT]
  | dyadicSaturation => [endpointCRT, singletonRejection]
  | ceilingAnnulus => [qPairBound]
  | ownerDisjoint => [exactWordModel]
  | roughPartAggregate => [qPairBound, ownerDisjoint]
  | chebyshevImported => []
  | srecBlockBound => []
  | logSrecBound => [srecBlockBound, chebyshevImported]
  | shellFingerprint => [topLayerTwo]
  | entropyInequality => [shellFingerprint]
  | entropyInversion => []
  | repairedRecurrence => [logSrecBound, entropyInequality, entropyInversion]
  | internalMultiples => [exactWordModel]
  | guardPattern => [positionalChain]
  | disjointGuards => [guardPattern, internalMultiples, repairedRecurrence]
  | carrierReserve => [qPairBound, ceilingAnnulus]
  | carrierOverlap => [carrierReserve]
  | carrierUnion => [carrierOverlap, smallCeilingUnique]
  | highShellTrivial => [singletonRejection]
  | providerHighShell => []
  | highShellEmptyRow => [providerHighShell]
  | intermediateScales => []
  | nearbyTransition => []
  | polylogWindowFirewall => [repairedRecurrence]
  | proximity => []
  | crossScaleSync => []
  | finiteExclusion => []
  | tailClosure => [crossScaleSync, counterexampleEquiv, disjointGuards, shellFingerprint,
      carrierReserve, highShellTrivial]
  | erdos287ConditionalOnSync => [tailClosure, finiteExclusion]
  | erdos287 => [erdos287ConditionalOnSync, proximity, intermediateScales]

/-- Topological rank (dependencies have strictly smaller rank). -/
def rank : Node → ℕ
  | exactWordModel => 0 | minorRelation => 0 | integerDetIntegral => 0
  | providerFixedSupply => 0 | providerUniformSupply => 0 | chebyshevImported => 0
  | srecBlockBound => 0 | entropyInversion => 0 | providerHighShell => 0
  | intermediateScales => 0 | nearbyTransition => 0 | proximity => 0
  | crossScaleSync => 0 | finiteExclusion => 0
  | counterexampleEquiv => 1 | minorDenominator => 1 | topLayerTwo => 1 | endpointCRT => 1
  | ownerDisjoint => 1 | logSrecBound => 1 | internalMultiples => 1 | highShellEmptyRow => 1
  | fixedDepthCompression => 2 | singletonRejection => 2 | conditionedRowRejection => 2
  | qTwoLeD => 2 | qPairBound => 2 | lowStartChamber => 2 | shellFingerprint => 2
  | fixedDepthNotExact => 3 | positionalChain => 3 | smallCeilingUnique => 3
  | dyadicSaturation => 3 | ceilingAnnulus => 3 | roughPartAggregate => 3
  | entropyInequality => 3 | highShellTrivial => 3
  | surrogateSeparation => 4 | minorRouteClosure => 4 | fixedModulusSaturation => 4
  | uniformModulusSaturation => 4 | carrierReserve => 4 | repairedRecurrence => 4
  | guardPattern => 4
  | fixedBaseGrowth => 5 | growingBaseGrowth => 5 | carrierOverlap => 5
  | disjointGuards => 5 | polylogWindowFirewall => 5
  | maximalCarrierUniform => 6 | carrierUnion => 6 | tailClosure => 6
  | erdos287ConditionalOnSync => 7
  | erdos287 => 8

theorem dag_acyclic : ∀ n : Node, ∀ m ∈ deps n, rank m < rank n := by decide

theorem dag_max_rank : ∀ n : Node, rank n ≤ 8 := by decide

/-- Nodes reachable from `n` by following dependency edges, within `k` steps.  Since every
edge decreases the rank and ranks are `≤ 8`, `supportWithin 9 n` is the full transitive
support of `n`. -/
def supportWithin : ℕ → Node → List Node
  | 0, n => [n]
  | k + 1, n => n :: (deps n).flatMap (supportWithin k)

/-- The transitive support of a node. -/
def support (n : Node) : List Node := supportWithin 9 n

theorem dag_exact_closed :
    ∀ n : Node, status n = bankedExact → ∀ m ∈ deps n, status m = bankedExact := by decide

/-- The transitive support of a banked-exact node contains only banked-exact nodes. -/
theorem dag_exact_support :
    ∀ n : Node, status n = bankedExact → ∀ m ∈ support n, status m = bankedExact := by decide

/-- Every conditional node transitively depends on an open node (its provider). -/
theorem dag_conditional_has_open :
    ∀ n : Node, status n = conditional → ∃ m ∈ support n, status m = .open := by decide

/-- No non-retired node depends directly on a retired node. -/
theorem dag_no_retired_edge :
    ∀ n : Node, status n ≠ retired → ∀ m ∈ deps n, status m ≠ retired := by decide

theorem supportWithin_not_retired (k : ℕ) :
    ∀ n : Node, status n ≠ retired → ∀ m ∈ supportWithin k n, status m ≠ retired := by
  induction k with
  | zero => intro n hn m hm; simp [supportWithin] at hm; subst hm; exact hn
  | succ k ih =>
    intro n hn m hm
    simp only [supportWithin, List.mem_cons, List.mem_flatMap] at hm
    rcases hm with rfl | ⟨j, hj, hmj⟩
    · exact hn
    · exact ih j (dag_no_retired_edge n hn j hj) m hmj

/-- No banked-exact or conditional node transitively uses a retired node. -/
theorem dag_no_retired_use :
    ∀ n : Node, (status n = bankedExact ∨ status n = conditional) →
      ∀ m ∈ support n, status m ≠ retired := by
  intro n hn
  apply supportWithin_not_retired
  rcases hn with h | h <;> rw [h] <;> decide

theorem dag_erdos287_open : status erdos287 = .open := rfl

theorem dag_erdos287_no_decl : decl erdos287 = none := rfl

/-- Every direct route into the Erdős #287 node is open or conditional — none is banked
exact. -/
theorem dag_erdos287_inputs_not_exact :
    ∀ m ∈ deps erdos287, status m ≠ bankedExact := by decide

/-- The open frontier nodes in the support of the Erdős #287 node. -/
theorem dag_erdos287_open_support :
    (support erdos287).filter (fun n => status n == .open) =
      [erdos287, crossScaleSync, finiteExclusion, proximity, intermediateScales] := by decide

/-- Every banked-exact or conditional node has a backing Lean declaration. -/
theorem dag_proved_have_decls :
    ∀ n : Node, (status n = bankedExact ∨ status n = conditional) → (decl n).isSome := by
  decide

end Erdos287.PostV71V87.DAG
