import RequestProject.Erdos287.PostV87V90R.RegressionSuite

/-!
# Erdős #287 (post-V87 → V90R) — machine-checked closure DAG

Every node carries a status

* `exact` — kernel-proved here with no provider hypothesis;
* `conditional` — kernel-proved here from an explicit, never-constructed provider;
* `externalBank` — imported, previously kernel-checked material (the audited `PostV71V87`
  bank, Mathlib's Cauchy–Schwarz);
* `open` — an explicit provider interface or an unformalised claim;
* `retired` — a former closing route / owner shown insufficient or overstrong (KILL);

the Lean declaration it refers to (double-backtick literals, so renaming breaks the build) and
its direct dependencies.  Checked by `decide` (kernel reduction, no `native_decide`):

* `dag_acyclic` — every edge strictly decreases the rank;
* `dag_exact_closed` / `dag_exact_support` — exact nodes depend only on exact or external-bank
  nodes;
* `dag_conditional_has_open` — every conditional node traces to an open input;
* `dag_no_retired_use` — no exact or conditional node has a retired node in its support;
* `dag_erdos287_open`, `dag_erdos287_no_decl`, `dag_erdos287_open_support` — global #287 is
  OPEN, with no declaration claiming it, and its open inputs are exactly the W3 provider, the
  compiler existence, the narrow-width owner and the finite splice;
* `dag_crossScale_retired`, `dag_narrow_is_owner` — the cross-scale owner is retired and the
  current owner is the narrow-width closure.

The "no theorem name overstates its assumptions" check is a meta-level check in
`AxiomAudit.lean` (`#assert_conditional` / `#assert_unconditional`).
-/

namespace Erdos287.PostV87V90R.DAG

/-- Node status. -/
inductive Status
  | exact
  | conditional
  | externalBank
  | open
  | retired
  deriving DecidableEq, Repr

/-- Nodes. -/
inductive Node
  -- external banks
  | postV71V87Bank
  | mathlibCauchy
  -- model
  | modelCompat
  | harmonicWidth
  -- V88 retained exact facts
  | v88Replication
  | v88GuardOwner
  | v88LcmTransfer
  | v88Capacity
  | v88SingleGrid
  | v88EvenMultigrid
  -- closure-first failure fixtures
  | exteriorFixture
  | proximityFixture
  | crossScaleEquiv
  -- retired consumer architectures / owners
  | retiredSingleGridOverload
  | retiredMultiGridOverload
  | retiredExteriorCombination
  | retiredProximityContact
  | retiredCrossScaleOwner
  | retiredC116Threshold
  | retiredFixedDepthMinor
  -- V90 geometry
  | v90Cyclic
  | g112Alpha
  | g112Decide
  | widthRatio
  | annulusBarrier
  -- repaired moment consumer
  | momentCauchy
  | momentOccupancy
  | cNormalization
  | c113
  | balancing
  | sharpMean
  -- compiler
  | affineAdjacency
  | compilerExistence
  -- row rigidity
  | rowRigidity
  | adjacentRows
  -- consumers
  | occupancyContact
  | momentContact
  -- analytic / owners / conditional conclusions
  | widthThreeProvider
  | w3
  | w3Family
  | narrowOwner
  | e287Provider
  | e287
  | tailW3Narrow
  | tailE287
  | finiteExclusion
  | globalSplice
  | erdos287

open Node Status

/-- Node index (used to decide equality without a quadratic derived instance). -/
def Node.idx : Node → ℕ
  | .postV71V87Bank => 0
  | .mathlibCauchy => 1
  | .modelCompat => 2
  | .harmonicWidth => 3
  | .v88Replication => 4
  | .v88GuardOwner => 5
  | .v88LcmTransfer => 6
  | .v88Capacity => 7
  | .v88SingleGrid => 8
  | .v88EvenMultigrid => 9
  | .exteriorFixture => 10
  | .proximityFixture => 11
  | .crossScaleEquiv => 12
  | .retiredSingleGridOverload => 13
  | .retiredMultiGridOverload => 14
  | .retiredExteriorCombination => 15
  | .retiredProximityContact => 16
  | .retiredCrossScaleOwner => 17
  | .retiredC116Threshold => 18
  | .retiredFixedDepthMinor => 19
  | .v90Cyclic => 20
  | .g112Alpha => 21
  | .g112Decide => 22
  | .widthRatio => 23
  | .annulusBarrier => 24
  | .momentCauchy => 25
  | .momentOccupancy => 26
  | .cNormalization => 27
  | .c113 => 28
  | .balancing => 29
  | .sharpMean => 30
  | .affineAdjacency => 31
  | .compilerExistence => 32
  | .rowRigidity => 33
  | .adjacentRows => 34
  | .occupancyContact => 35
  | .momentContact => 36
  | .widthThreeProvider => 37
  | .w3 => 38
  | .w3Family => 39
  | .narrowOwner => 40
  | .e287Provider => 41
  | .e287 => 42
  | .tailW3Narrow => 43
  | .tailE287 => 44
  | .finiteExclusion => 45
  | .globalSplice => 46
  | .erdos287 => 47

/-- Inverse of `Node.idx`. -/
def Node.ofIdx : ℕ → Node
  | 0 => .postV71V87Bank
  | 1 => .mathlibCauchy
  | 2 => .modelCompat
  | 3 => .harmonicWidth
  | 4 => .v88Replication
  | 5 => .v88GuardOwner
  | 6 => .v88LcmTransfer
  | 7 => .v88Capacity
  | 8 => .v88SingleGrid
  | 9 => .v88EvenMultigrid
  | 10 => .exteriorFixture
  | 11 => .proximityFixture
  | 12 => .crossScaleEquiv
  | 13 => .retiredSingleGridOverload
  | 14 => .retiredMultiGridOverload
  | 15 => .retiredExteriorCombination
  | 16 => .retiredProximityContact
  | 17 => .retiredCrossScaleOwner
  | 18 => .retiredC116Threshold
  | 19 => .retiredFixedDepthMinor
  | 20 => .v90Cyclic
  | 21 => .g112Alpha
  | 22 => .g112Decide
  | 23 => .widthRatio
  | 24 => .annulusBarrier
  | 25 => .momentCauchy
  | 26 => .momentOccupancy
  | 27 => .cNormalization
  | 28 => .c113
  | 29 => .balancing
  | 30 => .sharpMean
  | 31 => .affineAdjacency
  | 32 => .compilerExistence
  | 33 => .rowRigidity
  | 34 => .adjacentRows
  | 35 => .occupancyContact
  | 36 => .momentContact
  | 37 => .widthThreeProvider
  | 38 => .w3
  | 39 => .w3Family
  | 40 => .narrowOwner
  | 41 => .e287Provider
  | 42 => .e287
  | 43 => .tailW3Narrow
  | 44 => .tailE287
  | 45 => .finiteExclusion
  | 46 => .globalSplice
  | 47 => .erdos287
  | _ => .erdos287

theorem Node.ofIdx_idx (n : Node) : Node.ofIdx n.idx = n := by cases n <;> rfl

theorem Node.idx_inj {a b : Node} (h : a.idx = b.idx) : a = b := by
  rw [← Node.ofIdx_idx a, ← Node.ofIdx_idx b, h]

instance : DecidableEq Node := fun a b =>
  decidable_of_iff (a.idx = b.idx) ⟨Node.idx_inj, fun h => h ▸ rfl⟩



/-- The list of all nodes (completeness: `mem_allNodes`). -/
def allNodes : List Node :=
  [postV71V87Bank, mathlibCauchy, modelCompat, harmonicWidth, v88Replication,
   v88GuardOwner, v88LcmTransfer, v88Capacity, v88SingleGrid, v88EvenMultigrid,
   exteriorFixture, proximityFixture, crossScaleEquiv, retiredSingleGridOverload, retiredMultiGridOverload,
   retiredExteriorCombination, retiredProximityContact, retiredCrossScaleOwner, retiredC116Threshold, retiredFixedDepthMinor,
   v90Cyclic, g112Alpha, g112Decide, widthRatio, annulusBarrier,
   momentCauchy, momentOccupancy, cNormalization, c113, balancing,
   sharpMean, affineAdjacency, compilerExistence, rowRigidity, adjacentRows,
   occupancyContact, momentContact, widthThreeProvider, w3, w3Family,
   narrowOwner, e287Provider, e287, tailW3Narrow, tailE287,
   finiteExclusion, globalSplice, erdos287]

theorem mem_allNodes (n : Node) : n ∈ allNodes := by cases n <;> decide

theorem allNodes_card : allNodes.length = 48 := rfl

/-- Status assignment. -/
def status : Node → Status
  | postV71V87Bank | mathlibCauchy => externalBank
  | modelCompat | harmonicWidth => exact
  | v88Replication | v88GuardOwner | v88LcmTransfer | v88Capacity | v88SingleGrid
  | v88EvenMultigrid => exact
  | exteriorFixture | proximityFixture | crossScaleEquiv => exact
  | retiredSingleGridOverload | retiredMultiGridOverload | retiredExteriorCombination
  | retiredProximityContact | retiredCrossScaleOwner | retiredC116Threshold
  | retiredFixedDepthMinor => retired
  | v90Cyclic | g112Alpha | g112Decide | widthRatio => exact
  | annulusBarrier => .open
  | momentCauchy | momentOccupancy | cNormalization | c113 | balancing | sharpMean => exact
  | affineAdjacency => exact
  | compilerExistence => .open
  | rowRigidity | adjacentRows => exact
  | occupancyContact | momentContact => exact
  | widthThreeProvider => .open
  | w3 | w3Family => conditional
  | narrowOwner => .open
  | e287Provider => .open
  | e287 => conditional
  | tailW3Narrow | tailE287 => conditional
  | finiteExclusion => .open
  | globalSplice => conditional
  | erdos287 => .open

/-- Backing Lean declaration (`none` = no formal statement). -/
def decl : Node → Option Lean.Name
  | postV71V87Bank => some ``Erdos287.PostV71V87.ExactWord
  | mathlibCauchy => some ``Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  | modelCompat => some ``counterexample_iff_exactWord
  | harmonicWidth => some ``ExactWord.exp_upper
  | v88Replication => some ``primePower_replication
  | v88GuardOwner => some ``guardOwner_unique
  | v88LcmTransfer => some ``lcm_transfer
  | v88Capacity => some ``isolated_omissions_realizable
  | v88SingleGrid => some ``single_grid_realizable
  | v88EvenMultigrid => some ``even_multigrid_realizable
  | exteriorFixture => some ``exterior_obligations_do_not_combine
  | proximityFixture => some ``proximity_density_no_contact
  | crossScaleEquiv => some ``crossScale_retired_equiv_tail
  | retiredSingleGridOverload => none
  | retiredMultiGridOverload => none
  | retiredExteriorCombination => none
  | retiredProximityContact => none
  | retiredCrossScaleOwner => some ``Erdos287.PostV71V87.CrossScaleSynchronization287
  | retiredC116Threshold => none
  | retiredFixedDepthMinor => none
  | v90Cyclic => some ``alpha_contactCycle
  | g112Alpha => some ``alpha_G_11_2
  | g112Decide => some ``G_11_2_four_subsets_have_edge
  | widthRatio => some ``widthParam_spec
  | annulusBarrier => some ``AnnulusBarrier287
  | momentCauchy => some ``moment_cauchy
  | momentOccupancy => some ``exists_occupancy_of_moment
  | cNormalization => some ``occupancy_of_normalized_moments
  | c113 => some ``occupancy_11_3
  | balancing => some ``qbal_le_pairs
  | sharpMean => some ``sharp_mean_consumer
  | affineAdjacency => some ``affine_adjacency
  | compilerExistence => some ``AffineContactCompiler
  | rowRigidity => some ``selRow_empty_of_bounded_cofactors
  | adjacentRows => some ``adjacent_empty_rows_contradiction
  | occupancyContact => some ``occupancy_contact_false
  | momentContact => some ``moment_contact_false
  | widthThreeProvider => some ``WidthThreeMomentProvider
  | w3 => some ``W3_of_provider
  | w3Family => some ``W3_family_of_providers
  | narrowOwner => some ``NarrowWidthClosureProvider
  | e287Provider => some ``E287_11_4_Provider
  | e287 => some ``E287_11_4
  | tailW3Narrow => some ``tail_of_W3_narrow
  | tailE287 => some ``tail_of_E287_11_4
  | finiteExclusion => some ``Erdos287.PostV71V87.FiniteExclusionBelow
  | globalSplice => some ``erdos287_of_W3_narrow_finite
  | erdos287 => none

/-- Direct dependencies. -/
def deps : Node → List Node
  | postV71V87Bank => []
  | mathlibCauchy => []
  | modelCompat => [postV71V87Bank]
  | harmonicWidth => [postV71V87Bank]
  | v88Replication => [postV71V87Bank]
  | v88GuardOwner => [postV71V87Bank]
  | v88LcmTransfer => [postV71V87Bank]
  | v88Capacity => [postV71V87Bank]
  | v88SingleGrid => [v88Capacity]
  | v88EvenMultigrid => [v88Capacity]
  | exteriorFixture => []
  | proximityFixture => []
  | crossScaleEquiv => [postV71V87Bank]
  | retiredSingleGridOverload => [v88SingleGrid]
  | retiredMultiGridOverload => [v88EvenMultigrid]
  | retiredExteriorCombination => [exteriorFixture]
  | retiredProximityContact => [proximityFixture]
  | retiredCrossScaleOwner => [crossScaleEquiv]
  | retiredC116Threshold => [c113]
  | retiredFixedDepthMinor => [postV71V87Bank]
  | v90Cyclic => []
  | g112Alpha => [v90Cyclic]
  | g112Decide => []
  | widthRatio => []
  | annulusBarrier => []
  | momentCauchy => [mathlibCauchy]
  | momentOccupancy => [momentCauchy]
  | cNormalization => [momentOccupancy]
  | c113 => [cNormalization]
  | balancing => []
  | sharpMean => [balancing]
  | affineAdjacency => []
  | compilerExistence => [affineAdjacency]
  | rowRigidity => [postV71V87Bank]
  | adjacentRows => [rowRigidity]
  | occupancyContact => [v90Cyclic, affineAdjacency, adjacentRows]
  | momentContact => [occupancyContact, cNormalization, sharpMean]
  | widthThreeProvider => [compilerExistence, widthRatio]
  | w3 => [widthThreeProvider, momentContact, harmonicWidth, modelCompat]
  | w3Family => [w3]
  | narrowOwner => [harmonicWidth]
  | e287Provider => [compilerExistence]
  | e287 => [e287Provider, g112Alpha, occupancyContact]
  | tailW3Narrow => [w3, narrowOwner]
  | tailE287 => [w3, e287]
  | finiteExclusion => []
  | globalSplice => [tailW3Narrow, finiteExclusion]
  | erdos287 => [globalSplice, tailE287]

/-- Topological rank. -/
def rank : Node → ℕ
  | postV71V87Bank => 0 | mathlibCauchy => 0 | exteriorFixture => 0 | proximityFixture => 0
  | v90Cyclic => 0 | g112Decide => 0 | widthRatio => 0 | annulusBarrier => 0 | balancing => 0
  | affineAdjacency => 0 | finiteExclusion => 0
  | modelCompat => 1 | harmonicWidth => 1 | v88Replication => 1 | v88GuardOwner => 1
  | v88LcmTransfer => 1 | v88Capacity => 1 | crossScaleEquiv => 1 | retiredFixedDepthMinor => 1
  | retiredExteriorCombination => 1 | retiredProximityContact => 1 | g112Alpha => 1
  | momentCauchy => 1 | sharpMean => 1 | compilerExistence => 1 | rowRigidity => 1
  | v88SingleGrid => 2 | v88EvenMultigrid => 2 | retiredCrossScaleOwner => 2
  | momentOccupancy => 2 | adjacentRows => 2 | widthThreeProvider => 2 | narrowOwner => 2
  | e287Provider => 2
  | retiredSingleGridOverload => 3 | retiredMultiGridOverload => 3 | cNormalization => 3
  | occupancyContact => 3
  | c113 => 4 | momentContact => 4 | e287 => 4
  | retiredC116Threshold => 5 | w3 => 5
  | w3Family => 6 | tailW3Narrow => 6 | tailE287 => 6
  | globalSplice => 7
  | erdos287 => 8

theorem dag_acyclic : ∀ n ∈ allNodes, ∀ m ∈ deps n, rank m < rank n := by decide

theorem dag_max_rank : ∀ n ∈ allNodes, rank n ≤ 8 := by decide

/-- Nodes reachable within `k` dependency steps. -/
def supportWithin : ℕ → Node → List Node
  | 0, n => [n]
  | k + 1, n => (n :: (deps n).flatMap (supportWithin k)).dedup

/-- Full transitive support (ranks are `≤ 8`). -/
def support (n : Node) : List Node := supportWithin 9 n

/-- Exact nodes depend directly only on exact or external-bank nodes. -/
theorem dag_exact_closed :
    ∀ n ∈ allNodes, status n = exact → ∀ m ∈ deps n, status m = exact ∨ status m = externalBank := by
  decide

/-- The transitive support of an exact node is exact or external bank. -/
theorem dag_exact_support :
    ∀ n ∈ allNodes, status n = exact → ∀ m ∈ support n, status m = exact ∨ status m = externalBank := by
  decide

/-- Every conditional node transitively depends on an open node. -/
theorem dag_conditional_has_open :
    ∀ n ∈ allNodes, status n = conditional → ∃ m ∈ support n, status m = .open := by decide

/-- No exact or conditional node has a retired node in its support. -/
theorem dag_no_retired_use :
    ∀ n ∈ allNodes, (status n = exact ∨ status n = conditional) →
      ∀ m ∈ support n, status m ≠ retired := by decide

theorem dag_erdos287_open : status erdos287 = .open := rfl

theorem dag_erdos287_no_decl : decl erdos287 = none := rfl

/-- No direct input of the #287 node is exact. -/
theorem dag_erdos287_inputs_not_exact : ∀ m ∈ deps erdos287, status m ≠ exact := by decide

/-- The open inputs in the support of global #287. -/
theorem dag_erdos287_open_support :
    (∀ n ∈ support erdos287, status n = .open →
      n ∈ [erdos287, widthThreeProvider, compilerExistence, narrowOwner, finiteExclusion,
        e287Provider]) ∧
    (∀ n ∈ [erdos287, widthThreeProvider, compilerExistence, narrowOwner, finiteExclusion,
        e287Provider], n ∈ support erdos287 ∧ status n = .open) := by decide

/-- Global #287 depends on both the narrow-width owner and the finite splice, both open. -/
theorem dag_global_needs_narrow_and_finite :
    narrowOwner ∈ support erdos287 ∧ finiteExclusion ∈ support erdos287 ∧
      status narrowOwner = .open ∧ status finiteExclusion = .open := by decide

/-- The cross-scale owner is retired; the narrow-width closure is the current open owner. -/
theorem dag_crossScale_retired : status retiredCrossScaleOwner = retired := rfl

theorem dag_narrow_is_owner :
    status narrowOwner = .open ∧ retiredCrossScaleOwner ∉ support erdos287 := by decide

/-- The obsolete `C < 11/6` node is retired and unused. -/
theorem dag_c116_unused : ∀ n ∈ allNodes, retiredC116Threshold ∈ deps n → status n = retired := by
  decide

/-- Every exact or conditional node has a backing declaration. -/
theorem dag_proved_have_decls :
    ∀ n ∈ allNodes, (status n = exact ∨ status n = conditional) → (decl n).isSome := by decide

end Erdos287.PostV87V90R.DAG
