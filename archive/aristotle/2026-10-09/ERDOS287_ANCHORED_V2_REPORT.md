# Erdős #287 — Anchored V2 formal run (report)

**Erdős #287 is OPEN and is NOT claimed here.**  This run is append-only: Route S, Route D and
Anchored V1 are untouched, the certified finite frontier is unchanged and is not extended, and
no new asymptotic or analytic statement is asserted.

## PREVIOUS BANK

Preserved verbatim.  Route S (ten-node cut, countermodels), Route D (direct reciprocal core,
compiler equivalences, raw-mask arithmetic, boundary kernel, LCM/carry algebra, path polynomial,
finite Fourier, sparse subreservoir, protected switches, absorber interfaces,
`ExactSignedAbsorber` OPEN, hostile countermodels, cross-route bridges) and Anchored V1
(reciprocal state, allowed subsets, valuation criterion, fingerprint, prime-power layer, contact
relation, exact contact decision, leaf elimination, forest decision, isolated-cycle decision,
path transfer, cyclomatic infrastructure, leafless kernel reduction, `anchored_contact_endpoint`,
OPEN global branching rejection, excess-2 abstract firewall) are re-checked unchanged in
`RequestProject/Erdos287/AnchoredV2/Reconciliation.lean`.

Certified finite frontier: `67108856338751594`, U2 pending.  **Unchanged; not extended.**

## FILES ADDED

All under `RequestProject/Erdos287/AnchoredV2/` plus the aggregator
`RequestProject/Erdos287/AnchoredV2.lean`:

`FeedbackEdge.lean`, `BlockCut.lean`, `CactusMessage.lean`, `AffineNormalForm.lean`,
`ThetaFirewall.lean`, `TrackedKernel.lean`, `UnitSubsetSum.lean`, `CoupledCharge.lean`,
`CoupledBatchSupply.lean`, `FiniteExtension.lean`, `Capacity.lean`, `CapacityCertificate.lean`,
`CapacityGap.lean`, `Level2.lean`, `RouteBridge.lean`, `Reconciliation.lean`, `AxiomAudit.lean`.

## FILES MODIFIED

`RequestProject/Main.lean` — one added import (`RequestProject.Erdos287.AnchoredV2`).  No other
existing file was modified.

## LAKE BUILD

`lake build` succeeds: **8548 jobs**, no errors, no warnings in the new namespace.

## AXIOM AUDIT

`RequestProject/Erdos287/AnchoredV2/AxiomAudit.lean` runs `#print axioms` on all 40 principal
exported theorems.  Every one reports only `propext`, `Classical.choice`, `Quot.sound` (several
report fewer; `v2_routes_preserved` reports none).  Source scan of the new namespace: no `sorry`,
no `admit`, no custom `axiom`, no `native_decide`, no `unsafe`, no `opaque`, no
`@[implemented_by]`.

## FEEDBACK-EDGE THEOREM

`sat_iff_exists_branch` — KERNEL-PROVED.  For a supplied feedback set `F ⊆ Edges` whose edges
carry the contact (OR) relation, `I.Sat ↔ ∃ S ⊆ F, (branch I F S).Sat`, where `branch I F S`
pins the `S`-chosen endpoint of every feedback edge to *selected* and deletes that edge.  Both
directions.  Branch solution sets may overlap; this is not a disjoint counting identity.

## 2^BETA

`branch_count`: `F.powerset.card = 2 ^ F.card`.  `feedbackSet_card`: with a supplied spanning
forest `T` of `c` components (`|T| + c = |V|`), `|F| = |E| − |V| + c = β`.
`anchored_forest_branches` packages: exact reduction, `2 ^ β` branches, and each branch instance
has edge set exactly the supplied forest `T`.  **No claim that β is uniformly bounded.**

## BETA=2

`beta_two_four_tests` — KERNEL-PROVED: `β = 2` gives an exact decision by at most **four**
complete anchored forest tests.  No infeasibility is derived.

## CACTUS

`SplitAt` (certified block-cut data) + `sat_split_iff` — KERNEL-PROVED, both directions, at a
certified articulation set; `sat_split_single_iff` at one articulation position.
`CactusData` + `cactus_star_sat_iff` — KERNEL-PROVED exact decision for a certified star of
children meeting pairwise only in the articulation: satisfiable iff all children admit a common
Boolean value there.  `msg2_pathChild` identifies a path child's two-contact message with the
Anchored V1 transfer.  Contacts that refer to the same physical position are literally the same
Boolean variable, and the full local relation (each child's unary domains) is retained.

## AFFINE NORMAL FORM

`AffineTreeData` (certified `α, β` data along a supplied spanning tree), `famLabel`,
`famLabel_satisfiesTree`, `eq_famLabel_of_satisfiesTree` (uniqueness given the root value),
`nonTree_iff`, `nonTree_dichotomy` (genuine affine equation with a unique root value / no root
value / identity), `FullyBalanced`, `fullyBalanced_one_parameter` (one-parameter affine family),
`modulus` (lcm of the denominators of the `α_v`), `modulus_pos`, `integral_root_progression`
(all integral root values lie in `x₀ + modulus·ℤ`) and `integral_progression_sound` (the
converse inclusion).  All KERNEL-PROVED.  No label is claimed prime or a prime power.

## THETA FIREWALL

`thetaBalancedRejection_false` — KERNEL-PROVED.  The explicit abstract theta instance
(`thetaCSP`, excess 2, leafless, satisfiable) with fully balanced affine transfer data
(`thetaAffine`, certified and `FullyBalanced`) and locally feasible relations refutes the
unconditional rejection `ThetaBalancedRejection`.  **Not a #287 survivor**; an abstract logical
firewall only.

## TRACKED KERNEL

`TrackedPrimeKernel` (retained positions, shared-position equalities, endpoint pins, forced
zeros, no-`00` adjacency, inherited high-power equations, one truncated prime-power equation per
tracked prime), `Satisfies`, `Feasible`, `Localised`, and the contact relaxation `contact`.

## KERNEL MONOTONICITY

`feasible_of_refines` — KERNEL-PROVED: if `K'` tracks at least `K`'s primes with the same
equations and carries all of `K`'s other constraints, then `K'` feasible ⟹ `K` feasible.  No
cardinality or asymptotic claim.

## COUPLED-BATCH SUPPLY

`CoupledBatchSupply K p e` — a purely finite record: site count with `2^e p − 1 ≤ n`, injective
fresh site positions, left/right neighbours with proofs they are pinned and retained, proofs no
two sites are adjacent, proofs the inherited high-power and truncated prime-power equations
depend only on retained positions, and unit charges modulo `2^e` and modulo `p`.  No asymptotic
existence occurs inside the record.

## UNIT-LIST SUBSET-SUM

`exists_subset_sum_eq` — KERNEL-PROVED: for `m ≥ 2` and any family of at least `m − 1` units of
`ZMod m` (repetitions allowed), every residue is a subset sum.  Proved exactly by the intended
route: `eq_univ_of_add_unit_invariant` (a nonempty translation-invariant set under a unit is
everything) and `card_union_image_add_lt` (each step grows the attainable set).

## COUPLED CHARGE

`coprime_two_pow_prime`, `coupledCharge` (CRT preimage), `isUnit_coupledCharge`, and
`coupled_subset_sum` — KERNEL-PROVED: with enough sites carrying unit charges mod `2^e` and mod
an odd prime `p`, some subset has total charge `0 (mod 2^e)` and any prescribed `t (mod p)`.

## FINITE EXTENSION

`finite_coupled_extension` — KERNEL-PROVED: a localised feasible tracked kernel plus an explicit
`CoupledBatchSupply` extends to a full physical word which agrees with the kernel witness on all
retained positions, satisfies every retained constraint (pins, zeros, shared equalities,
no-`00` adjacency, inherited high-power equations, all tracked prime components), selects
exactly the chosen batch of repair sites with their neighbour adjacency conditions satisfied,
and realises the prescribed coupled charge.  Entirely finite.

## FULL/RESTRICTION EQUIVALENCE

`feasible_of_fullTrackedSolution` (literal restriction) and `fullTrackedSolution_iff_feasible`
(finite equivalence *under supply*) — KERNEL-PROVED.

## CAPACITY FUNCTION

`PortSystem` (blocks, contact edges with endpoint blocks, complete finite local relations),
`Feasible`, and `cap S λ v = max_{B ∈ L v} ∑_{e ∈ B} λ e` via `Finset.sup'`, defined as `0` when
the local relation is empty (`cap_of_empty`).

## CAPACITY MONOTONICITY

`cap_mono` — KERNEL-PROVED: `L'_v ⊆ L_v` ⟹ `C'_v(λ) ≤ C_v(λ)` for `λ ≥ 0`.  `slack_mono`:
relation shrinkage cannot increase the normalised slack.

## NEGATIVE CAPACITY CERTIFICATE

`capacity_sound` — KERNEL-PROVED: feasibility implies `∑_e λ_e ≤ ∑_v C_v(λ)` for every
nonnegative weighting (elementary; no LP duality, no converse).  `slack`,
`not_feasible_of_slack_neg`, `not_feasible_of_capacity_lt`, the finite record
`NegativeCapacityCertificate` and `NegativeCapacityCertificate.not_feasible` — all
KERNEL-PROVED.

## ACTUAL ANCHORED BRIDGE

`portOfContact` turns any anchored contact instance (in particular any leafless branching kernel
produced by V1 peeling) into a port system with its complete local relations, capacity data and
Level-2 data.  `feasible_of_sat`, `negativeCapacity_rejects_anchored`, `level2_rejects_anchored`
— KERNEL-PROVED — reject the *actual* anchored kernel.  Tracked-kernel versions:
`negativeCapacity_rejects_trackedKernel`, `level2_rejects_trackedKernel`.  Neither certificate
is claimed to exist for any particular kernel.

## CAPACITY GAP FIREWALL

`gapSystem` (two blocks, four ports, left `{{0,1},{2,3}}`, right `{{0,2},{1,3}}`):
`gap_not_feasible` (no integral pair covers all four edges), `gap_no_negativeCapacityCertificate`
(*no* nonnegative weighting has negative slack — the Level-1 test never rejects it),
`gap_fractional_mixture` (the 50/50 mixture on each side has expected coverage `1` on every
edge), packaged as `capacity_incompleteness`.  All KERNEL-PROVED.  Nothing is asserted about
actual arithmetic kernels from this abstract example.

## LEVEL-2 FRACTIONAL

`margAt`, `Incident`, `Level2FractionalFeasible`: finite nonnegative rational weights on
admissible covering pairs, total mass one per edge, consistent one-block marginals across all
incident edges.  No general LP library was built.

## LEVEL-2 SOUNDNESS

`level2_of_feasible` and `not_feasible_of_not_level2` — KERNEL-PROVED.  Converse **not** claimed.

## FOREST LEVEL-2 EXACTNESS

**Not attempted** (declared stretch goal).  Recorded as the open node `forestLevel2` in the
Anchored V2 ledger.

## FIXED-POWER SUPPLY STATUS

`FixedPowerCoupledSupply M R p e` is defined as an ordinary proposition and
`coupledBatchSupply_of_fixedPower` is proved from it.  It is **uninhabited**: no analytic
Jacobsthal/Bertrand input is formalised, and no axiom is introduced.  Nothing about `R = M^ρ`,
`ρ < 1/6` is asserted in Lean.

## NEW OPEN OWNERS

* `UniformNegativeCapacity (Arises)` — every arising leafless kernel of excess ≥ 2 admits a
  negative capacity certificate.  OPEN, uninhabited.
* `UniformLevel2Rejection (Arises)` — every such kernel is Level-2 fractionally infeasible.
  OPEN, uninhabited.
* `FixedPowerCoupledSupply M R p e` — OPEN, uninhabited.
* `forestLevel2` — stretch goal, OPEN.

`v1_owner_refined` proves `UniformNegativeCapacity → BranchingKernelRejection` and
`UniformLevel2Rejection → BranchingKernelRejection` (for kernels with contact (OR) relations).
The Anchored V1 global branching owner is **kept**, refined rather than deleted; its
unconditional form remains refuted.

## ROUTE-S STATUS

Unchanged; cut nodes still open (`v2_routes_preserved`).

## ROUTE-D STATUS

Unchanged; `ExactSignedAbsorber` and the direct cut still open (`v2_routes_preserved`).

## ANCHORED-V1 STATUS

Preserved; `BranchingKernelRejection` still OPEN, now refined by two explicit certificate
owners.

## ANCHORED-V2 STATUS

New.  Thirteen kernel-proved nodes; four open nodes (`uniformNegativeCapacity`,
`uniformLevel2Rejection`, `fixedPowerSupply`, `forestLevel2`) plus `erdos287`.

## FINITE FRONTIER

`67108856338751594` — unchanged and **not** extended (`v2_finite_frontier_unchanged`).

## U2 STATUS

Pending external import; unchanged.

## ERDŐS #287 STATUS

**OPEN.**  Not proved, not disproved, not claimed.

## MINIMUM FORMAL OPEN CUT

`{ UniformNegativeCapacity ∨ UniformLevel2Rejection (either suffices for the V1 branching owner),
   FixedPowerCoupledSupply (for the large-cutoff supply),
   Route-S cut, Route-D ExactSignedAbsorber, U2 import }`.

## NEXT ARISTOTLE TARGET

Forest Level-2 exactness (`Level2FractionalFeasible → Feasible` on forest contact graphs,
agreeing with the V1 leaf solver), and the search for a *concrete* negative capacity or Level-2
certificate on an explicitly arising anchored kernel family.
