# ERDŐS #287 — MASTER-SOURCE FRONTIER SAFE BANK REPORT

Append-only pass reflecting the newest source-census hostile audit.
Nothing was deleted, renamed, weakened or relocated.  The only modification to an existing
file is **ten appended `import` lines** at the end of the import block of
`RequestProject/Main.lean`.

Erdős #287 is **not** claimed to be solved.  No `Erdos287ClosureInputs` inhabitant is
constructed.  No theorem named `erdos287` exists in the repository.

---

## 1. FILES ADDED

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287MasterSourceInterface.lean` | finite test model of the unprojected source; `SourceSpec`; `MasterPhysicalSourceRealisation` (uninhabited); `SourceDictionary`; dictionary ≠ realisation firewall |
| `RequestProject/CurrentProgramme/Erdos287ProofOmegaPartition.lean` | new `ProofOmega` namespace: abstract dyadic partition certificate, exact insertion identity, dyadic local finiteness (`≤ 3`), physical Ω-insertion interface (uninhabited) + firewall |
| `RequestProject/CurrentProgramme/Erdos287PerronSingleContour.lean` | exact `∫_{-T}^{T}(c²+t²)^{-1/2} dt = 2 arsinh(T/c)`, the log budget at `c = 1/L`, `T = L^K`, the `SingleContourL1Bound` interface and its deterministic compiler |
| `RequestProject/CurrentProgramme/Erdos287TypedSourcePacketCompiler.lean` | `SourcePacketDecomposition` with the **explicit global** `totalNuclearMass ≤ nuclearBudget` field; the conditional compiler; log-budget specialisation; the "global mass is not packetwise data" firewall |
| `RequestProject/CurrentProgramme/Erdos287PerronInterfaceCounterguard.lean` | finite counterguard: a per-contour bound is not a total bound without cardinality control |
| `RequestProject/CurrentProgramme/Erdos287BDiagonalDeltaQAbstract.lean` | the abstract `Δ × q_a` finite Fourier kernel, residue aggregation with `(1 + D/n)`, `(1 + E/n)` multiplicities, and the Cauchy step over `t` |
| `RequestProject/CurrentProgramme/Erdos287PhysicalDictionaryInterfaces.lean` | `BDiagonalDeltaQPhysicalDictionary`, `C0SourceRealisationBridge`, `TransverseSourceRealisationBridge` — all uninhabited — plus the conditional physical compiler |
| `RequestProject/CurrentProgramme/Erdos287SourceCoverageCompiler.lean` | `PhysicalOwnerMap` bookkeeping (no double spending, exhaustive over the domain), `PhysicalSourceCoverage100` (uninhabited), coverage firewall |
| `RequestProject/Status/CurrentStatusErdos287MasterSourceFrontier.lean` | the new **controlling** status layer (nodes, statuses, backing theorems, supersession ledger, end-to-end firewall) |
| `RequestProject/Status/AxiomAuditErdos287MasterSourceFrontier.lean` | 100 × `#print axioms` over all principal new declarations + end-to-end regression |
| `ERDOS287_MASTER_SOURCE_FRONTIER_SAFE_BANK_REPORT.md` | this report |

Files modified: `RequestProject/Main.lean` (ten appended imports only).

Authoritative existing bank preserved and imported, byte-identical:
`Status/SemanticFirewallsErdos287.lean`, `Status/CurrentAuthoritativeStatusErdos287.lean`,
`Erdos287/ClosureInputs.lean`, `Status/Erdos287EndToEndStatus.lean`,
`Status/PublicTreeReconciliation20260901.lean`, the C0 finite-Fourier banks, the
one-conductor / dual-level banks, and all historical status and audit modules.

## 2. PRINCIPAL NEW THEOREMS (all kernel-checked)

**Master source (interface only).**
`unprojectedSource`, `norm_unprojectedSource_le`, `norm_unprojectedSource_le_mass`,
`MasterPhysicalSourceRealisation.parent_eq`,
`MasterPhysicalSourceRealisation.parent_eq_zero_of_coefficient_zero`,
`no_realisation_vanishingWeightSpec`, `no_realisation_zeroGcdSpec`,
`sourceDictionary_ne_physicalRealisation`,
`dictionary_population_does_not_construct_parent`, `toy_model_is_not_the_physical_source`.
The realisation structure requires: identification with the authoritative parent
expression, the exact physical index family, the exact coefficient factorisation, a
*positive* shared-gcd coordinate, source coprimality data and the required outer variables.
It is **left uninhabited**; a finite countermodel (`vanishingWeightSpec`) exhibits a
populated dictionary whose claimed physical equality fails, and a separate toy spec shows
the interface is a real condition rather than a disguised `False`.

**Proof-local Ω.**
`DyadicPartition` (non-negative weights, **exact** partition of unity, local support,
bounded overlap), `weight_le_one`, `scales_nonempty`, `one_le_overlapBound`,
`reconstruction`, `unprojectedSource_eq_sum_projectedSource(_of_partition)`,
`card_le_three_of_spread_le_two`, `contributingScales_spread`, **`dyadicLocalFiniteness`**
(`≤ 3` dyadic scales contribute to a fixed positive `g`), `dyadicLocalFiniteness_sharp`
(`= 3` attained), `physical_insertion` (conditional on the uninhabited
`ProofOmegaInsertionInput`), and
**`abstractProofOmegaPartition_does_not_construct_physicalInsertion`**.

**Single Perron contour.**
**`singleContour_integral_eq_arsinh`** — the exact real integral
`∫_{-T}^{T} (c²+t²)^{-1/2} dt = 2 arsinh(T/c)` for `c > 0` (proved, not assumed) —
`arsinh_le_log_one_add_two_mul`, `singleContour_integral_le_log`,
`perronContour_integral_eq` (`c = 1/L`, `T = L^K` ⇒ `2 arsinh(L^{K+1})`),
`perronContour_log_budget`, the interface `SingleContourL1Bound` with the constructions
`singleContourL1Bound_log`, `perronSingleContourL1Bound`, and the deterministic compilers
`contour_compile`, `contour_total_compile` (cardinality explicit).

**Typed source packets.**
`typedPacket_compile`, `SourcePacketDecomposition` (finite index set, continuous parameter
data, coefficients, packet values, error term, exact reconstruction, **explicit global**
`totalNuclearMass ≤ nuclearBudget`), `SourcePacketDecomposition.compile`
(`‖source‖ ≤ nuclear·packetBound + errorBound`), `typedPacket_compile_logBudget`,
`packetwise_coefficient_bound_does_not_bound_total`,
`no_nuclearBudget_from_packetwise_bound`,
`typedPacketCompiler_does_not_construct_masterSource`.

**Per-contour counterguard.**
`perContour_bound_does_not_imply_total_without_cardinality`,
`perContour_datum_compatible_with_unbounded_total`,
`no_global_total_from_perContour_bound`, and the positive companion
`total_bound_of_perContour_and_cardinality`.

**Abstract `Δ × q_a` Fourier kernel.**
`deltaQ_unitaryFourier_bound`, `phase_fiberwise`,
`deltaQ_residueAggregation_compiler` (`‖S‖² ≤ n·M_Δ·M_q·E_A·E_B`),
`deltaQ_residueAggregation_sqrt` (`‖S‖ ≤ √n √M_Δ √M_q ‖A‖₂ ‖B‖₂`),
`deltaQ_interval_compiler` (interval ranges supply `M_Δ = D/n + 1`, `M_q = E/n + 1`),
`cauchy_over_t`, `deltaQ_cauchy_over_t`, `deltaQ_cauchy_over_t_withMultiplicities`.
The banked reciprocal/unitary Fourier theorems were **reused**, not re-proved.

**Physical dictionaries (uninhabited) and coverage.**
`bDiagonalPhysical_compiler` (conditional on the dictionary plus explicit energy inputs),
`bDiagonalPhysicalDictionary_open`, `abstractDeltaQKernel_does_not_close_bDiagonal`,
`c0Bridge_owner_unique`, `c0SourceRealisationBridge_open`,
`transverseSourceRealisationBridge_open`, `owner_labels_distinct`;
`PhysicalOwnerMap.no_double_spending`, `PhysicalOwnerMap.exhaustive`,
`PhysicalOwnerMap.coverage_of_domain`,
`abstractOwnerMap_does_not_imply_physicalSourceCoverage100`, `coverage100_total`,
`physicalSourceCoverage100_open`, `ownerBookkeeping_available_coverage_open`.

**Status layer.**
`status` table, `erdos287_open`, `first_frontier_open`, `next_frontier_open`,
`fullSourceLocalAnalyticKernel_open`, `windowPairSupply_open`, `status_labels_distinct`,
`kernelProved_node_count` (= 5), `open_node_count` (= 6), the six `backing_*` theorems
(every row that claims a proof is backed by an actual theorem),
`no_frontier_module_constructs_closureInputs`, `reconfirm_endToEnd_frontier`,
`closureInputs_supply_still_visible`, `frontier_work_does_not_close_statement`,
`oldClaims_relabelled`, `superseded_claims_retain_content`,
`proofOmega_is_abstract_certificate`.

## 3. BUILD

* Every new module builds individually: PASS.
* Default `lake build`: **success, 8330 jobs, 0 errors**, 32 warnings — all 32 pre-existing
  cosmetic linter warnings in older files; **0 warnings from the new modules**.
* No source file was moved or removed to hide a failure.

## 4. AXIOM AUDIT

`RequestProject/Status/AxiomAuditErdos287MasterSourceFrontier.lean` runs **100**
`#print axioms` reports over the new declarations plus the end-to-end regression chain:

* 89 reports: `[propext, Classical.choice, Quot.sound]`
* 1 report: `[propext]`
* 10 reports: axiom-free

No `sorryAx`, no user `axiom`, no `sorry`, no `admit`, no `unsafe`, no `opaque`, no
`native_decide`, no `@[implemented_by]` occurs as Lean code in any new file; those words
appear only inside docstring prose.

---

## FINAL BLOCK

```
MASTER PHYSICAL SOURCE:
UNINHABITED

SOURCE DICTIONARY != PHYSICAL REALISATION:
KERNEL FIREWALL PASS

PROOF-OMEGA ABSTRACT PARTITION:
KERNEL-PROVED (abstract dyadic certificate; exact partition of unity, local support,
bounded overlap; exact insertion identity)

PROOF-OMEGA PHYSICAL INSERTION:
OPEN (input uninhabited; abstract partition proved not to construct it)

SINGLE-CONTOUR PERRON:
KERNEL-PROVED (exact identity 2·arsinh(T/c); logarithmic budget at c = 1/L, T = L^K)

PER-CONTOUR SUFFICIENCY COUNTERGUARD:
PASS (finite countermodel; no global total from a per-contour bound)

TYPED PACKET COMPILER:
PASS (kernel-proved conditional; global nuclear-mass field is explicit source data)

DELTA x q_a ABSTRACT FOURIER:
PASS (abstract finite kernel, residue-aggregation form, Cauchy over t)

BDIAGONAL PHYSICAL DICTIONARY:
OPEN

C0 SOURCE COVERAGE:
OPEN (bridge type defined, uninhabited)

TRANSVERSE SOURCE COVERAGE:
OPEN (bridge type defined, uninhabited)

BDIAGONAL SOURCE COVERAGE:
OPEN (physical dictionary uninhabited)

FULL SOURCE LOCAL KERNEL:
OPEN

WINDOWPAIR SUPPLY:
OPEN

ERDOS287:
OPEN

CURRENT FORMAL FRONTIER:
UNPROJECTED-MASTER-PHYSICAL-SOURCE-REALISATION45

NEXT RESEARCH FRONTIER:
MASTER-SOURCE-TO-TYPED-PERRON-PACKETS45

BUILD:
lake build PASS — 8330 jobs, 0 errors, 32 pre-existing warnings, 0 new warnings

AXIOM AUDIT:
100 reports; 89 × {propext, Classical.choice, Quot.sound}, 1 × {propext}, 10 axiom-free;
no sorryAx, no custom axiom, no unsafe/opaque/native_decide/implemented_by

STOP.
```
