# ERDŐS #287 — V24 FULL-`q` BALANCED7 PROVIDER-EXHAUSTIVENESS SAFE BANK

Append-only continuation of the repository.  V20, V21, V22, SP-2 and V23 layers are
untouched; `ARISTOTLE_SUMMARY.md` is unmodified.  The next consistent version identifier
after V23 was chosen: **V24**.

## Files added

| File | Content |
| --- | --- |
| `RequestProject/Erdos287/PhysicalLogPrefactorRepair3221.lean` | repaired physical log prefactor `C_ext = 1`, retraction theorem, `Q = X^{3/5}` local numerology |
| `RequestProject/Erdos287/SP2LiteralPhysicalSource3221.lean` | literal one-sign SP-2 physical source, two-sign reassembly, non-circularity firewalls |
| `RequestProject/Erdos287/EulerUniformityLayer3221.lean` | repaired Euler local factor, explicit `|f − 1| ≤ 6p^{-7/4}` bound, `H_P(0) = 2B(P)`, uninhabited uniformity interface |
| `RequestProject/Erdos287/FullQStructuralPartition3221.lean` | cut `U = X^{1/3}`, three-way sector split, dyadic partition of unity, provider ownership |
| `RequestProject/Erdos287/SmallQSmallRAdapters3221.lean` | literal sector sums, SmallQ / SmallR Type-I adapter interfaces (uninhabited) |
| `RequestProject/Erdos287/HardDyadicProviders3221.lean` | `Q = X^{3/5}` cell metadata, hard dyadic census, exhaustiveness interface (refuted) |
| `RequestProject/Erdos287/BalancedSevenFullQCompiler3221.lean` | full-`q` provider bundle and conditional compiler, firewalls |
| `RequestProject/Status/Erdos287V24Status.lean` | V24 machine ledger |
| `RequestProject/Status/AxiomAuditErdos287V24.lean` | `#print axioms` for all principal V24 declarations |

`RequestProject/Main.lean` extended with nine import lines only.

## Principal theorems proved (kernel-checked, no `sorry`)

Prefactor repair: `sp2CextRepaired_spec`, `oldPrefactor_and_repaired_are_incompatible`,
`repairedPrefactor_not_automatic`, `q35_netLogExponent_eq_neg_five_halves`,
`q35_netLogExponent_lt_neg_one`, `q35_signed_log_margin`, `q35_local_capacity_pass`,
`q35_capacity_is_not_balancedSeven`.

Literal source: `HstarBalancedSeven_eq_depthSum`, `twoSign_reassembles_source_summand`,
`P_sm_eq_sum_of_oneSign`, `oneSignPhysical_eq_comparison_summand`,
`physicalTwoB_not_defined_from_principalQCell`, `principalQCell_carries_no_B`,
`physicalSource_needs_external_twoB`.

Euler layer: `repairedLocalFactor_sub_one_bound`, `repairedLocalFactor_eq_one_iff`,
`balancedSeven_at_most_seven_onP_factors`, `balancedSeven_at_most_seven_oddPrimeDivisors`,
`euler_H0_eq_twoB`, `eulerUniformity_not_automatic`.

Structural partition: `uCut_cube`, `balancedSeven_qr_threeWay_cover`,
`balancedSeven_qr_threeWay_disjoint`, `sum_threeWay`, `sum_threeWay_sector`,
`hardDyadic_partitionOfUnity`, `dyadic_supports_not_disjoint`,
`hardPacketOwner_exists_unique`, `balancedSeven_fullQ_structural_partition`,
`hardDyadicProvider_q35`, `hardDyadicProvider_not_all_owned`, `fullQ_ownership_incomplete`.

Adapters: `sigma_threeWay_reassembly`, `smallQ_closed_of_literal_typeI_adapter`,
`smallQAdapter_not_automatic`, `smallR_closed_of_switched_typeI_adapter`,
`smallRAdapter_not_automatic`, `smallQ_and_smallR_cells_differ`.

Hard cells: `q35_Q_mul_R_eq_X`, `q35_smoothCut_lt_Q`, `q35_inside_hard_sector`,
`hardDyadic_owner_only_q35`, `hardDyadic_census_incomplete`,
`hardDyadicExhaustiveness_not_automatic`, `hardCell_twoSign_total`,
`hardCell_oneSign_insufficient`, `q35_closure_is_not_balancedSeven`.

Compiler: `allQProviderExhaustive_of_inputs`, `sp2BalancedSevenFullQ_of_inputs`,
`balancedSevenAsymptotic_of_fullQ_and_comparison`,
`allQProviderInputs_currently_unavailable`, `fullQ_status_stays_open`,
`fullQ_bound_gives_no_threshold`.

Status: `v24_prefactor_repaired`, `v24_q35_local_numerology`, `v24_finite_layer_proved`,
`v24_external_layer_uninhabited`, `v24_provider_exhaustiveness_fails`,
`v24_q35_is_one_cell_only`, `v24_first_exact_residual`, `v24_census_not_activated`,
`v24_effectivity_separate`, `v24_fullQ_and_erdos287_open`.

## Uninhabited external interfaces introduced

`BalancedSevenEulerUniformity287Input`, `Affine287SP2SmallQTypeIAdapterInput`,
`Affine287SP2SmallRSwitchTypeIInput`, `HardDyadicProviderExhaustiveness287Input`
(the last one is not merely uninhabited but *refuted* by the current census).

---

## FINAL BLOCK

```
C_ext OLD:
    0 — RETRACTED / INCOMPLETE NORMALIZATION
    (oldPrefactor_and_repaired_are_incompatible; historical source preserved)

C_ext CURRENT:
    1 — SP2PhysicalLogPrefactorRepaired, sp2CextRepaired_spec

Q35 LOG EXPONENT:
    -5/2  (q35_netLogExponent_eq_neg_five_halves), < -1

SIGNED LOG MARGIN:
    3     (q35_signed_log_margin)

LITERAL PHYSICAL SOURCE:
    BANKED — one-sign object, two-sign reassembly; 2B(P) is NOT derived from the
    principal q-cell (physicalTwoB_not_defined_from_principalQCell)

EULER LOCAL ALGEBRA:
    PASS — |local factor - 1| <= 6 p^{-7/4}, at most seven on-P corrections,
    H_P(0) = 2 B(P)

EULER UNIFORMITY:
    BALANCED7-EULER-UNIFORMITY45 — RESEARCH PASS / EXTERNAL, UNINHABITED
    (reported A0 = 2 is metadata, not a theorem)

q-PARTITION:
    BALANCED7-QPACKET-STRUCTURAL-PARTITION45 — PASS
    SmallQ / SmallR / Hard cover + disjoint + exact reassembly;
    dyadic partition of unity has non-disjoint supports (firewall proved)

HARD DYADIC CENSUS:
    Q = X^{3/5} : RESEARCH CLOSURE CANDIDATE (single cell)
    all other admissible exponents 1/3 < e < 2/3 : PROVIDER_OPEN / UNCENSUSED

SMALL-q ADAPTER:
    AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45 — OPEN / UNINHABITED

SMALL-r ADAPTER:
    AFFINE287-SP2-SMALLR-SWITCHED-TYPEI45 — OPEN / UNINHABITED
    (q <-> r is not a symmetry: smallQ_and_smallR_cells_differ)

PROVIDER EXHAUSTIVENESS:
    BALANCED7-QPACKET-PROVIDER-EXHAUSTIVENESS45 — OPEN / FAILS as a global claim
    (hardDyadicExhaustiveness_not_automatic)

FULL-q STATUS:
    SP2-BALANCED7-FULL-Q45 — OPEN.  Conditional compiler only; the antecedent bundle
    is currently satisfied by no parameter set
    (allQProviderInputs_currently_unavailable)

BALANCED7 ASYMPTOTIC STATUS:
    OPEN / CONDITIONAL COMPILER + EXTERNAL INPUTS

BALANCED7 EFFECTIVE STATUS:
    OPEN.  No explicit threshold anywhere; ineffective exceptional treatment supplies
    none (fullQ_status_stays_open)

POST-BALANCED7 CENSUS:
    NOT REACHED / NOT ACTIVATED.  It is NOT recorded that the future packet universe is
    a finite Omega-list; bounded fragmentation templates / parametric polytopal families
    may be required.

FIRST EXACT RESIDUAL:
    AFFINE287-SP2-SMALLQ-TYPEI-ADAPTER45

FCL:
    OPEN

ERDOS287:
    OPEN

LAKE BUILD:
    lake build — Build completed successfully (8190 jobs), 0 errors.
    Warnings: pre-existing linter notes only (unused simp arguments / unused variables in
    older files); zero warnings in the V24 files.

TRUST SCAN:
    0 occurrences of sorry / admit / axiom / opaque / unsafe / native_decide /
    @[implemented_by] in all V24 files.
    #print axioms for every principal V24 declaration: only propext, Classical.choice,
    Quot.sound (several depend on no axioms at all).
```

## FINAL FIREWALL

The Euler identity banked here is a statement about local factors and the full-`q`
reassembly; it is not a proof of the analytic aggregate estimate, which remains an
uninhabited external interface.  Closure of the single hard cell `Q = X^{3/5}` does not
close the Hard sector and does not close Balanced7: admissible dyadic exponents remain
unowned, and this is a theorem, not a label.  No generic Type-I theorem is invoked; the
SmallQ and SmallR sectors require a literal generated-coefficient adapter, which is exactly
what the two uninhabited interfaces demand, and the `q ↔ r` switch is not assumed to be a
symmetry.  Research-level external audit status is not relabelled as a kernel proof, and
ineffective asymptotics supply no effective `WindowPairSupply` threshold.

Erdős #287 remains **OPEN**.
