# ERDŐS #287 — BOUNDED-CONDUCTOR FORMAL SYNC REPORT

**INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.**
**NO PUBLIC ERDŐS CLAIM. PUBLIC-PROBLEM-ID PROVENANCE: `PENDING`.**

Checkpoint: `2026-09-08`, version `BOUNDED_CONDUCTOR_SYNC_v1`.
Mode: append-only / current-frontier sync / bounded-conductor interface / exact hyperbola /
CRT algebra / rank-three operator bank / evidence-typed / axiom-audited.

---

## 1. Files added

All under `RequestProject/Erdos287/`:

| # | File | Spec section |
| --- | --- | --- |
| 1 | `CompensatedMeasure.lean` | §5 |
| 2 | `HyperbolaInterfaces.lean` | §6 |
| 3 | `CompensatedSummationByParts.lean` | §7 |
| 4 | `AdjacentInterfaceFirewall.lean` | §8 |
| 5 | `ResidueCollapse.lean` | §9 |
| 6 | `InternalProductFibre.lean` | §10, §11 |
| 7 | `SmallEllCRT.lean` | §12, §13 |
| 8 | `HalfOpenProgressionCompiler.lean` | §14 |
| 9 | `SmallEllMeanCovariance.lean` | §15, §16 |
| 10 | `CompensationLoop.lean` | §18 |
| 11 | `BoundedConductorFrontier.lean` | §19, §24 |
| 12 | `RankThreeOperator.lean` | §20 |
| 13 | `RankThreeProjection.lean` | §21 |
| 14 | `ConductorComplementLedger.lean` | §2, §4 |
| 15 | `AnnihilatorFamily.lean` | §3 |
| 16 | `DensityCompensationRestoration.lean` | §17 |
| 17 | `CurrentStatusEffectivityBoundedConductor.lean` | §1, §22, §23 |

Documents added at repository root:

* `ERDOS287_EXISTING_BANK_INDEX.md` (§0)
* `ERDOS287_BOUNDED_CONDUCTOR_FORMAL_SYNC_REPORT.md` (this file, §28)

## 2. Files modified

| File | Change |
| --- | --- |
| `RequestProject/Main.lean` | **one added import line** for the new aggregator `RequestProject.Erdos287.CurrentStatusEffectivityBoundedConductor` (line 390). Nothing removed. |

`ARISTOTLE_SUMMARY.md` was **not** modified. No pre-existing module was rewritten or
deleted. The only rename inside the new material was internal to this sync
(`Delta → DeltaOp` in `RankThreeOperator`/`RankThreeProjection`), to avoid a collision
with the banked `Erdos287.Effectivity.Delta` of `PerronAlgebra`, which is untouched.

---

## 3. Theorem / evidence table (new material)

### §5 `CompensatedMeasure.lean`

| Declaration | Evidence |
| --- | --- |
| `hyperbolaRegion`, `mem_hyperbolaRegion`, `hyperbolaRegion_fiber`, `hyperbola_double_sum` | KERNEL_PROVED |
| `wbeta`, `etaLoc`, `gz_one_eq_wbeta` | definitions (selected β-weight, exact local η) |
| `selectedWeight_oddConvolution` — `t·β(t) = 1_odd * η` | KERNEL_PROVED |
| `GM`, `etaM`, `GhatM`, `EhatM`, `rhoAtom` | definitions |
| `GM_convolution_form`, `Ehat_exact` | KERNEL_PROVED (finite/exact expression for `Ê`) |
| `abs_rhoAtom_le`, `abs_Ehat_le_l1` | KERNEL_PROVED (tail justification, no external analytic input) |
| `CompensatedTailInterface`, `compensated_tail_not_asserted` | CONDITIONAL_ANALYTIC interface — not inhabited |

### §6 `HyperbolaInterfaces.lean`

| Declaration | Evidence |
| --- | --- |
| `Tn` = `z/(e·n+b)`, `Tn_denom_pos` | definition |
| `Tn_strictAnti`, `Tn_lower_iff`, `Tn_upper_iff` | KERNEL_PROVED (endpoint orientation) |
| `physIndex`, `hyperbola_window_reparam`, `physIndex_eq_Icc`, `physIndex_convex` | KERNEL_PROVED (exact reparametrisation) |
| `physIndexClosed`, `window_convention_firewall` | KERNEL_PROVED (inclusive/exclusive conventions differ) |

### §7 `CompensatedSummationByParts.lean`

| Declaration | Evidence |
| --- | --- |
| `sbpPrincipal`, `sbpEndpoint`, `sbpEhatReg`, `sbpJump` | definitions of the four terms |
| `GM_succ_sub`, `GM_sub_pred` | KERNEL_PROVED |
| `compensated_summation_by_parts` | **KERNEL_PROVED** — exact 4-term identity: principal + endpoint `Ê` − `Ê·H'_reg` − hyperbola-interface jump sum. Strict Bernoulli endpoint convention retained; reuses banked `abel_summation_general`. |
| `sbp_no_smallness_asserted` | KERNEL_PROVED firewall (`EhatM 1 1 = 1/2 ≠ 0`): no error term is asserted small |

### §8 `AdjacentInterfaceFirewall.lean`

| Declaration | Evidence |
| --- | --- |
| `densityCoeff`, `EhatStar`, `Zadj` (`Z_n = n·Ê(z/n)`) | definitions |
| `Zadj_density_constant`, `adjacent_interface_identity` | **KERNEL_PROVED** — density terms cancel, a nonzero arithmetic prefix survives |
| `shortShell`, `shortShell_empty_iff`, `adjacent_emptyShell_difference` | KERNEL_PROVED |
| `adjacent_emptyShell_not_zero` | **KERNEL_PROVED finite counterexample** (`z = 3`, `n = 2`): empty short shell does **not** imply zero adjacent-interface difference |
| `adjacentShellOnlyRoute`, `adjacent_shell_only_retired` | RETIRED_NONCLOSING tag |

### §9 `ResidueCollapse.lean`

| Declaration | Evidence |
| --- | --- |
| `NeCount` (`N_e(I)`), `SdE` (`S_{d,E}(a)`), `DdE` (`D_{d,E}(I)`), `CMI` (`C_{M,I}(s)`) | definitions |
| `shift_mod_eq`, `residue_class_collapse` | **KERNEL_PROVED principal theorem** — all residue classes collapse to `s ≡ z (mod e)` |
| `collapse_to_truncated_divisor_owner`, `offdiagonal_classes_vanish` | KERNEL_PROVED |
| `top_diagonal_absent` | **KERNEL_PROVED principal theorem** — the top diagonal `s = z` is absent |
| `top_diagonal_zero_based_firewall`, `NeCount_partitions` | KERNEL_PROVED |

### §10–§11 `InternalProductFibre.lean`

| Declaration | Evidence |
| --- | --- |
| `sigmaSrc`, `sigmaSrc_of_gt`, `truncated_source_cutoff_preserved` | KERNEL_PROVED (`E = 5000` cutoff-preserving shift sieve) |
| `SdE_truncation_complement` | KERNEL_PROVED — the correction involves only the complementary cases `{1,3,5}` |
| `fibreWindow`, `AfibreDE` (`A_{D,E}(ℓ;s,z)` with `d∣ℓ`, `d ≤ D`, `t = ℓ/d ≥ 2`, `t∣s`, truncated `e`-source) | definitions |
| `internal_product_fibre_identity` | **KERNEL_PROVED** |
| `AfibreDE_mono_D`, `fibreWindow_no_t_one` | KERNEL_PROVED |
| `oldConductorRange`, `internalEllRange`, `internal_ell_not_conductor` | KERNEL_PROVED firewall — internal `ℓ ≠` original conductor `f`; no old `f ≤ 1000` certificate transfers automatically |
| `E5000_cutoff_not_extended` | KERNEL_PROVED firewall — the frozen `e > 5000` source is not restored |

### §12–§13 `SmallEllCRT.lean`

| Declaration | Evidence |
| --- | --- |
| `lambdaSub`, `cEll` (`= μβ/φ`), `gcdFactors`, `coprimeMask`, `Kell` | definitions of `K_ℓ(s,z)` |
| `coprimeMask_eq_indicator`, `gcdFactors_eq_primeFactors_gcd`, `dvd_shift_of_dvd_ell`, `Kell_periodic` | KERNEL_PROVED |
| `outer_fibre_expansion` | **KERNEL_PROVED** — `K_ℓ` already contains the completed outer `d∣ℓ` fibre |
| `cEll_prime`, `Kell_prime_specialisation` (`K_p(s,z) = β(p)·1_{p∣s}`) | KERNEL_PROVED |
| `crtAtom`, `crtIndex`, `crtIndexFull`, `crtIndex_subset`, `coprimeMask_expansion`, `bracket_expansion` | KERNEL_PROVED |
| `Kell_crt_expansion` | **KERNEL_PROVED** — finite divisor/CRT expansion over coprime `a,b` with `ab∣ℓ`, `a > 1` |
| `disjoint_pairs_card` (`3^ω`), `crtIndex_card` (`3^ω − 2^ω`) | KERNEL_PROVED |
| `odd_prod_lower`, `omega_le_four_of_odd_le_5000` | KERNEL_PROVED (`ω(ℓ) ≤ 4` for odd `ℓ ≤ 5000`) |
| `crt_atoms_le_65` | **KERNEL_PROVED** — term count `≤ 65` |
| `beta_pos_of_odd_prime`, `second_dfibre_double_count` | KERNEL_PROVED firewall — a second `d`-fibre summation is an illegal double count |

### §14 `HalfOpenProgressionCompiler.lean`

| Declaration | Evidence |
| --- | --- |
| `apSet`, `apLow`, `apHigh`, `ap_injective` | definitions, half-open `A ≤ s < B`, `s ≡ r (mod m)` |
| `progression_reindex`, `progression_sum_reindex`, `apCount_exact` | KERNEL_PROVED — exact `T(A,B;r,m)` |
| `residueCount`, `periodic_of_shift`, `periodic_window_compiler` | KERNEL_PROVED |
| `Qell`, `Qell_compiler` | **KERNEL_PROVED** — exact finite compiler `Q_ℓ(A,B;z)`, no iteration over huge `s`-ranges |

### §15–§16 `SmallEllMeanCovariance.lean`

| Declaration | Evidence |
| --- | --- |
| `crt_two_factor`, `crt_prod_sum` | KERNEL_PROVED (CRT reassembly) |
| `local_sum_mask`, `local_sum_full`, `periodSum`, `meanK`, `Kell_local_split`, `smallEll_periodSum`, `totient_prod_primeFactors`, `totient_cast_prod` | KERNEL_PROVED |
| `smallEll_local_mean` — `mean(K_ℓ) = −μ(ℓ)β(ℓ)/ℓ` for `ℓ > 1` | **KERNEL_PROVED** |
| `prime_periodSum` | KERNEL_PROVED |
| `complete_fibre_not_zero_mean` | KERNEL_PROVED firewall — a complete local divisor fibre does **not** imply zero local mean |
| `Zcent` (`Z_ℓ = K_ℓ − mean`), `GammaL` (`Γ(ℓ,r)`) | definitions |
| `gram_quadratic_form`, `gram_quadratic_form_nonneg` | **KERNEL_PROVED** — positive quadratic-form decomposition (diagonal + divisor-square terms) |
| `period_covariance_does_not_control_intervals` | KERNEL_PROVED firewall |

### §17 `DensityCompensationRestoration.lean`

| Declaration | Evidence |
| --- | --- |
| `DensitySource` (`D_X`, `Q_{≤5000}`, `A_{>5000}`, `V*`, `P_boundary`, `ω`, `W`, `X`), `vstarBlock`, `outerWeight`, `bracket`, `compBlock`, `Ttilde` | definitions |
| `Ttilde_source_identity` | **KERNEL_PROVED** — the canonical `k = 1` source identity written out in full |
| `Ttilde_split` | **KERNEL_PROVED** — owner-block split, each owner charged exactly once |
| `DX_term_not_removable` | **KERNEL_PROVED firewall** with explicit finite witness (`T̃ = −4` vs `0`) |
| `Ttilde_zero_of_all_owners_zero` | KERNEL_PROVED sanity check |

### §18 `CompensationLoop.lean`

| Declaration | Evidence |
| --- | --- |
| `bankedAtom`, `compAtom` | definitions |
| `loop_cancellation_le_1000` | **KERNEL_PROVED** — `ℓ ≤ 1000` lies outside the original conductor support and cancels atomwise |
| `compAtom_gt_1000`, `returnedKernel`, `returnedKernel_eq_compensated_sum` | KERNEL_PROVED — the exact returned finite-conductor kernel for `1000 < ℓ ≤ 5000` |
| `gcdFactors_prime`, `coprimeMask_one`, `cEll_ne_zero`, `Kell_ne_zero_at_prime_atom` | KERNEL_PROVED |
| `returnedKernel_not_identically_zero` (witness `ℓ = 1001`) | KERNEL_PROVED |
| `LoopStatus`, `reassembleStatus`, `reassembly_exact_loop` | **KERNEL_PROVED HIGH-PRIORITY firewall** — reassembling the returned kernel into the original conductor expression is an EXACT LOOP, not closure |

### §19, §24 `BoundedConductorFrontier.lean`

| Declaration | Evidence |
| --- | --- |
| `BoundedConductorK1Target` | **OPEN** — defined, deliberately **not inhabited** |
| `boundedConductorTarget_mono`, `boundedConductor_target_has_content` | KERNEL_PROVED (the target is non-vacuous) |
| `FixedConductorCharacterBound` | **OPEN** research interface (signed outer-`z` control after finite DFT/character expansion of the bounded conductor kernel, `1000 < ℓ ≤ 5000`) — **not inhabited** |
| `character_bound_implies_k1_owner_bound` | **CONDITIONAL_ANALYTIC / KERNEL_PROVED implication** — `FixedConductorCharacterBound → k = 1` owner bound |
| `FrontierStatus`, `positiveFiniteKernelWrapper`, `currentK1Frontier`, `frontier_status_record` | RETIRED_NONCLOSING tag for the positive finite-kernel wrapper |

### §20 `RankThreeOperator.lean`

| Declaration | Evidence |
| --- | --- |
| `sum_moebius_divisors`, `moebius_mul_id_eq_totient`, `multiples_card`, `legendre_coprime_count` | KERNEL_PROVED |
| `P1`, `DeltaOp` (`Δ_k(x) = ∑_{d∣k} μ(d) P₁({(k/d)x})`), `coprimeCount` | definitions |
| `DeltaOp_discrepancy_identity` — `Δ_k(x) = φ(k)x − #{1 ≤ n ≤ kx : (n,k)=1}` | **KERNEL_PROVED** |
| `DeltaOp_periodic` | KERNEL_PROVED |

### §21 `RankThreeProjection.lean`

| Declaration | Evidence |
| --- | --- |
| `fractShiftSum`, `fractShiftSum_shift`, `fractShiftSum_shift_int`, `fractShiftSum_fundamental` | KERNEL_PROVED |
| `sawtooth_multiplication` (Raabe / Bernoulli multiplication identity) | **KERNEL_PROVED** |
| `shiftAverage`, `primitiveProjection`, `AoneProj` (`A_{1,f}(k,z)`) | definitions |
| `shiftAverage_norm`, `projection_norm_interface` | KERNEL_PROVED — exact finite projection norm interfaces |
| `cellValue`, `rankThree_cell_reduction`, `rankThree_extremum_finitely_many_cells` | **KERNEL_PROVED** — the extremum reduces to finitely many rational cells |

### §2, §4 `ConductorComplementLedger.lean`

| Declaration | Evidence |
| --- | --- |
| `bigOmega`, `complementSlab` (`k < 15015`, `Ω(k) ≤ 3`), `mem_complementSlab`, `omega_le_bigOmega_on_slab`, `slab_excludes_15015`, `slab_contains_core` | KERNEL_PROVED (exact finite decomposition; no numeric whole-slab bound is kernel-promoted) |
| `Owner` (`d > 30000` internal projector tail, `e > 5000` source, `t = 1` atom, `P8` boundary replacement, rank-three owners, `k = 1` core), `SourceVar`, `ownerSource` | definitions |
| `owner_sources_pairwise_disjoint` | **KERNEL_PROVED** — owners are disjoint at their declared source variables |
| `Ledger`, `ledgerTotal`, `ledgerUpdate`, `ledgerUpdate_total`, `ledgerUpdate_preserves_others` | **KERNEL_PROVED** — subtraction/update laws preserve the parent source |
| `disjointness_gives_no_bound` | KERNEL_PROVED firewall — no numerical inequality follows from disjointness alone |

### §3 `AnnihilatorFamily.lean`

| Declaration | Evidence |
| --- | --- |
| `charSum`, `Annihilates` | definitions |
| `char_shift_eigenvalue` | **KERNEL_PROVED** — exact operator eigenvalue relation |
| `char_unit_inv_mul`, `invariant_annihilated_of_char_ne_one` | **KERNEL_PROVED** — primitive-character kernel condition ⇒ exact annihilation |
| `constant_source_annihilated` | KERNEL_PROVED — character-cover implication |
| `AnnihilationCertificate`, `censusSize = 8112`, `census_size_value` | **CERTIFICATE_BACKED DATA** (no 8112 individual declarations) |
| `certified_pair_annihilates`, `source_owner_exclusion` | **KERNEL_PROVED** — any certified pair satisfies the exact annihilation predicate; source owner exclusion |

### §1, §22, §23 `CurrentStatusEffectivityBoundedConductor.lean`

| Declaration | Evidence |
| --- | --- |
| `EvidenceCurrent` (9-tag taxonomy), `EvidenceCurrent.isClosed`, `EvidenceCurrent.ofAncestor` | definitions |
| `evidence_embedding_preserves_closure` | KERNEL_PROVED |
| `Checkpoint`, `boundedConductorCheckpoint`, `checkpoint_tag_recorded` | data + KERNEL_PROVED tag (`2026-09-08`, `BOUNDED_CONDUCTOR_SYNC_v1`) |
| `BoundedConductorNode`, `boundedConductorEvidence`, `boundedConductorOpenNodes` | definitions |
| `boundedConductor_open_frontier` | **KERNEL_PROVED** — no open node is tagged closed; Maynard `NOT_ENTERED`; public-problem-id provenance recorded unresolved |
| `early4490_preserved_as_ancestor` | KERNEL_PROVED — EARLY_4490 preserved; only its role as current root is `SUPERSEDED` |
| `current_k1_frontier_is_bounded_conductor` | KERNEL_PROVED |
| `RankThreeSnapshot`, `rankThreeSnapshot`, `rankThree_snapshot_is_certificate_backed`, `rankThree_strictly_reduced` | **CERTIFICATE_BACKED data, checkpoint-tagged**; closed/remaining lists disjoint |
| `frontier_targets_not_inhabited` | KERNEL_PROVED |

---

## 4. Old / new frontier relation

| Coordinate | Before this sync | After this sync |
| --- | --- | --- |
| EARLY_4490 rational-jet bank | live root coordinate | **preserved as valid ancestor**, `SUPERSEDED` only in its role as current root |
| EARLY_4490 leaf | OPEN / strictly reduced | unchanged: OPEN / strictly reduced |
| compensated interface | not banked | **KERNEL-PROVED exact identity** |
| `ℓ ≤ 5000` CRT compiler | not banked | **KERNEL-PROVED** (`≤ 65` atoms per `ℓ`) |
| `ℓ ≤ 1000` layer | not banked | **KERNEL-PROVED exact cancellation** |
| `1000 < ℓ ≤ 5000` layer | not banked | **returned finite-conductor kernel defined and proved non-vanishing; the CURRENT `k = 1` OPEN FRONTIER** |
| positive finite-kernel wrapper | — | RETIRED_NONCLOSING |
| rank three | open | STRICTLY_REDUCED (numeric closures CERTIFICATE_BACKED, checkpoint-tagged) |
| `Ω(k) = 2`, `Ω(k) = 1` | OPEN | OPEN |
| proper gamma, `S_live`, `R_012`, signed floor, final splice | OPEN | OPEN |
| Maynard | NOT_ENTERED | NOT_ENTERED |
| public-problem-id provenance | PENDING | PENDING |

The sync strictly extends the frontier: no previously open node was closed, and the
`k = 1` question was moved from "unformalised" to "an explicitly defined bounded-conductor
kernel with an explicitly stated, uninhabited analytic target".

---

## 5. Axiom audit (§26)

`#print axioms` is executed inside
`RequestProject/Erdos287/CurrentStatusEffectivityBoundedConductor.lean` for every principal
new theorem. Build output:

```
compensated_summation_by_parts            : [propext, Classical.choice, Quot.sound]
residue_class_collapse                    : [propext, Classical.choice, Quot.sound]
top_diagonal_absent                       : [propext, Classical.choice, Quot.sound]
internal_product_fibre_identity           : [propext, Classical.choice, Quot.sound]
Kell_crt_expansion                        : [propext, Classical.choice, Quot.sound]
crt_atoms_le_65                           : [propext, Classical.choice, Quot.sound]
smallEll_local_mean                       : [propext, Classical.choice, Quot.sound]
gram_quadratic_form                       : [propext, Classical.choice, Quot.sound]
loop_cancellation_le_1000                 : [propext, Classical.choice, Quot.sound]
reassembly_exact_loop                     : [propext, Classical.choice, Quot.sound]
returnedKernel_not_identically_zero       : [propext, Classical.choice, Quot.sound]
character_bound_implies_k1_owner_bound    : [propext, Classical.choice, Quot.sound]
DeltaOp_discrepancy_identity              : [propext, Classical.choice, Quot.sound]
rankThree_extremum_finitely_many_cells    : [propext, Classical.choice, Quot.sound]
owner_sources_pairwise_disjoint           : [propext]
certified_pair_annihilates                : [propext, Classical.choice, Quot.sound]
Ttilde_split                              : [propext, Classical.choice, Quot.sound]
DX_term_not_removable                     : [propext, Classical.choice, Quot.sound]
boundedConductor_open_frontier            : does not depend on any axioms
```

Only the benign standard dependencies `propext`, `Classical.choice`, `Quot.sound` occur.

Trust-policy scan of the 17 new modules for
`sorry | admit | native_decide | @[implemented_by] | axiom | unsafe | opaque | trustCompiler`:
**no matches**.

## 6. Build outputs (§27)

* Dedicated per-module builds: **PASS** for all 17 new modules
  (`lake build RequestProject.Erdos287.<Module>`), zero errors, zero warnings.
* New aggregator `RequestProject.Erdos287.CurrentStatusEffectivityBoundedConductor`:
  **PASS**.
* Full repository build `lake build`: **PASS** —
  `Build completed successfully (8493 jobs).`  No pre-existing failure was encountered;
  no unrelated code was touched.

## 7. Current open analytic theorem (§24)

```
Erdos287.Effectivity.FixedConductorCharacterBound
```

*Control the signed outer `z`-sum after a finite DFT / character expansion of the
bounded-conductor kernel for `1000 < ℓ ≤ 5000`.*

It is defined and **not inhabited**. The conditional bridge
`character_bound_implies_k1_owner_bound` shows it implies the corresponding `k = 1`
owner bound at the exact source level.

**Next mathematical action:** fixed-conductor finite-DFT / character expansion followed by
the signed outer-`z` estimate.

**NO PUBLIC ERDŐS CLAIM. PUBLIC PROBLEM ID: PENDING.**
