# Erdős #287 — Research Bank V8 report (post-V7 ENTRY / window / obstruction bank)

**Erdős #287 remains OPEN. This research bank does not prove or disprove it.**

## 1. Files added

```
RequestProject/Erdos287/ResearchBankV8.lean                      (aggregator)
RequestProject/Erdos287/ResearchBankV8/Saturation.lean           (§2B)
RequestProject/Erdos287/ResearchBankV8/RoughWindow.lean          (§2C)
RequestProject/Erdos287/ResearchBankV8/WeakCutoffSeed.lean       (§2D)
RequestProject/Erdos287/ResearchBankV8/ExactEntrySystem.lean     (§2E)
RequestProject/Erdos287/ResearchBankV8/ActiveResidueDP.lean      (§2F)
RequestProject/Erdos287/ResearchBankV8/TernaryBlocker.lean       (§2G)
RequestProject/Erdos287/ResearchBankV8/RigidK2.lean              (§2H)
RequestProject/Erdos287/ResearchBankV8/GoodM.lean                (§2I)
RequestProject/Erdos287/ResearchBankV8/CertificateInterval.lean  (§2J)
RequestProject/Erdos287/ResearchBankV8/VirtualEdge.lean          (§2K)
RequestProject/Erdos287/ResearchBankV8/WholeParentCap.lean       (§2A)
RequestProject/Erdos287/ResearchBankV8/Ledger.lean               (§6, V8 part)
RequestProject/Erdos287/ResearchBankV8/AxiomAudit.lean           (#print axioms, all V8 theorems)
ERDOS287_RESEARCH_BANK_V8_REPORT.md
```

All declarations live in `Erdos287.ResearchBankV8.<FileName>`, so no name can collide with
V2–V7.

## 2. No prior layer modified

`git diff --name-status <initial commit> HEAD` lists only added files under
`ResearchBankV8*` / `ResearchBankV9*` and the two reports. No file of `AnchoredV2`, `AnchoredV3`,
`AnchoredV4`, `ResearchBankV5`, `ResearchBankV6`, `ResearchBankV7`, `ResearchBankV7.lean` or
`ARISTOTLE_SUMMARY.md` was edited, renamed or moved. V8 imports V7 (`ResearchBankV7.Ledger`) and
re-records the V7 ledger verbatim (`Ledger.v7Frozen`, `Ledger.v7_classifications_preserved`,
`Ledger.ofV7_injective`).

## 3. Declarations proved internally (kernel, no parameters beyond ordinary hypotheses)

**§2A Whole-parent cap** (`WholeParentCap`): `forced_card_le_sum`,
`forced_card_eq_sum_of_disjoint` (finite forced-neighbour counting), `entry_alone_not_refuted`,
`entryModel_cap_fails` (model showing the cap fails while entry holds: the kill is of the
*sufficient hypothesis*, not of ENTRY).

**§2B Canonical saturation** (`Saturation`): `saturate_mono` / `saturate_changed` (0→1 only),
`saturate_endpoint`, `selected_subset_saturate`, `saturate_noAdjZero`, `saturate_denomEntry`,
`saturate_forbidden_subset`, `saturate_forbidden_eq`, `saturate_new_dvd`, `integral_of_dvd_sum`,
`saturate_idem`, `saturate_selects_divisors`, `forbidden_saturate_subset_nonDivisors`.

**§2C Rough window** (`RoughWindow`): `coprime_of_rough`, `rough_multiplier_unique`,
`rough_supports_disjoint`, `support_card`, `rough_labels_not_pairwise_coprime`,
`not_forall_rough_coprime` (the stronger "pairwise coprime" property is false),
`grid_glue_lcm`, `onGrid_of_dvd`, `lcm_mul_gcd`, `lcm_not_product`, `glue_example`,
`grid_point_common_iff`, `common_grid_points_card` (gcd endpoint-loss count), `fresh_prime_lcm`,
`fresh_prime_new_grid`.

**§2D Weak-cutoff seed** (`WeakCutoffSeed`, `P = 2^(6k)`, `M = P+2`, `T = M/2`, `A = M/3`, `k ≥ 1`):
`seed_two_dvd_M`, `seed_three_dvd_M`, `seed_T_eq`, `seed_M_eq_two_T`, `seed_T_odd`, `seed_A_pos`,
`seed_A_le_T`, `seed_T_ge_two`, `seed_endpoints_selected`, `nondvd_lcmUpTo_isPrimePow`
(n ≤ 2T, n ∤ L_T ⟹ n a prime power > T), `seed_P_not_dvd`, `seed_P_mem`, `seed_even_zero_eq_P`
(P is the unique even zero), `seed_P_sub_one_factor`, `seed_P_sub_one_not_primePow`,
`seed_P_add_one_factor`, `seed_P_add_one_not_primePow`, `seed_noAdjZero`, `seed_denomEntry`,
and the bundle **`weak_cutoff_entry_existence`** (WEAK_CUTOFF_ENTRY_EXISTENCE), plus the firewall
`weak_cutoff_does_not_transfer` (T = M/2 does not give T = M/(2H)).

**§2E Exact entry system** (`ExactEntrySystem`): `PInt.*` p-integrality algebra, `row_pint_iff`,
`lcm_decomp`, `image_rowSet`, **`pLocal_entry_iff_row_congruence`** (p-local denominator entry ⟺
full row congruence mod `d_p = p^(r_p+1)`, under the stated hypotheses), and the firewalls
`top_digit_insufficient`, `mod_p_not_sufficient`.

**§2F Active-residue DP** (`ActiveResidueDP`): `feasible_eq_of_state_eq` (same previous bit + same
complete residue vector ⟹ same feasible suffixes), `forget_owner_of_final_zero`,
`owner_final_nonzero_infeasible`, `forget_before_final_unsound`, `forget_nonzero_unsound`,
`same_bit_not_same_continuation`, `boundary_bit_only_not_exact`, `boundedSolve_unsat_sound`,
`resource_exhaustion_not_unsat`.

**§2G Ternary blocker** (`TernaryBlocker`): `pairwise_extendible`, `ternary_incompatible`,
`ternary_incompatible_with_guard`, `pairwise_compatibility_not_sufficient`.

**§2H Rigid K2** (`RigidK2`): `rigid_iff_capacity_zero`, `rigid_row_forces_zero`,
`k2_forces_adjacent_zeros`, `k2_unsat`, `row_alone_compatible`, `contact_unique`,
`rigid_row_avoids_selected_endpoint`, `k2_instance`, `rigid_not_positive_capacity`,
`k2_does_not_refute_positive_capacity` (κ=0 obstruction ≠ refutation of the κ ≥ 1 statement).

**§2I GOOD-M** (`GoodM`): `entrySat_count_eq`, `inter_biUnion_card_le`,
`card_pos_of_first_moment`, `completeness_not_automatic`.

**§2J Certificate interval** (`CertificateInterval`): `ceilDiv3_eq_iff`, `div_eq_iff'`,
`Icc_eq_Icc_iff`, **`certInterval_eq_iff`** (C_Q(M) = [a,b] ⟺ M ∈ J(Q;a,b)),
`mem_all_windows_iff`, `window_inter`, `ValidSource.certInterval_eq`, `window_examples`.

**§2K Virtual edge** (`VirtualEdge`): `virtual_edge_from_row`, `virtual_edge_nontrivial`,
`virtual_edge_not_physical_contact`, `virtual_edges_not_independent`, `three_virtual_edges`.

**§6 Ledger** (`Ledger`): `epochV8_chronology`, `ofV7_injective`, `v7_classifications_preserved`,
`v8_no_closed`, `v8_erdos287_open`, `v8_proved_implies_kernel`, `v8_record_rows_not_proved`,
`v8_external_not_proved`, `v8_cap_killed_entry_open`, `killedSufficient_ne_false`,
`superseded_ne_false`.

## 4. Declarations conditional on theorem parameters / interfaces

* `WholeParentCap.old_whole_parent_cap_incompatible` — given `CapAnalyticInput m a C` (lower bound
  on the forced set, upper bound on the summed caps `C N_p/(log N_p)^a`, eventual separation),
  for all `M ≥ M₀` denominator-entry + the every-parent cap bound are jointly impossible. It does
  **not** say that no seed exists.
* `Saturation.saturate_forbidden_small_of_interface` — conditional on
  `NonDivisorCountSublinear` (`|{n ∈ I : n ∤ L_T}| = o(M)`).
* `RoughWindow.sharedGridOutput_of_inputs` — `RoughLabelSupply → LocalDeletionInput →
  SharedGridOutput`, all premises visible in the type.
* `RigidK2.k2_unsat_infinitely_often_of_supply` — conditional on `K2PrimeSupply`.
* `GoodM.exists_good_source_of_first_moment` — `Σ_F |C_X ∩ J_F| < |C_X|` ⟹ a good source,
  with completeness (`Complete`) supplied as a hypothesis.
* `WeakCutoffSeed`: `SeedZeroSetSublinear`, `SeedMassTendsToLogThree` are named external
  propositions (PNT-based), never proved.

## 5. External analytic interfaces left uninhabited

`CapAnalyticInput` (BV/Selberg/Brun–Titchmarsh–type counting), `NonDivisorCountSublinear`,
`RoughLabelSupply` / `LocalDeletionInput` (Croot / prime supply / sieve abundance / mesoscopic
ROW), `SeedZeroSetSublinear`, `SeedMassTendsToLogThree`, `K2PrimeSupply`,
`PositiveCapacityStatement` (the κ ≥ 1 theorem, only compared, never asserted). None has an
instance, default constructor or proof anywhere in V8.

## 6. Historical / status distinctions (V8 ledger rows, `Ledger.v8New`)

| row | status |
|---|---|
| OLD whole-parent SEED-CAP | KILLED SUFFICIENT HYPOTHESIS (not ENTRY = FALSE; `v8_cap_killed_entry_open`) |
| finite forced-neighbour counting | PROVED |
| canonical saturation | PROVED |
| non-divisor count o(M) | CONDITIONAL / external |
| rough multiplier uniqueness, LCM gluing, endpoint loss | PROVED |
| rough labels pairwise coprime | FALSE (counterexample) |
| RoughLabelSupply → … → SharedGridOutput | CONDITIONAL |
| weak-cutoff T=M/2 seed family | PROVED (weak cutoff only) |
| T=M/2 transfers to T=M/(2H) | FALSE (firewall) |
| seed zero set o(M), mass → log 3 | CONDITIONAL / external |
| target-scale ENTRY | OPEN |
| exact prime-power entry system | PROVED |
| top digit (mod p) suffices | FALSE |
| active-residue DP exactness | PROVED |
| boundary-bit-only DP | KILLED METHOD |
| pairwise compatibility sufficiency | KILLED METHOD |
| raw sparse-owner SAT principle | KILLED METHOD (research record only) |
| rigid K2 obstruction (finite core) | PROVED |
| K2 prime supply | CONDITIONAL / external |
| rigid K2 refutes κ≥1 theorem | FALSE |
| GOOD-M bookkeeping | PROVED |
| GOOD-M survivor supply | OPEN |
| certificate source interval | PROVED |
| virtual edge = physical contact | FALSE |
| ternary blocker fixture | FINITE FIXTURE |
| Erdős #287 | OPEN |

Machine-checked: `superseded_ne_false`, `killedSufficient_ne_false`, `v8_no_closed`,
`v8_proved_implies_kernel`, `v8_record_rows_not_proved`, `v8_external_not_proved`.

## 7. Build result

```
lake build RequestProject.Erdos287.ResearchBankV8   → Build completed successfully (8142 jobs).
lake build                                         → Build completed successfully (8653 jobs, whole project).
```
No errors, no warnings in V8 files.

## 8. `#print axioms`

`ResearchBankV8/AxiomAudit.lean` prints axioms for all 135 V8 theorems. Result: each depends on
a subset of `[propext, Classical.choice, Quot.sound]` (82 × all three, 26 × `propext, Quot.sound`,
13 × `propext`, the rest none). No `sorryAx`, no `Lean.ofReduceBool` / `trustCompiler`, no
`_native` axiom, no custom axiom (grep of the build log: 0 hits).

## 9. Forbidden-token scan

`rg -w "sorry|admit|axiom|unsafe|native_decide|bv_decide|opaque|implemented_by"` over the V8
files: the only hits are the `#print axioms` commands and docstrings that *state* these are not
used. No code use.

## 10. Current open owners (V8 scope)

target-scale ENTRY (OPEN); GOOD-M survivor-supply inequalities (`|C_X| > 0`, certificate-family
completeness, first-moment inequality) (OPEN); all §5 external interfaces.

## 11. Honest deviations / limits

* §2G: the p = 107 phenomenon is banked as an abstract finite truth table (three Boolean relations
  that are pairwise extendible but jointly UNSAT, plus a guard). The actual p = 107 numerical
  data is not encoded.
* §2H: bounded-height rigidity is modelled by an abstract row structure (capacity 0 ⟺ rigid);
  the κ ≥ 1 pseudoforest theorem appears only as an uninhabited proposition for the firewall.
* §2A: the analytic counting inputs are bundled in `CapAnalyticInput`, not derived.
* The ternary fixture, killed rows and "raw sparse-owner SAT" are recorded at their evidence level
  (finite fixture / research record), not as theorems about the actual programme data.

## Machine-readable ledger (V8 new rows)

```
OLD_WHOLE_PARENT_CAP=KILLED_SUFFICIENT_HYPOTHESIS
FORCED_NEIGHBOUR_COUNTING=PROVED
CANONICAL_SATURATION=PROVED
NONDIVISOR_COUNT_o(M)=CONDITIONAL_EXTERNAL
ROUGH_WINDOW_ALGEBRA=PROVED
ROUGH_LABELS_PAIRWISE_COPRIME=FALSE
ROUGH_SUPPLY_CHAIN=CONDITIONAL
WEAK_CUTOFF_ENTRY_EXISTENCE=PROVED_WEAK_CUTOFF_ONLY
WEAK_TO_TARGET_CUTOFF_TRANSFER=FALSE
TARGET_SCALE_ENTRY=OPEN
EXACT_PRIME_POWER_ENTRY_SYSTEM=PROVED
TOP_DIGIT_SUFFICES=FALSE
ACTIVE_RESIDUE_DP=PROVED
BOUNDARY_BIT_ONLY_DP=KILLED
PAIRWISE_COMPATIBILITY_NOT_SUFFICIENT=PROVED_FINITE_ABSTRACT
RAW_SPARSE_OWNER_SAT=KILLED
RIGID_K2_CORE=PROVED
K2_PRIME_SUPPLY=EXTERNAL
K2_REFUTES_KAPPA_GE_1=FALSE
GOOD_M_BOOKKEEPING=PROVED
GOOD_M_SURVIVOR_SUPPLY=OPEN
CERTIFICATE_SOURCE_INTERVAL=PROVED
VIRTUAL_EDGE_IS_PHYSICAL=FALSE
ERDOS_287=OPEN
```

Erdős #287 remains OPEN. This research bank does not prove or disprove it.
