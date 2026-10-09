# Erdős #287 — post-`Q_Σ` consolidation (V53 → V64): formal bank, audit and frontier

**ERDŐS #287 REMAINS OPEN.**
PG-287 has not been proved. No finite-exclusion certificate beyond `M ≤ 4·10⁹` is formalised:
the Huang 502-digit `U_fin` bundle is **not** in the repository.

This run only added files; no existing file was modified (see §6). Everything is in
`RequestProject/Erdos287/PostQSigma/`, in namespace `Erdos287.PostQSigma`, with the aggregator
`RequestProject/Erdos287/PostQSigma.lean`.

**Source note.** No V53–V64 manuscripts were supplied with the project. Every definition below
was rebuilt from the task specification. Wherever a paper statement was under-specified, the
Lean statement gives the exact hypotheses that were actually proved. These are recorded in the
"Notes" column.

## 1. Status key

* Mathematical status: BANK / PAY / STRICT REDUCE / PROVISIONAL / RETIRED / OPEN / CLOSED.
* Formal status categories:
  * (1) proved in Lean;
  * (2) proved in Lean, conditional on an explicit provider or hypothesis;
  * (3) external input, formalised;
  * (4) external input, not formalised locally;
  * (5) paper-level, not formalised;
  * (6) open.
* Axioms: every proved declaration was checked with `#print axioms` (see
  `PostQSigma/AxiomAudit.lean`). The result is always `[propext, Classical.choice, Quot.sound]`;
  `Ledger.open_entries` depends on no axioms at all.

## 2. Final table

| Object | Lean declaration(s) | Math status | Formal status | Axioms | Supersedes | Notes |
|---|---|---|---|---|---|---|
| original #287 | `Erdos287.erdos287_seq_of_no_counterexample`, `Erdos287Counterexample`, `ClosureInputs.Erdos287Statement` | OPEN | (6) | — | — | the original ordered-sequence statement is kept visible; it remains open |
| ExactSource | `ExactSource.sourceSol_of_counterexample`, `counterexample_of_sourceSol`, `erdos287_iff_no_source`, `original_erdos287_iff_exact_source` | BANK | (1) | std | — | adapter A |
| QSigma | `ExactSource.QSigma_dvd_prod`, `no_solution_of_QSigma_gt_Pmax` | BANK | (1) | std | — | "global `Q_Σ > P_max` as the universal owner" is RETIRED |
| QSigmaStrong | `QSigmaStrong`, `GammaSum`, `GammaSum_le_factorization`, `QSigmaStrong_dvd_prod`, `Qold_dvd_QSigmaStrong`, `no_solution_of_QSigmaStrong_gt_Pmax`, `Fixture.fixture_Qold/QSigmaStrong/Pmax/strict_improvement` | BANK | (1) | std | QSigma (max-depth) | fixture V={2..7}, W=420, T=235: `Q_old=84`, `Q_Σ=168`, `P_max=105`. DIAGNOSTIC only |
| weighted primary cover | `weighted_primary_cover_excludes`, `MarginalLP`, `no_solution_of_marginalLP_infeasible` | BANK | (1) | std | product compression | no LP duality assumed |
| mandatory primary | `Mandatory`, `MAND`, `mandatory_subset_solution`, `mandatory_adjacency_excludes`, `infeasible_excludes` | BANK | (1) | std | — | |
| exact-mass automaton | `Reach`, `reach_iff`, `exact_mass_automaton_iff`, `modW_false_acceptance` | BANK | (1) | std | modulo-W automaton (RETIRED) | false-acceptance fixture V={2,4,6,8}, W=24, T=1 |
| V57 local criterion | `mandatory_iff_local`, `selected_complement_congruence`, `eta`, `exists_unreachable_iff_deepest` | BANK | (1) | std | — | set version, with the fixed endpoints made explicit through `eta` |
| V57 deep classification | `deep_mandatory_classification`, `deepExceptions`, `pair_exists`, `res_pair_zero`, `pow_eW_le` | BANK | (1) | std | — | **all M**, no census. Hypotheses: `a ≥ 1`, `H(a,M) ≥ 1`. Terminal cases `(a,M)=(21,55),(21,56)` are checked in the kernel |
| — audit counterfixture | `deep_classification_needs_harmonic` | BANK (diagnostic) | (1) | std | — | `(a,M)=(22,50)`: `2a ≤ M` holds, `H<1`, and `(7,2)` is mandatory. So `H ≥ 1` cannot be weakened to `2a ≤ M` |
| five-coordinate theorem | `MAND1`, `Ddeep`, `mandatory_eq_first_digit_union_deep_exception`, `Ddeep_disjoint`, `Ddeep_localised`, `Ddeep_prime_support` | BANK | (1) for the decomposition and localisation; (5) for `|Ddeep| ≤ 5` | std | — | `|Ddeep| ≤ 5` is **not formalised**. Only the localisation into the 4 exceptional layers is proved. Exploratory search (not certified) found `max |Ddeep| = 4` for M ≤ 260 |
| first-digit structure | `firstDigit_residue_ne_zero`, `firstDigit_pair_iff`, `firstDigit_mandatory_no_endpoint`, `firstDigit_singleton` | BANK | (1) | std | — | the size ≤ 3 classification with exceptional primes was not supplied and is **not formalised** |
| harmonic corridor | `harmonic_source_le_half`, `harmonic_lt_log`, `exp_mul_pred_lt_of_harmonic` (`e(a-1) < M`), `eight_mul_pred_lt_three_mul`, `harmonic_rational_bound`, `counterexample_corridor` (`16M<121a`) | BANK | (1) | std | — | no transcendental axioms |
| translated-row theorem | `RecipZSF`, `translated_row_zero_sum_free`, `translated_row_mandatory`, `prefix_row_mandatory`, `fixture_cofInt/translated_ok/prefix_fails` | BANK | (1) | std | prefix rows | fixture p=7, row {4,5,6}: the translated row is certified, the prefix [1,6] fails. The 10^18/10^24 chains are validation only. The strengthened endpoint cap `3M ≤ 8n` is **not** formalised (its hypotheses were not supplied) |
| V54 source qualification | `source_qualification` | BANK | (1) | std | — | the other V54 numerator/boundary items (0.19/log M, 0.81/log M) were not supplied and are not the owner. Not formalised |
| every-M contacts | `Pplus`, `contactInterval`, `contacts`, `contacts_card_ge`, `ContactSupply` | BANK | (2) | std | Maynard windows (RETIRED) | the explicit prime-count supply is isolated as `ContactSupply` (category 4) and is never asserted |
| owner-disjoint matching | `greedy_matching`, `owner_degree_le`, `contact_matching`, `distinct_rows_activated`, `large_prime_row_card_ge_three` | BANK | (1) | std | — | |
| diameter-primary cap | `diameter_primary_cap`, `dvd_lcm_of_diameter`, `top_strip_omitted` | BANK | (1) | std | — | no novelty claimed |
| contact defect | `Defect`, `defect_contradiction`, `ContactDefect287`, `erdos287_of_ContactDefect287` | PROVISIONAL | `ContactDefect287` is (6) and never asserted | std | — | |
| exact core/carry identity | `CoreCarry.core_carry_identity`, `CoreCarry.core_carry_iff` | BANK | (1) | std | modular residue solvability | exact identity over ℚ/ℤ |
| contact-carry bridge | `CoreCarry.cover_lower_bound`, `tau_gt_tenth`, `contact_carry_lower_bound`, `core_cut`, `contact_carry_cut` | PAY | (2) | std | — | conditional on the contact-abundance hypothesis `5|E| > M`, which comes from `ContactSupply` |
| three-status GF | `StatusCarry.Gedge_eq`, `three_status_factorisation`, `relaxed_coeff_zero_excludes` | BANK | (1) | std | — | stated as a relaxation: only the exclusion direction is used |
| status carry cosets | `StatusCarry.gco`, `carry_modEq`, `gco_eq` (`g = Lh / lcm V`), `gco_eq_one_of_lcm_complete`, `edge_carry_mem_cosets`, `fixture_g_one`, `fixture_g_three` | BANK | (1) | std | — | the cosets are not claimed to be nontrivial. LCM-complete gives `g=1` (firewall) |
| square-certificate firewall | `square_certificate_excludes`, `interpolation_firewall`, `punctured_cube_degree` | BANK | (1) | std | arbitrary-degree certificates (RETIRED) | the delta at the origin needs degree `r` on `{0,1}^r` |
| approximate-mass firewall | — | RETIRED route | (4) | — | fixed Archimedean gap | the Croot construction is not formalised (documentation only) |
| hard-core coefficient | `Omega`, `Bm`, `Xd`, `hardCorePoly`, `NT`, `hard_core_coefficient_exact`, `sourceSol_iff` | BANK | (1) | std | — | |
| no-wrap | `no_wrap_recip`, `Bm_lt_W`, `T_nonneg`, `T_lt_W`, `no_wrap` | BANK | (1) | std | modulo-W surrogate | domain `1 ≤ H < 2` |
| root-of-unity filter | `fourier_filter`, `root_of_unity_exact_coefficient` | BANK | (1) | std | — | |
| conductor decomposition | `cond`, `Acond`, `conductor_decomposition`, `A_one`, `physical_conductor_decomposition` | BANK | (1) | std | — | no absolute values across d |
| Ramanujan blocks | `ramanujan`, `A_eq_sum_ramanujan`, `divisor_block_identity`, `physical_ramanujan_block_identity` | BANK | (1) | std | — | |
| transfer matrix | `Transfer.Zw`, `Zw_succ_succ`, `tmat`, `tmat_mulVec`, `transfer_matrix_product`, `tmat_mul_tmat`, `tmat_det`, `Zw_one` | BANK | (1) | std | — | exact algebra only. No contraction claim |
| prime resonance firewall | `prime_block_identity` (`A_p = pN_p − P`), `prime_resonance_dvd_iff` (`p∣X(E) ⇔ p∈E`), `v64_prime_resonance`, `forced_count_fib`, `prime_resonance_fib`, `Ptot_le_eight_forced`, `SC287.abs_A_p_lower`, `SC287.prime_moduleA_false` | BANK | (1) | std | prime square-root Module A (RETIRED) | fully proved with no external input: for every `θ < 1` and every `C`, `‖A_p‖ ≤ C p^θ P` fails on the family `M=2p−1`, `a=⌊M/4⌋`. Binet asymptotics are not needed (the 8-to-1 forcing bound replaces them) |
| composite resonance firewall | — | RETIRED route | (4) | — | aggregate SC-287 | needs PNT/θ(x) and an affine-form Selberg upper bound. Not formalised |
| SC-287 status | `SC287.PrimeModuleA` (defined only to be refuted) | **RETIRED** | prime module refuted in Lean (1); aggregate version: (4) | std | — | no downstream theorem uses SC-287 |
| proper-modulus set | `Lset` (`q ∣ W ∧ q^25 ≤ W^12`), `lcm_lt_of_mem_Lset`, `proper_modulus_firewall` | BANK | (1) | std | — | no Gram entry uses `N_W = N_T` |
| Gram PSD | `Gram`, `gram_eq_sum`, `quadForm_eq_sum_sq`, `gram_psd`, `proper_modulus_gram_psd` | BANK | (1) | std | — | |
| exact Gram majorant | `gram_majorant`, `proper_modulus_majorant` (`N_T ≤ λᵀGλ`), `zero_count_certificate` | BANK | (1) | std | — | covers §42: an unreachable proper modulus gives the single-projector certificate |
| PG strictness fixture | `W30.target_absent`, `W30.gram_values`, `W30.constrained_optimum_ge_one` | BANK (diagnostic) | (1) | std | — | W=30. PG-287 has real content |
| PG-287 | `PG287` (definition only) | **OPEN / PROVISIONAL** | (6) | — | — | never proved, assumed or instantiated (scan in §5) |
| ψ(M) ≥ 0.9M | `PsiLowerBound` | BANK (external) | (4) | — | V63 misuse (RETIRED) | used only as an explicit hypothesis, in the correct direction |
| entropy estimate | `indepCount_le`, `Ptot_eq_indepCount`, `Ptot_lt_exp` (`log P < 21M/50`) | BANK | (1) | std | — | |
| closure arithmetic | `pow_le_exp_of_large`, `capacity_closure`, `count_zero_of_PG287` | BANK | (1) | std | — | `M^100 W^{-12/25} P < 1` for `M ≥ 2^1500`, in integer-safe form |
| finite exclusion interface | `FiniteExclusionUpTo`, `finiteExclusionUpTo_4e9`, `FiniteExclusionUpTo.mono` | BANK (4·10⁹) / OPEN (U_fin) | (1) for 4·10⁹ | std | — | no Huang bundle is present, so the larger range is a premise |
| PG tail theorem | `PG287_implies_no_tail_source`, `no_large_counterexample_of_PG287` | STRICT REDUCE | (2) | std | — | assumes `PG287` (open) and `PsiLowerBound` (external) |
| finite/tail splice | `finite_exclusion_and_PG287_imply_erdos287` (B), `erdos287_of_PG287_repository_native` (A) | STRICT REDUCE | (2) | std | — | B assumes `FiniteExclusionUpTo U` with `2^1500 ≤ U+1`. A uses the proved 4·10⁹ bank and leaves `(4·10⁹, 2^1500)` as a hypothesis |
| final #287 | — | **OPEN** | (6) | — | — | **ERDŐS #287 REMAINS OPEN** |

Fixtures that were requested but are not in the repository:
* the physical CRT fixture `N_2=8, N_3=13, N_6=0` (its `(a,M)` was not supplied);
* the V57 small deep-layer tables, as separate tables. The classification theorem covers them for all M.

## 3. Retired routes (none appears as a closure assumption)

The following routes are listed as RETIRED in `PostQSigma/Ledger.lean`:
* global QSigma>Pmax as the owner;
* b-optimisation;
* pure >1/2 mandatory packing;
* the finite-coverage extension owner;
* Maynard graph pigeonhole;
* independent row-solvability;
* transition-primary-only closure;
* arbitrary-degree square certificates;
* fixed Archimedean mass gap;
* the prime-conductor square-root Module A (refuted in Lean);
* aggregate SC-287;
* automatic CRT tensorisation;
* bare compressed prime-row transfer;
* the modulo-W automaton (refuted in Lean).

`Ledger.open_entries` (proved by `decide`) shows that the only OPEN entries in the ledger are
the original problem and PG-287.

## 4. Audit findings (SUCCESS C items)

1. **V57 deep classification: hypothesis repair.**
   * The classification is false under only `2a ≤ M`. Counterfixture
     `deep_classification_needs_harmonic`: `(a,M)=(22,50)`, `p=7`, `d=2`, mandatory.
   * It is true under `H(a,M) ≥ 1`. This is the hypothesis in `deep_mandatory_classification`,
     proved for all M.
   * The proof also needs the sharp value `e > 2.718`: the rational bound `8(a−1) < 3M` is not
     enough, because `(a,M)=(21,55)` survives it.
   * The two terminal cases are `(21,55)`, excluded by `H<1`, and `(21,56)`, excluded by
     `η_{7,2} ≠ 0`.
2. **`|Ddeep| ≤ 5`: not reproduced formally.** Only the localisation into the four exceptional
   layers is proved; the cardinality bound is left as a paper-level claim.
3. **Earlier repair (kept from the previous checkpoint).** `Pmax ≤ M^k` needs `M > 0`.

No exact V53–V64 bank item that was formalised turned out to be false as stated, once the
hypotheses were made explicit.

## 5. Checks

* Narrow builds: every new module was built individually with `lake build <module>`.
* `lake build RequestProject.Erdos287.PostQSigma.AxiomAudit` succeeds (8074 jobs).
* Full `lake build`: see §5a.
* Forbidden-token scan:
  * Command: `rg 'sorry|admit|^\s*axiom|native_decide|bv_decide|unsafe|implemented_by|opaque'`
    over `PostQSigma/` and `PostQSigma.lean`.
  * Result: the only hit is the word "axiom" inside a docstring (`PathCount.lean`, "no
    transcendental axiom"). There are no code hits.
* Provider scan:
  * `PG287`, `PsiLowerBound`, `FiniteExclusionUpTo U_fin`, `ContactSupply` and
    `ContactDefect287` appear only as definitions or as hypotheses of implications.
  * There is no `instance`, no `theorem PG287`, and no term of these types is constructed.
  * `SC287.PrimeModuleA` appears only as a refuted proposition.
* `#print axioms`: as stated in §1, for all 51 major declarations (`PostQSigma/AxiomAudit.lean`).
* `leanchecker`: see §5a.
* Append-only check: `git diff --name-status 7a33e99` lists only `A` (added) entries; no existing
  file was modified.

### 5a. Full build and checker

* Full `lake build`: **Build completed successfully (8941 jobs)**, exit code 0.
  * The log has 26 warnings, all in pre-existing files.
  * None of the warnings is in `PostQSigma/`.
* `lake build RequestProject.Erdos287.PostQSigma.AxiomAudit`: success (8074 jobs).
* `lake env leanchecker RequestProject.Erdos287.PostQSigma.AxiomAudit` (non-fresh): exit 0, in about 28 s.
* `lake env leanchecker --fresh RequestProject.Erdos287.PostQSigma.AxiomAudit`: did **not**
  finish. It hit the 1750 s timeout (exit 124) with no output, so there is no fresh-replay
  result to report.

## 6. Files added in this run

All files below are under `RequestProject/Erdos287/PostQSigma/`, except the aggregator
`RequestProject/Erdos287/PostQSigma.lean` and this report:

* `QSigmaStrong.lean`, `PrimaryCover.lean`, `MandatoryPrimary.lean`, `MandatoryLocal.lean`
* `ExactMassAutomaton.lean`, `RawSource.lean`, `HardCore.lean`, `Conductor.lean`
* `ProperModulusGram.lean`, `PathCount.lean`, `PG287.lean`, `TerminalBridge.lean`
* `FirstDigit.lean`, `DiameterPrimary.lean`, `Contacts.lean`, `CoreCarry.lean`
* `SquareFirewall.lean`, `StatusCarry.lean`, `TransferMatrix.lean`, `PrimeResonance.lean`
* `SC287Firewall.lean`, `TranslatedRows.lean`, `MandatoryDeep.lean`, `MandatoryDecomp.lean`
* `Ledger.lean`, `AxiomAudit.lean`

## 7. Bottom line

The repository now ends at the current frontier:

`PG287` (OPEN) → `PG287_implies_no_tail_source` → `finite_exclusion_and_PG287_imply_erdos287`
→ original #287.

The only open research owner is the proper-modulus Gram capacity PG-287, together with:
* the external input `PsiLowerBound`;
* the finite range above 4·10⁹, unless the Huang certificate is supplied and replayed.

**ERDŐS #287 REMAINS OPEN.**
