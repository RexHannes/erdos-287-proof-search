# Erdős #287 — post-V87 → V90R subtree report

**Erdős #287 remains OPEN.** Nothing in this subtree proves it.

Subtree: `RequestProject/Erdos287/PostV87V90R/`, namespace `Erdos287.PostV87V90R`,
aggregator `RequestProject/Erdos287/PostV87V90R.lean`.
Append-only: `PostV64V71/`, `PostV71V87/` and `ARISTOTLE_SUMMARY.md` are unchanged
(checked by `audit.sh`, step 4, against the repository's root commit).

## Files

| File | Content |
|---|---|
| `ModelCompatibility.lean` | adapter to the audited `PostV71V87` exact-word model |
| `ContactCycle.lean` | V90 cyclic contact graph, general independence theorem, `G(11,2)`, width ratio |
| `MomentConsumer.lean` | repaired pair-energy (Cauchy) consumer, `C < 11/3` specialisation, integer balancing, sharp finite-mean consumer |
| `AffineCompiler.lean` | affine adjacency identity and integrality, `AffineContactCompiler` data structure (never constructed) |
| `RowRigidity.lean` | `L_H`, `B_H`, bounded-cofactor row rigidity, adjacent empty rows contradiction |
| `OccupancyContact.lean` | occupancy → contact-graph → gap-two contradiction |
| `RetiredRoutes.lean` | V88 facts that are retained, retired consumer architectures, retired cross-scale owner |
| `WidthThree.lean` | explicit analytic provider `WidthThreeMomentProvider`, conditional W3 |
| `NarrowWidth.lean` | `NarrowWidth287`, `NarrowWidthClosureProvider`, tail/global splices, `E287_11_4` |
| `RegressionSuite.lean` | the 10 required semantic regressions |
| `ClosureDAG.lean` | kernel-checked status DAG (48 nodes) |
| `AxiomAudit.lean` | `#print axioms`-style checks run at build time, naming checks, provider-construction audit |
| `audit.sh` | grep checks, a check that historical files are unchanged, the build, 7 negative controls that must fail to compile |

## 1. Model compatibility

The new subtree uses the old model directly: `Erdos287.PostV71V87.ExactWord` (endpoints `a`, `M`,
selected set `A`, gap-two condition, reciprocal identity). It defines no parallel model.

* `counterexample_iff_exactWord` — a `#287` counterexample (finite set, reciprocal sum 1,
  gaps ≤ 2, more than one element) is the same as an `ExactWord` with `1 < a`.
* `ofCounterexample_a`, `ofCounterexample_M` — the endpoints are `min A` and `max A`.
* `ExactWord.exp_lower`, `ExactWord.exp_upper` — the harmonic geometry `e(a−1) < M ≤ e²(a+1)`.
* `omitted_neighbours` — omissions are isolated.

## 2. Status table

| Result | Status | Assumptions | Kernel-proved? | Current role |
|---|---|---|---|---|
| `counterexample_iff_exactWord`, `ExactWord.exp_lower/upper` | Exact | none | yes | model adapter |
| `alpha_contactCycle` : `1 ≤ m`, `2m ≤ r` ⇒ `α(ContactCycle r m) = m` | Exact | none | yes | V90 consumer geometry, general |
| `alpha_G`, `alpha_G_11_2` : `α(G(11,2)) = 3` (useful differences 3..8) | Exact | none | yes | 11-block geometry |
| `G_11_2_four_subsets_have_edge`, `G_11_2_three_indep` | Exact (`decide`) | none | yes | finite regression for the specialisation |
| `width_ratio` : `(r−m)/m = 3 + 1/m` for `r = 4m+1` | Exact | none | yes | width geometry |
| `widthParam_spec` : every `s > 3` has an explicit `m = ⌊1/(s−3)⌋₊+1` with `3+1/m < s` | Exact | none | yes | constructive instantiation |
| `AnnulusBarrier287` (general real-line averaging bound) | Open | — | not formalized | not used: W3 uses the finite cyclic theorem |
| `moment_cauchy` : `(EP)² ≤ EZ·(EP+2EQ)` | Exact | finite nonnegative weights | yes | repaired consumer |
| `expected_occupancy_lower`, `exists_occupancy_of_moment` (existence of a parameter with `Z ≥ m+1`) | Exact | none | yes | repaired consumer |
| `moment_numerical`, `occupancy_of_normalized_moments` : `C < r/m` **and** `μ > mr/(r−mC)` ⇒ occupancy | Exact | stated hypotheses | yes | `C`-normalisation |
| `occupancy_11_3` : `C < 11/3` **and** `μ > 33/(11−3C)` ⇒ some parameter has `Z ≥ 4` | Exact | stated hypotheses | yes | 11-block specialisation |
| `qbal_le_pairs` (integer balancing) | Exact | none | yes | sharp consumer |
| `sharp_mean_consumer`, `exists_occupancy_of_sharp` : `EQ < q_m(EP)` ⇒ some parameter has `Z ≥ m+1` | Exact | none | yes | sharp finite-mean consumer (Jensen step via `qbal_supporting_line`, fully proved) |
| `affine_adjacency` : `n⁺ = n⁻ + 1`; integrality lemmas; `gcd_eq_sub_iff` | Exact | `aᵢ < aⱼ`, `(aⱼ−aᵢ) ∣ aᵢ` | yes | compiler algebra |
| `AffineContactCompiler r m K` (finite gcd compiler existence) | Open | — | structure only, never constructed | compiler input (CRT construction not in repository) |
| `BH_pos`, `selRow_empty_of_bounded_cofactors`, `selRow_eq_empty` | Exact | `p` prime, `p > B_H`, cofactors ≤ H | yes | row rigidity |
| `adjacent_empty_rows_contradiction`, `ContactWitness.false` | Exact | the elementary row hypotheses | yes | row-to-gap-two consumer |
| `false_of_edge`, `occupancy_contact_false`, `moment_contact_false`, `sharp_contact_false` | Exact | a compiler `C` and window control taken as hypotheses (parameters, not providers) | yes | occupancy → contact → contradiction |
| V88: `conductor_replication`, `primePower_replication`, `guardOwner_unique`, `lcm_transfer` | Exact | none | yes | V88 facts that are retained |
| V88: `isolated_omissions_realizable`, `single_grid_realizable`, `even_multigrid_realizable` | Exact (retirement evidence) | none | yes | **Retired**: single-grid / multi-grid overload consumers |
| `exterior_obligations_do_not_combine`, `proximity_density_no_contact` | Exact (retirement evidence) | none | yes | **Retired** closure-first architectures |
| `crossScale_retired_equiv_tail` : `CrossScaleSynchronization287 M0 ↔` tail exclusion | Exact | none | yes | **Retired** owner (overstrong) |
| `WidthThreeMomentProvider s` | Open (explicit provider) | — | never constructed | width > 3 analytic moment theorem |
| `W3_of_provider`, `W3Statement_of_provider`, `W3_counterexample_form`, `W3_family_of_providers` | Conditional | `WidthThreeMomentProvider s` | yes (the implication) | W3 |
| `NarrowWidth287`, `narrowWidth_bounds` (`e(a−1) < M < s·a`) | Exact definition and bound | none | yes | current owner of the narrow chamber |
| `NarrowWidthClosureProvider s` | Open | — | never constructed | `[e,3]` chamber |
| `tail_of_W3Statement_narrow`, `tail_of_W3_narrow`, `tail_of_W3family_narrow` | Conditional | W3 provider(s) + narrow provider | yes (the implication) | tail exclusion |
| `erdos287_of_W3_narrow_finite` | Conditional | W3 provider + narrow provider + `FiniteExclusionBelow` | yes (the implication) | global splice |
| `E287_11_4_Provider s` | Open | — | never constructed | 11-block / 4-occupancy target |
| `E287_11_4_geometry` : `α(G(11,2)) < 4` | Exact | none | yes | consumer geometry only |
| `E287_11_4` : `E287_11_4_Provider s → NarrowWidthClosureProvider s`; `tail_of_E287_11_4` | Conditional | `E287_11_4_Provider` (+ W3 provider for the tail) | yes (the implication) | closes the narrow chamber, conditionally |
| `ClosureDAG` theorems | Exact | none | yes (`decide`) | status bookkeeping |
| Global Erdős #287 | **Open** | — | no | — |

## 3. BANK / exact (kernel-proved, no open assumption)

* **Repaired moment Cauchy consumer.** `pointwise_cauchy` (`P² ≤ Z(P+2Q)` pointwise),
  `moment_cauchy`, `expected_occupancy_lower` (`EZ ≥ (EP)²/(EP+2EQ)`), and the existence theorem
  `exists_occupancy_of_moment`: `(EP)² > m(EP+2EQ)` ⇒ `∃ t ∈ T, w t > 0 ∧ Z t ≥ m+1`. All are
  stated over a finite nonnegative weighted parameter set (`FiniteWeights`), so no measure theory
  is involved.
* **`C < 11/3` with the first-moment condition.** `moment_numerical` (general `r`, `m`: `C < r/m`
  and `μ > mr/(r−mC)`) and `occupancy_11_3` (`r = 11`, `m = 3`: `C < 11/3` and `μ > 33/(11−3C)` ⇒
  four occupied blocks at one parameter). `pairConstant_iff`: for `r = 4m+1`, `C < r/m` is the
  same as `C < 4+1/m`. This is the classical `4+η` pair constant.
* **Sharp finite-mean consumer.** `qbal m n = Σ_{i<n} ⌊i/m⌋` is the minimum pair count of `n`
  items in at most `m` occupied blocks (`qbal_le_pairs`). `qlin` is its piecewise-linear
  interpolation, with the supporting-line lemma `qbal_supporting_line`. From these:
  `sharp_mean_consumer` (`Z ≤ m` everywhere ⇒ `EQ ≥ q_m(EP)`) and `exists_occupancy_of_sharp`.
  The Jensen step is proved, not taken as a provider.
* **Cyclic graph independence theorem.** `alpha_contactCycle`: for `1 ≤ m` and `2m ≤ r`, the
  independence number of `ContactCycle r m` (useful differences `m, …, r−m`) is exactly `m`.
  This is proved for all such `r`, `m`. The upper bound uses an interval Cauchy–Davenport count
  (`card_shiftSet_ge`); the lower bound is the arc `{0,…,m−1}` (`arc_indep`).
* **`G(11,2)`, α = 3.** `alpha_G_11_2`. The independent `decide` regressions are
  `G_11_2_four_subsets_have_edge` (all 330 four-subsets) and `G_11_2_three_indep`.
* **Affine adjacency identity.** `affine_adjacency`: if `aᵢ < aⱼ` and `d = aⱼ − aᵢ` divides `aᵢ`
  (equivalently `d = gcd(aᵢ,aⱼ)`, `gcd_eq_sub_iff`), then `n⁺(t) = n⁻(t) + 1`. The integrality
  lemmas are proved as well.
* **Bounded-cofactor row contradiction.** `BH_pos`. `selRow_empty_of_bounded_cofactors`: if `p`
  is prime, `p > B_H`, and every selected multiple of `p` is `p·j` with `1 ≤ j ≤ H`, then no selected
  element is divisible by `p`. The proof multiplies the reciprocal identity by `L_H·(lcm of the
  rest)` and uses `1 ≤ Σ_{j∈J} L_H/j ≤ B_H < p` together with `p ∣` that sum.
  *Audit note:* the hypothesis `p² > M` from the prose is **not needed** and was dropped, which
  makes the theorem stronger. `adjacent_empty_rows_contradiction`: an empty `p`-row at `n` and an
  empty `q`-row at `n+1` inside `[a, M]` contradict gap-two.
* **Occupancy → contact.** `false_of_edge`, `occupancy_contact_false`, `moment_contact_false`,
  `sharp_contact_false`. They are unconditional in the sense that the compiler and the window
  control enter as ordinary hypotheses about given data. They state what is consumed and assume
  nothing open.
* **V88 algebra that could be reconstructed.** `conductor_replication`,
  `primePower_replication`, `guardOwner_unique`, `lcm_transfer`.
* **Width geometry.** `width_ratio`, `widthParam_spec`.

## 4. CONDITIONAL (the implication is kernel-proved; the input is unconstructed)

* **W3.** `W3_of_provider : WidthThreeMomentProvider s → ∀ W : ExactWord, 1 < W.a →
  P.onset ≤ W.M → s·W.a ≤ W.M → False`. Also `W3Statement_of_provider` (`∃ M_s, …`),
  `W3_counterexample_form` (the same statement for raw `#287` counterexamples `A`), and
  `W3_family_of_providers`. **Level reached:** `WidthThreeProvider s → W3 s` only. The
  provider-free statement `W3 s` is **not** derived, because no inhabitant of
  `WidthThreeMomentProvider s` exists in the project.
  The provider exposes only numerical data: `m`, the width inequality, a compiler on `4m+1`
  blocks, a row bound `H`, an explicit uniform `onset`, and, **for every wide window**
  `(a, M)` (`WideWindow`: `1 < a`, `onset ≤ M`, `s·a ≤ M`, `e(a−1) < M ≤ e²(a+1)`), a
  `WindowMomentData` record. That record contains the finite weights, `μ > 0`, the first-moment
  inequality, the pair-moment inequality, `C < r/m`, the large-first-moment inequality, and
  window control at every weighted parameter.
* **`E287_11_4`.** `E287_11_4 : E287_11_4_Provider s → NarrowWidthClosureProvider s` and
  `tail_of_E287_11_4`. The provider asserts: a fixed compiler on `G(11,2)`, a uniform onset, and,
  for every residual window, one parameter `t` with window control (source window, adjacency
  orientation, row bound, big-prime condition) at which **at least four distinct** macroblocks
  are occupied by prime form values. The consumer combines `4 > α(G(11,2)) = 3` with
  `exists_useful_edge`, `false_of_edge` and row rigidity.
* **Tail / global.** `tail_of_W3family_narrow` (W3 family + `NarrowWidthClosureProvider` ⇒
  `∃ M0, TailExclusion M0`) and `erdos287_of_W3_narrow_finite` (adding
  `FiniteExclusionBelow (max onsets)` ⇒ no `#287` counterexample). These are visibly conditional
  on three open inputs.

## 5. RETIRED

* **Old fixed-depth minor closure route / single-grid and global-overload consumers.** Retired
  by `single_grid_realizable` and `even_multigrid_realizable`: the forced omissions of one grid,
  or of any finite family of even grids, are realised by a gap-two word. So such overload never
  exceeds the unchanged global gap-two capacity.
* **Closure-first failures.** `exterior_obligations_do_not_combine` (individual exterior
  obligations do not combine into a common one) and `proximity_density_no_contact` (proximity plus
  density does not give guard contact). Both are concrete `decide` fixtures.
* **Cross-scale synchronization as a strict intermediate.** `crossScale_retired_equiv_tail`:
  `CrossScaleSynchronization287 M0` is *equivalent* to tail exclusion. It is an overstrong owner
  and has been replaced by `NarrowWidth287`.
* **Obsolete `C < 11/6` "sharp threshold".** Retired. `obsolete_11_6_not_threshold` records the
  fixture. `audit.sh` (check 2) and the DAG theorem `dag_c116_unused` confirm that the constant
  appears nowhere else.

V88 items with no complete statement or proof in the repository are marked **OPEN/INFORMAL**
and were not invented: the full guard-owner architecture beyond `guardOwner_unique`, the
rough/exterior transfer beyond the LCM lemma, and the quantitative global-overload capacity
comparison beyond the realisability theorems above.

## 6. OPEN

* The full source-literal narrow-width / width-> 3 analytic moment theorem
  (`WidthThreeMomentProvider`, i.e. the Bombieri–Vinogradov / BFM / Maynard-type input with the
  `4+η` pair constant).
* The finite gcd compiler existence (`AffineContactCompiler` inhabitant: the CRT prescription
  is not in the repository).
* The `[e,3]` chamber: `NarrowWidthClosureProvider`.
* The `E287_11_4_Provider`.
* The effective onset / finite-bank splice: `FiniteExclusionBelow M0` for the onsets involved.
* The general annulus barrier `AnnulusBarrier287` (not needed downstream).
* Global Erdős #287.

## 7. Semantic audit findings

1. **A word-quantified provider would be tautological** (`wordQuantified_provider_trivial`).
   Moment data indexed by an `ExactWord` would be vacuously supplied, because exact words in the
   range are exactly what is being refuted. The providers therefore quantify over **windows**
   `(a, M)`, which exist beyond every onset (`wideWindow_exists`, `residualWindow_exists`,
   `w3_domain_nonempty`, `e287_domain_nonempty`). With this, the provider is a genuine
   prime-distribution statement and not a restatement of the conclusion.
2. **`p² > M` is unnecessary** for bounded-cofactor row rigidity.
3. **`CrossScaleSynchronization287` is equivalent to the tail**, so it is not a reduction.
4. **W3 needs no hidden synchronization** beyond what the provider states: the occupancy, the
   window control and the moment inequalities all sit at **one common parameter**, and this is
   stated explicitly in `WindowMomentData.scaleControl`.
5. The W3 provider is stated for `3 < s ≤ 7`. Larger `s` follow from `W3Statement.mono`, and for
   exact words `M ≤ e²(a+1)` in any case.

No statement from the prose was found to be false. Only the redundant hypothesis `p² > M` was
removed.

## 8. Regression suite (`RegressionSuite.lean`)

1. `C_lt_11_3_alone_insufficient` — a one-point space with `C = 0 < 11/3` and `Z = 1`: the
   condition `C < 11/3` without the first-moment bound gives no occupancy
   (`singleCount_violates_first_moment`).
2. `obsolete_11_6_not_threshold` (and audit check 2 / `dag_c116_unused`).
3. `crossScale_not_reduction`.
4. `width_exclusion_not_global` — width exclusions alone do not imply the global statement.
5. `fixed_s_not_pointwise_three` — excluding every fixed `s > 3` is not a pointwise bound
   `M/a ≤ 3` at finite `M`.
6. Provider instantiation from `True` / `False.elim` / `IsEmpty` / an empty record: rejected by
   `#audit_providers_v90` (negative controls 3, 4, 5 and 7 in `audit.sh`).
7. `predicate_provider_trivial` versus `windowMomentData_exposes` — a predicate-only record is
   trivially inhabited, while `WindowMomentData` exposes the numerical inequalities.
8. `finite_verifier_not_asymptotic`.
9. `three_blocks_no_contact` — three occupied blocks can be independent in `G(11,2)`, so the
   graph theorem proves geometry only and says nothing about occupancy.
10. `finite_bank_gap` — finite-bank exclusion does not fill an unknown onset gap.

## 9. Closure DAG (`ClosureDAG.lean`)

There are 48 nodes, each with status `exact`, `conditional`, `externalBank`, `open` or `retired`.
The following are kernel-checked by `decide`:

* `dag_acyclic`;
* `dag_exact_closed` and `dag_exact_support` (exact nodes depend only on exact or external-bank
  nodes);
* `dag_conditional_has_open` (every conditional node reaches an open input);
* `dag_no_retired_use` (no retired node has a path into an exact or current node);
* `dag_erdos287_open`, `dag_erdos287_no_decl` and `dag_erdos287_open_support`. The open inputs of
  global #287 are `widthThreeProvider`, `compilerExistence`, `narrowOwner`, `finiteExclusion` and
  `e287Provider`;
* `dag_global_needs_narrow_and_finite`;
* `dag_narrow_is_owner` (the current owner is `NarrowWidth287`, not cross-scale);
* `dag_c116_unused`;
* `dag_proved_have_decls`.

## 10. Trust audit

* `AxiomAudit.lean` runs `#assert_std_axioms_v90` on about 85 principal theorems at build time.
  Each depends only on `propext`, `Classical.choice` and `Quot.sound`: no `sorryAx`, no
  `Lean.ofReduceBool`, no custom axiom. It also runs `#assert_unconditional` / `#assert_conditional`
  on the theorem names, and `#audit_providers_v90`, which fails if any declaration of the subtree
  concludes a guarded provider without a guarded hypothesis, or from a `False` / `IsEmpty`
  hypothesis.
* `audit.sh` covers forbidden tokens (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`,
  `bv_decide`, `implemented_by`, `opaque`, `extern`, `False.elim`, `IsEmpty`, `Inhabited`), the
  obsolete constant, provider construction, unchanged historical files, and the narrow build. It
  also runs **7 compile-fail negative controls**, each of which must be rejected for its expected
  reason: `sorry`, `native_decide`, a `False.elim` provider, an `IsEmpty` provider, an empty
  compiler, a provider-dependent theorem mislabelled unconditional, and a trivial provider.
* Builds and checker: see section 11.

## 11. Build / checker log

* `lake build RequestProject.Erdos287.PostV87V90R`: **succeeds**. This build also runs every
  `#assert_std_axioms_v90` check and `#audit_providers_v90`.
* `lake build` (all default targets, 8990 jobs): **Build completed successfully**, exit code 0.
* `lake env leanchecker --fresh RequestProject.Erdos287.PostV87V90R` (the toolchain's kernel
  re-checker, which replays the whole environment from scratch): **exit code 0**, no errors.
* `bash RequestProject/Erdos287/PostV87V90R/audit.sh`: **AUDIT PASSED**. All 7 negative
  controls were rejected, each for its expected reason.
* No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by` or `opaque` appears
  in the subtree's code. Such tokens occur only in comments and in the negative-control fixtures
  inside `audit.sh`, which must fail to compile.

---

This subtree does not prove Erdős #287. It kernel-verifies the post-V87 finite/combinatorial consumers and the exact implication from the explicit analytic providers to the width reductions. Any unformalized prime-distribution input remains an explicit assumption.
