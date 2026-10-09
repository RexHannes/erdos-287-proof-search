# Erdős #287 — Research Bank V10 report (Astra-repaired frontier)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN.**

The repaired Type-II/HB composition is formalized only relative to explicitly
visible analytic providers.

The endpoint-only HB coverage argument is permanently refuted by a formal
counterfixture.

The compatible-cell saving is kernel-level combinatorics, not a Kloosterman
theorem.

The asymptotic pair-coefficient gate is formally composed, but Erdős #287
remains OPEN.

---

## 1. Files (append-only)

All files are new. `git diff --name-status` against the initial commit lists only `A` (added)
entries. No file from V2–V9 (or anywhere else) was modified.

* `RequestProject/Erdos287/ResearchBankV10.lean` (aggregator)
* `RequestProject/Erdos287/ResearchBankV10/`
  `FrozenFrontier`, `TypeIRescaling`, `TypeIRoughness`, `TypeIGroupedCoefficient`, `TypeIProvider`,
  `TypeIICompatibleCells`, `TypeIICoefficient`, `TypeIIHighLow`, `HBSelection`, `HBSupportCoverage`,
  `EndpointCounterfixture`, `WellFactorableCutoff`, `RoughSeedIdentities`, `Providers`,
  `AsymptoticComposition`, `ExponentGate`, `Ledger`, `AxiomAudit` (`.lean`)

Layout differences from the suggested one:

* `RoughSeedIdentities`, `HBSelection` and `HBSupportCoverage` are used as proposed. The following
  were **added**:
  * `Providers.lean`: all analytic provider structures (§C) in one place;
  * `WellFactorableCutoff.lean`: §M;
  * `EndpointCounterfixture.lean`: §J.
* `TypeIProvider.lean` holds the `∑_e T_e` composition and the Type-I provider contract.
* Files do **not** start with `module`. Lean's module system does not allow a `module` file to
  import the non-module V9 files (`cannot import non-module … from module`, checked), so the
  project's existing (non-module) convention is kept.

Namespaces: `Erdos287.ResearchBankV10.<File>`.

## 2. Build

| target | command | result |
|---|---|---|
| V10 (narrow) | `lake build RequestProject.Erdos287.ResearchBankV10` | success, **8177 jobs**, 0 errors, 0 warnings in V10 files |
| V11 (narrow) | `lake build RequestProject.Erdos287.ResearchBankV11` | success, **8186 jobs**, 0 errors, 0 warnings in V10/V11 files |
| full | `lake build` | success, **8681 jobs**, exit 0; 26 warning lines, all in pre-existing files, 0 in V10/V11 |

The only warnings in the logs come from pre-existing files; they are unchanged.

## 3. Axiom audit (§X)

`ResearchBankV10/AxiomAudit.lean` runs `#print axioms` on **all 170 V10 theorems**. We parsed the
build output: across all 170, the union of reported axioms is exactly
`{propext, Classical.choice, Quot.sound}`. There is no `sorryAx`, no `Lean.ofReduceBool`, no
`Lean.trustCompiler` and no custom axiom.

We scanned the new files for `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `bv_decide`,
`opaque`, `implemented_by` and `debug.skipKernelTC`. They appear only inside comments/docstrings
and in the `#print axioms` commands. The only decision procedure used is ordinary kernel `decide`,
on fixed finite propositions: small residue counts, ledger rows, `divisorsAntidiagonal 3`.

## 4. Principal theorems and semantic audit (§W)

For each item below: **Lean** is the statement (abridged only by omitting universe/implicit
binders), **Informal** is what it means, **Equiv.** says whether the Lean statement is faithful
to the intended claim, **Ext.** lists the external assumptions, and **Not** says what it does not
prove.

### §B Frozen firewall — `FrozenFrontier`
* `frozenV9Bank_holds : FrozenV9Bank`.
  * `FrozenV9Bank` is the conjunction of the exact statements of these V9 theorems:
    `Gates.gate_margin`, `AsraCRT.clean_main_modulus`, `AsraZeroMode.centred_kernel_sum_zero`,
    `Gates.gate_145_38` and `Splice.splice`.
  * Equiv.: yes. The proof is a tuple of the V9 proof terms; nothing is reproved.
  * Not: raw/cut joining, pruning, `R10/R00` and the small-total-modulus BV interface have **no**
    exact theorem in V2–V9. They are frozen only as ledger rows (research record, or external
    interface for BV).
* `Ledger.v10_preserves_v9_ledger`: the V9 ledger (embedded verbatim) is a prefix of `v10Ledger`,
  and every V9 row keeps its name, status, evidence and epoch.
* `Ledger.v10_no_reclassification`: `∀ r ∈ v9Ledger, ∀ r' ∈ v10New, r'.name = r.name → r'.status = .old r.status`.

### §C Providers — `Providers`
* The provider structures are `ZhengKloostermanInput Kl κ`, `GeneralizedBVInput Δ`,
  `OrdinaryBVInput P E`, `SiegelWalfiszSeedInput Δ`, `SmoothTypeIInput P E Kl κ` and
  `RestoredTypeIIInput P E Kl κ packets`. All are `Prop` structures, not axioms.
* The Type-I and Type-II providers are *reductions*:
  * Type I: `ZhengKloostermanInput → TypeICombinatorialFacts → ∀ b ∈ region, LogPowerSaving (E b)`;
  * Type II: `ZhengKloostermanInput → CompatibleCellFacts → ReciprocalPhaseFacts packets → …`.

  The combinatorial premises are proved here (`typeICombinatorialFacts_holds`,
  `compatibleCellFacts_holds`, `reciprocalPhaseFacts_of_coprime`).
* Dependency checks:
  * The following are all proved false: `ordinaryBV_not_automatic`, `typeI_not_automatic`,
    `typeII_not_automatic`, `zheng_not_automatic`, `gbv_not_automatic` and `sw_not_automatic`.
    Each is refuted by an explicit bad error (`X²`) or kernel (`Kl(c) = c`).
  * Hence no provider follows from combinatorial (V8/V9) facts: `FrozenV9Bank` holds, while the
    providers fail for these models.
  * The `*_zero` theorems show each provider is satisfiable in the zero model.
* `seed_aggregate_of_SW`: the pointwise SW bound implies log-power saving of
  `∑_{q ≤ (log X)^B} |Δ(q, a(q), X)|`. This is a genuine elementary proof.

### §D Type-I `e`-rescaling — `TypeIRescaling`
* `rescale_product : (M / e) * (e * N) = M * N`.
* `betaE e β v = if e ∣ v then β (v / e) else 0`.
* The exact finite statements are all proved:
  * `betaE_support`: support preservation;
  * `betaE_divisor_bound`: `‖β w‖ ≤ τ(w)^k ⟹ ‖β_e v‖ ≤ τ(v)^k`;
  * `betaE_sum`: the bijection on `[1, eV] ↔ [1, V]`;
  * `physical_product_preserved`: `(u/e)(ev) = uv`, together with the box bounds;
  * `reference_term_preserved`;
  * `lattice_card` / `lattice_density`: `#{v ≤ eX : e ∣ v} = X`;
  * `lattice_congruence_iff`, `lattice_set_iff`, `lattice_sum`, `lattice_spacing` and
    `lattice_translate`: the congruence/lattice identity with `u ≡ ē r (mod L)` and spacing `eL`.
* Fixture: `density_diagnostic_2_5_1` (the counts in `[0, 10)` are `1` vs `2`, i.e. densities
  `1/10` vs `1/5`) and `old_transform_rejected`.
* Not: no analytic Poisson summation or Fourier transform is formalized.

### §E Roughness — `TypeIRoughness`
* `bonf_eq` evaluates the truncation exactly: it is `1` if no allowed prime divides `m`, and
  `(-1)^J C(t-1, J)` if `t ≥ 1` allowed primes divide `m`.
* For odd `J`:
  * `lowerBonf_le`: `bonf P J m ≤ roughInd P m`;
  * `le_upperBonf`: `roughInd P m ≤ bonf P (J-1) m`;
  * `upper_sub_lower_eq_shell`: `bonf P (J-1) m − bonf P J m = shell P J m`.
* `shell_modulus_le`: `∏d ≤ z₀^J`.
* `esymm_le` and `shell_reciprocal_le`: `∑_{|d|=J} 1/∏d ≤ s₀^J / J!`.
* `pow_div_factorial_le_exp_bound`: `s^J/J! ≤ (e s/J)^J`.
* `exp_loglog_sq_le_rpow`: `∀ C δ > 0, ∀ᶠ X in atTop, exp(C (log log X)²) ≤ X^δ`. This is proved,
  so no provider is needed for it.
* Unit condition: `allowedPrimes z₀ L` = primes `≤ z₀` not dividing `L`.

### §F Grouped coefficient — `TypeIGroupedCoefficient`
* `GroupedCoeff` has a single field `coeff : CoeffIndex → ℂ` (plus a unit bound). By its type it
  cannot take a `SpectralIndex`.
* `GroupedCoeff.lift_spectral_invariant`.
* `root_removed_in_abs`: `‖∑ ρ(o) a(i) K(i,s)‖ = ‖∑ a(i) K(i,s)‖` when `‖ρ(o)‖ = 1`.
* `root_depending_on_inner_not_removable`: the removal fails if the root factor depends on the
  inner variable.
* Negative fixture: `not_factorsThrough_of_depends` and `spectralDependent_fails_interface`.

### §G Compatible cells — `TypeIICompatibleCells`
* `compatibleAlpha_card_eq_d : 0 < K → (compatibleAlpha K d n₁).card = d`, where
  `compatibleAlpha K d n₁ = {α < K d : α ≡ n₁ (mod K)}`.
* `compatibleAlpha_card_eq_d_int`: the same with `K = |k|`, `k ≠ 0` and `d = C q₁ q₂`.
* Hostile fixtures:
  * `old_count_fails_2_3`: the count is `3`, not `6`;
  * `old_count_fails`: for every `K > 1` and `d > 0`, the count is `≠ K d`.
* `detector_n2_determined` (detector geometry), `outer_cell_ratio` (`(K d)/count = K`), and
  `outer_total_comparison` / `outer_total_uniform`.
* Not: this is **not** a Kloosterman estimate.

### §H Type-II coefficient — `TypeIICoefficient`
* `indexMap x = (C q₁ n₂ n₂', q₂, a k (h n₂' − h' n₂))`.
* `grouped S φ : ℤ×ℤ×ℤ → ℂ` is the fibre sum. Its type contains neither `c` nor `r₁`
  (`SpectralVars` is a separate type).
* `grouped_factorization`:
  `∑_{x∈S} φ x · F(indexMap x, σ) = ∑_{t ∈ S.image indexMap} grouped S φ t · F(t, σ)`.
* `u_coprime_v`, `exists_reciprocal`: the reciprocal `ū (mod v)` exists under the packet
  coprimality hypotheses.
* `w_ne_zero_iff`, `w_eq_zero_iff`.
* Kloosterman bounds stay external.

### §I High/low-H — `TypeIIHighLow`
* Exact layer:
  * `collision_identity`: `∑_t |fibre t|² = #{(x,y) : f x = f y ∧ P(f x)}`;
  * `collisions_split`;
  * `norm_sq_le_collisions` / `normSqNonzero_le`: `‖B^{≠0}‖₂² ≤ #collisions(w≠0)` for unit weights.
* Divisor factor: the explicit real parameter `Dmult`.
* Envelope (hypothesis): `HighHCountEnvelope`.
* `highH_norm_bound`: `‖B^{≠0}‖₂² ≤ Dmult (Q⁻²N²H² + KNH³ + N²H + KNQ²H²)`.
* `wZero_count_le`: `#{h n₂' = h' n₂} ≤ H N²`.
* `lowH_w_eq` and `lowH_diag_card` (`= H N`).
* `lowH_cost_identity`: from `P_lo·C Q² = P_hi·H`,
  `(P_lo/P_hi)²·(HN²)/(Q⁻²N²H²) = H/(C²Q²)`.
* `lowH_cost_lt_one` (`H < Q²`, `C ≥ 1` give `< 1`) and `lowH_cost_comparison`.
* Fixtures: `smaller_norm_insufficient` and `wrong_prefactor_fails` (with `P_lo = P_hi` the ratio
  is `Q²/H > 1`).
* Not: the envelope itself (lattice-point counting with `x^ε`) is **not** proved; it is the
  hypothesis `HighHCountEnvelope`.

### §J Endpoint counterfixture — `EndpointCounterfixture`
* `endpointCornerChecks_do_not_cover_support P` holds for **every** admissible `P`, at the point
  `θ = 0, ν = 1/13, s = 1/13 − ζ, r = λ − 1/13 + ζ`. It proves:
  1. the point is inside the well-factorable support bounds;
  2. `r + s > 1/2`, and the point lies outside the BV region;
  3. `1/13 < 1/8`, i.e. the point is outside the checked Case II rectangle;
  4. the affine margin `12ν − 1` is `≥ 0` at all four endpoint corners but `< 0` at the point.
* **Caveat.** The prompt refers to "supplied internal r,s exponents" and the "old second Type-II
  margin", but neither formula appears in the prompt or the project sources. We asked for them
  and received no answer during the run. The `(r, s)` above is the Case II parametrization at
  `ν = 1/13`. The negative margin is proved for an explicit affine functional consistent with
  every endpoint check. This refutes the endpoint-only *argument*, but it is **not** claimed to be
  the historical margin.

### §K HB selection — `HBSelection`
* `hb_selection (D : HBData) : CaseI D.factors ∨ CaseII D.factors ∨ CaseIII D.factors`. It is
  **proved** from the list hypotheses: nonnegative exponents, sum `1`, Möbius factors `≤ 1/4`.
  The length bound `≤ 8` is carried as data but not needed.
* Case III is proved with the precise constants: `7/24 < μ < 4/13` and a partial-product exponent
  `ν ∈ [1 − 3μ, 1/8)` with `ν > 1/13`.
* Limitation: the smooth/Möbius label is an input field. It is the minimal classification the
  proof needs; nothing is recovered from a formal HB identity.
* Counterfixtures: `mobius_bound_needed` (dropping the Möbius bound) and `sum_one_needed`
  (dropping the sum condition).

### §L Coverage — `HBSupportCoverage`
* `CoverageParams`: `0 ≤ θ₀ ≤ 1/1000`, `0 < ε₀ ≤ 1/1000`, `ζ = ε₀/100`, `λ = 7/13 − 3θ₀ − ε₀`.
  `InBV`: `θ + r + s ≤ 1/2 − 10ζ`.
* `caseII_params`: for `θ ≥ 0` and `ν ∈ [1/8, 1/4]` it gives `r* + s* = λ`, the exact ranges of
  `s*` and `r*`, positivity, and `θ + r* + s* > 1/2 − 10ζ`.
* Vertex argument: `affine_ge_min_1d`, `affine_ge_of_vertices` and `GapSystem.covers_rectangle`.
  A decidable vertex certificate for an explicit list of affine gap functionals gives the bound on
  the **whole** rectangle.
* `dStar = min(λ, (1 + 2μ − λ − 7θ)/2 − 10ζ)`.
* `caseIII_overlap`: the overlap has length `2ζ > 0`, and every `r + s` falls in one of the two
  windows.
* `every_box_routed : InBV P b ∨ InTypeI P b ∨ InTypeII P b`.
* **Not reconstructed.** The following were not available in the project sources, and none is
  invented:
  * the explicit repaired Type-II gap functionals and their recorded margins (`1/208`,
    `9/208 − θ₀`, `7/208`, the `g1` bound, `G5 ≥ 19ζ`);
  * the exact Type-I domain condition.

  Once supplied, the margins can be discharged mechanically through `GapSystem.VertexCertificate`
  (decidable) and `covers_rectangle`. Until then the quantitative validity of the Type-I/Type-II
  domains is part of the provider hypotheses.
* The routing theorem implies nothing analytic.

### §M Well-factorability — `WellFactorableCutoff`
* `delta3_wellFactorable_6`, `delta3_truncated_not_wellFactorable_4` and
  `wf_truncation_not_automatic`:
  `¬ ∀ λ D D', D' ≤ D → WellFactorable λ D → WellFactorable (truncate λ D') D'`.
* Data-flow:
  * `truncated_eq_product_cutoff`: exact insertion of `1_{ab ≤ D'}` after a legal factorization;
  * `cutoff_separated_bilinear`: with an (external) `CutoffSeparation`, the truncation equals
    `∑_j (α f_j) ⋆ (β g_j)` (original supports kept, `piece_supported`), up to `ε·#divisor pairs`.
* The Mellin construction is the external `MellinSeparationProvider`.
* Model: `WellFactorable` quantifies over factorizations `R S = D` in `ℕ` (integer model).

### §N Rough seed — `RoughSeedIdentities`
* `rough_eq_zeta_mul : roughInd z = ζ * μ.pmul (smoothInd z)`.
* `moebius_rough_eq : μ.pmul (roughInd z) = μ * smoothInd z`.

  Both are exact identities of Mathlib `ArithmeticFunction ℤ`.
* `rankin_split` (elementary Rankin).
* `RoughSeedSWProvider` is external. `roughSeedSW_zero` and `roughSeedSW_not_automatic` are
  proved.

### §O Composition — `AsymptoticComposition`, `ExponentGate`
* `mtSpecificAsymptotic_of_repairedProviders` takes the following hypotheses:
  * `FrozenV9Bank`;
  * `ZhengKloostermanInput Kl κ`;
  * `SmoothTypeIInput P E Kl κ`;
  * `RestoredTypeIIInput P E Kl κ packets`;
  * `OrdinaryBVInput P E`;
  * `SiegelWalfiszSeedInput Δseed`;
  * `PacketCoprime packets`;
  * `HBDecompositionBound boxes E Δseed aSeed B Total`.

  It concludes
  `MTSpecificAsymptotic P Total ∧ (78/145 < P.lam ↔ 3θ₀ + ε₀ < 1/1885)`.
  * Informal: under the visible providers, the pair-distribution error at level `λ` has
    log-power saving.
  * Equiv.: the analytic content of "`MTSpecificAsymptotic`" is modelled as `LogPowerSaving` of an
    abstract total error `Total`. The link between `Total` and the actual pair sums is the
    hypothesis `HBDecompositionBound`. This is a faithful *interface*, not a formalization of the
    arithmetic sums themselves.
* `mtSpecific_at_repaired_parameters` specializes to `θ₀ = 1/25000 + 1/625000000`,
  `ε₀ = 1/100000`, adding `78/145 < λ` and `145/39 − 2/λ = 52426455/18953756081`.
* `providers_jointly_satisfiable`: the hypotheses are satisfiable, so the theorem is not vacuous.
* `composition_does_not_constrain_counterexamples`.
* `ExponentGate` (exact rationals):
  * `theta0_lt`: `θ₀ < 1/1000`;
  * `loss_lt`: `3θ₀ + ε₀ < 1/1885`;
  * `vartheta_eq`: `ϑ = 4373943711/8125000000`;
  * `vartheta_gt_gate`: `ϑ > 78/145`;
  * `pair_coefficient_gap`: `145/39 − 2/ϑ = 52426455/18953756081 > 0`;
  * `gate_pass_real`, via the frozen V9 `gate_iff`.
* Not: nothing about Erdős #287 itself.

### §P Ledger — `Ledger`
* `v10_frontier` records these statuses:

  | item | status |
  |---|---|
  | zero/raw-cut composition, R10/R00 | FROZEN BANK |
  | smooth Type-I (incl. `e`-rescaling and `∑_e T_e`) | REPAIRED (conditional) |
  | restored Type-II | REPAIRED (conditional) |
  | high/low-H composition | REPAIRED (conditional) |
  | full HB routing | REPAIRED (conditional) |
  | gate `> 78/145` | EXACT PASS |
  | explicit numerical `M_an` | NONE |
  | viable finite architecture | OPEN |
  | asymptotic composition | CONDITIONAL / formally composed (`repairedConditional`) |
  | finite splice | BLOCKED |
  | endpoint-only argument | KILLED |

* `v10_erdos287_open`, `v10_no_closed`.
* `no_ledger_path_closes_erdos287_v10`: the DAG fixpoint from the `PROVED` / `EXACT PASS` /
  `FROZEN BANK` rows excludes Erdős #287, the asymptotic composition, the effective threshold and
  the splice.

## 5. Regression fixtures (§V)

1. `TypeIRescaling.density_diagnostic_2_5_1`, `old_transform_rejected`
2. `TypeIICompatibleCells.old_count_fails_2_3`, `old_count_fails`
3. `EndpointCounterfixture.endpointCornerChecks_do_not_cover_support`
4. `TypeIIHighLow.smaller_norm_insufficient`, `wrong_prefactor_fails`
5. `WellFactorableCutoff.wf_truncation_not_automatic`
6. `TypeIGroupedCoefficient.spectralDependent_fails_interface`
7. and 8. are in V11 (`fixture_asymptotic_vs_effective`, `fixture_analytic_vs_finite`).

## 6. What V10 does not prove

* No Kloosterman, BV, SW, spectral or Type-I/II analytic estimate.
* No explicit repaired Type-II gap formula (not supplied).
* No numerical constant.
* Nothing about the finite architecture.
* **Erdős #287 remains OPEN.**

## 7. Kernel re-check (§Y)

Lean 4.28 ships its checker as `leanchecker` (the successor to the external `lean4checker`).
It is installed in the toolchain and was run through `lake env` after a clean full build.

| command | module | exit | output/warnings |
|---|---|---|---|
| `lake env leanchecker RequestProject.Erdos287.ResearchBankV10` | V10 aggregator (with all its imports) | 0 | none (≈2m44s wall time) |
| `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV11` | V11 aggregator; it imports V10, so V10 is re-checked from scratch too | 0 | none (≈23–30 min wall time) |
