# Erdős #287 — Research Bank V29: provider classification

INTERNAL #287 RESEARCH PROGRAMME ONLY. **Erdős #287 is OPEN. Explicit M₀ is OPEN. Finite splice is OPEN.**

This table covers every field of `ResearchBankV28.RepairedAnalyticBundle.FinalAnalyticProviders`,
plus every other hypothesis of `ResearchBankV28.PreEffectivityTheorem.pre_effectivity_asymptotic_287_after_full_repair`.
It also lists the providers nested inside those fields. The theorem using every field is
`pre_effectivity_asymptotic_287_after_full_repair`, through `routeC_pair_baseline_after_full_repair`
and `bx_norm_bound` in `ResearchBankV28/FinalPairComposition.lean`. Where a field is used at a more
specific point, that point is named in the `used at` column.

Legend:
- **INTERNAL / EXTERNAL**: the classification rule of task §2.
- **eliminate?**: whether §2 requires the item to be eliminated.
- **V29 outcome**: what happened to the item in this run.

| # | provider_name | exact_statement (Lean, abbreviated only by eliding implicit binders) | used at | INTERNAL / EXTERNAL | current_source | eliminate? | V29 outcome | literal external theorem (if any) |
|---|---|---|---|---|---|---|---|---|
| 1 | `rosser` | `RosserScalarProvider K h F Psm Prd lev X` (fields `density : DimensionOneDensity h K`, `F_rosser`, `F_tendsto_one`, `small`, `rough_unrounded`, `small_nonneg`) | `principal_budget_le_A_C` (V23) inside `bx_norm_bound` | EXTERNAL | V22 `RosserCostProvider` | no | kept in `MinimalExternalAnalyticProviders` | Rosser–Iwaniec dimension-one upper-bound sieve asymptotic (`F(s)=2e^γ/s`, 1≤s≤3), with Mertens-type density hypotheses |
| 2 | `tuple` | `PrimeHarmonicTupleProvider h Prd X wτ` (`rounding : ∀ S>0, ∀ τ>0, ∀ ε>0, ∃ x₀, ∀ x ≥ x₀, costU(rounded) ≤ costU(unrounded) + C_{ν,R} τ + ε`) | `principal_budget_le_A_C` | EXTERNAL (prime harmonic sums / Mertens) | V22 | no | kept (minimal) | Mertens' theorem for `Σ 1/p` over cells (rounding error `O(τ)`) |
| 3 | `euler` | `PrincipalEulerProvider h r Sd LF I (S0 τC W) N Li phiW model` (fields `Zgen, good, excLocal, euler_product, zeta_simple_pole, EA, mellin, mellin_truncation, mixed_derivative, Sall_ne, normalization_agreement : S0Contract (S0 τC W) N, sifted_main`) | `principal_budget_le_A_C`; `normalization_agreement` at `conditional_asymptotic_287_of_baseline` | EXTERNAL (Euler product / Mellin asymptotic, S0 main term). `zeta_simple_pole` is provable (`zeta_simple_pole_available`, Mathlib `riemannZeta_residue_one`) | V23 | no (analytic) | kept (minimal) | Principal Euler/Mellin evaluation of the sifted second moment; S0 asymptotic for the fixed tuple |
| 4 | `hat` | `HatReferenceApproximationProvider Kh EAB` (`nonneg`, `bound : ∃ C ≥ 0, ∃ M₀, ∀ M ≥ M₀, EAB M ≤ C / log M ^ (Kh+26)`) | `hat_approximation_eventually_small` in `bx_norm_bound` | EXTERNAL (tensor approximation estimate) | V23 | no | kept (minimal) | Tensor/hat reference approximation with `log^{-(K+26)}` saving |
| 5 | `di` | `DISpectralProvider (1/1100) DIClass` (`spectral : ∀ K, DIClass K → MaynardAdmissible η K → DIConclusion K`) | `nonzero_branch_small` → `clean_nonzero_derived` | EXTERNAL (Deshouillers–Iwaniec / Maynard spectral estimate). **Caveat:** `DIClass` is an uninterpreted parameter. With `DIClass := False` the field holds vacuously (`di_provider_empty_class`); with `DIClass := True` it is false (`di_provider_full_class_false`). | V27 | no (analytic), but the class needs a definition | kept (minimal), with the caveat | Deshouillers–Iwaniec Kloosterman-sum bilinear bound (Maynard's form), for the literal DI class, which has **no definition in the repository** |
| 6 | `zeroFreq` | `BranchClassBound Us Ur D0` (`linear`, `class_bound : ∀ S, ∀ ε>0, ∃ M₀, ∀ M ≥ M₀, ∀ g, SourceFactorization g (Us S M) (Ur S M) → |D0 M g| ≤ ε`) | `derived_source_class_provider` → `distribution_error_small` | EXTERNAL shape (masked SW / BDH class bound). `D0` is **uninterpreted**. The identification `D0 = physical zero-frequency functional` is INTERNAL and missing. | V28 | the identification should be; the bound should not | kept (minimal); identification recorded missing | Masked Siegel–Walfisz / Barban–Davenport–Halberstam for source-factorized weights. V25's `zero_frequency_localized_bound` gives this form for an explicit `FullSum`, but it is not linked to `D0` |
| 7 | `oneLarge` | `BranchClassBound Us Ur D1` | as 6 | EXTERNAL shape; `D1` uninterpreted | V28 | as 6 | kept (minimal) | one-large HB analytic theorem: **no literal statement with sequence and modulus hypotheses exists in the repository** |
| 8 | `twoLarge` | `BranchClassBound Us Ur D2` | as 6 | EXTERNAL shape; `D2` uninterpreted | V28 | as 6 | kept (minimal) | two-large HB analytic theorem: same situation as 7 |
| 9 | `boundary` | `BranchClassBound Us Ur Db` | as 6 | EXTERNAL shape; `Db` uninterpreted | V28 / V26 `BoundaryBudget` | as 6 | kept (minimal) | product-boundary estimate (V26 union-of-boundary budget) |
| 10 | `nonzero` | `∀ S τ M, NonzeroCleanRealization DIClass M (DEnz M (LamFam … S τ M)) Cnz`. Its fields are clean states `st`; `CleanAdmissible DIClass (1/1100)` (**DIClass membership**); per-state `RepresentationMomentProvider`; the root-mass bound; `DivisorSumProvider Ds C x (1/19000) ε`; **`NonzeroPruningContract`**; the normalization `Nq/d = NU`; and `val = Rnz.re` | `nonzero_branch_small` | **INTERNAL.** It contains clean-state construction, DIClass membership, kernel realization, the pruning identity and the source-to-kernel map. The nested `RepresentationMomentProvider` and `DivisorSumProvider` are external-type divisor bounds. | V28 | **YES** | **NOT eliminated**: moved to `InternalGlueOwner.nonzero`. It holds vacuously for `DEnz = 0` (`nonzero_realization_zero`). | — |
| 11 | `tensor` | `BranchedActualMeasureProvider τC W N model (pref Li phiW N) (LamFam …) (sumDE D0 D1 D2 Db) DEnz EAB Ct err` (`Ct_nonneg`, `decomp : ∀ S τ M, Pair/N ≤ M_new(Λ) + |DE_src(Λ)| + [DE_nz(Λ)]₊ + Ct √|E_AB| + 90 + err`) | `routeC_pair_baseline_after_full_repair` | **INTERNAL.** Actual-measure majorization, i.e. physical pair ≤ upper-sieve majorant = principal + branch remainders. It is a source decomposition; the analytic tensor part is field 4. | V28 | **YES** | **NOT eliminated**: moved to `InternalGlueOwner.tensor` | — |
| 12 | `s1` | `S1Contract (S1 τC W) N muF` (`∀ η>0, ∃ M₀, ∀ M ≥ M₀, μ_F − η ≤ S1 M / N M`) | `conditional_asymptotic_287_of_baseline` | EXTERNAL (first-moment asymptotic, BV-type) | V14/V15 | no | kept (minimal) | Bombieri–Vinogradov-type first-moment evaluation for the fixed tuple |
| 13 | `cert` | `ThinFunctionalCertificate muLo WHi muF (LF/I)` (`μ_lo < μ_F`, `W_F < W_hi`, `0 ≤ W_F`) | `conditional_asymptotic_287_of_baseline` | **FINITE CERTIFIED INPUT** (neither analytic nor internal) | V17 shape, V28 values | isolate | isolated as `FunctionalKernelCertificate`, outside all analytic bundles. It is equivalent to the V28 certificate (`certificate_iff_thin`). | numerical certificate: **no certificate data found in the repository** |
| 14 | `G : SieveGeometry …` | hU, hUs, hUr (the same universes in the principal model and the source class), the disjointness facts d1–d3, and `h < 1` on sieve primes | `bx_norm_bound` | INTERNAL (structural facts about **uninterpreted** universes `E, Psm, Prd`) | V24 | yes, once the universes are defined | NOT eliminated. It remains a theorem hypothesis, because the universes are parameters. | — |
| 15 | `cd : RoundedCellData …` | cell data: monotone cells, endpoints, allocation, atom bound `R` | `lamFam_source_decomposition` | INTERNAL (cell construction for uninterpreted `Prd, wτ, X`) | V24 | yes, once defined | NOT eliminated. It remains a hypothesis. | — |
| 16 | `hLi`, `hphi`, `hWF` | `0 ≤ Li M`, `0 < phiW`, `0 ≤ LF/I` | principal budget | INTERNAL (parameter positivity) | V28 | yes | `hWF` **eliminated**: V30 derives it from the certificate (`C.WF_nonneg`). `hLi` and `hphi` remain, because `Li` and `phiW` are parameters. | — |

## Items listed in task §2 that are **not** provider fields

These are internal, and they were already theorems or definitional identities:

- **normalization matching**: `all_components_same_normalization` and `same_normalization_end_to_end` prove this.
- **auxiliary-weight equality**: `principal_weight_eq_error_weight` and `same_auxiliary_weight_end_to_end` prove this.
- **parameter arithmetic / margin check**: `thin_margin_check_final`, plus `consumer_check_iff` and `consumedMargin_value`.
- **branch coverage**: V26 `branch_trichotomy`, restated as `typeII_coverage`.
- **source decomposition of the weight**: V24 `lamFam_source_decomposition`.

## Summary

- EXTERNAL, kept in `MinimalExternalAnalyticProviders`: items 1–9 and 12. Items 5–9 carry the caveat that their argument (`DIClass`, `D0`–`Db`) is uninterpreted.
- FINITE CERTIFIED INPUT, isolated: item 13.
- INTERNAL and **not eliminated**: items 10 and 11, collected in the one structure
  `ResearchBankV29.ProviderElimination.InternalGlueOwner`. Items 14, 15 and 16 (`hLi`, `hphi`)
  also remain as structural hypotheses on uninterpreted parameters.
- Earliest remaining composition hole (§4 STOP): the `DIClass s.DD.KD` membership inside `CleanAdmissible` for the clean states of item 10. No physical clean state exists, and `DIClass` is undefined.
