# Erdős #287 — Research Bank V24 report: repaired completed-sieve provider and conditional closure

**Erdős #287 remains OPEN.** V24 proves only a CONDITIONAL asymptotic theorem, from explicit
analytic provider interfaces. It constructs NO explicit `M₀`, performs NO finite splice, and
proves NO global #287 theorem. The V16 analytic source-class theorem, the Rosser asymptotic and the
Euler/Mellin asymptotic are NOT re-proved.

Namespace `Erdos287.ResearchBankV24`. Aggregator `RequestProject/Erdos287/ResearchBankV24.lean`.

## Files

| File | Content |
|---|---|
| `RepairedCompletedSieveProvider.lean` | coefficient contract (`SourceDecomposition`, `CountDetermined`, pattern representation, coloured source decomposition, finite-atom → integer transfer, count-determinacy of rounded rough weights), `SourceClassDistributionProvider`, `distribution_error_small`, bundle `RepairedCompletedSieveProvider` (namespace `RepairedProvider`) |
| `RepairedRouteCBaseline.lean` | `LamFam`, `RoundedCellData`, `SieveGeometry`, `SameWeightActualMeasureProvider`, `lamFam_source_decomposition`, **`repaired_routeC_baseline_of_providers`** |
| `ConditionalPairBaseline.lean` | `repaired_uses_frozen_normalization`, `conditional_pair_baseline_after_repair` |
| `ConditionalAsymptotic287.lean` | **`conditional_asymptotic_287_after_positive_sieve_repair`** |
| `FinalFirewalls.lean` | the nine negative statements `fw1_…`–`fw9_…` |
| `Status.lean` | `v24Ledger = v23Ledger ++ v24New`, `v24_final_status`, `v24_global_open` |
| `AxiomAudit.lean` | `#print axioms` for all 52 V24 theorems |

## Principal theorems

### LEAN BANK — the new weight satisfies the V16 coefficient contract
- `RepairedProvider.pattern_representation` — a count-determined rough coefficient is exactly a
  finite combination of cell-pattern indicators.
- `RepairedProvider.coloured_source_decomposition` — `β ⋆ ℓ` (smooth `β` one-bounded, disjoint from
  the rough universe) is `Σ_i c_i g_i` with every `g_i = u_i ⋆ v_i` in the bilinear source class
  (`u_i` one-bounded, carrying the small primes in the FIRST bin; `v_i` one-bounded and rough), and
  `Σ|c_i| ≤ (R+1)^{#cells} 3^R` — from the exact colouring identity and
  `coloured_weight_source_contract` of V22.
- `RepairedProvider.ellRd_countDetermined` — with cell-endpoint rounding `w = wc ∘ cell` and
  monotone cells, `ℓ_rd` depends only on the cell-count vector (induction removing the largest
  atom; `admGen_erase_max`, `cell_max'_le`, `admGen_count`).
- `RepairedProvider.new_completed_weight_matches_V16_contract` and
  **`rounded_completed_weight_matches_V16_contract`** — the ACTUAL
  `Λ_new^+ = μ_E ⋆ β_sm^+ ⋆ ℓ_rd` on `ℕ` satisfies
  `SourceDecomposition Λ_new^+ (E ∪ Psm) Prd ((R+1)^{#cells} 3^R)` (transfer via `push`,
  `push_conv`, `push_pull`). Only the atom bound `R` and the cell data are hypotheses.
- `RepairedRouteCBaseline.lamFam_source_decomposition` — every weight of the family satisfies the
  contract with an `M`-independent mass; `ellRd_congr`.
- `RepairedProvider.small_prime_weight_constructed` — no small-prime provider is needed.

### EXTERNAL PROVIDER (interfaces; never constructed)
- `RepairedCompletedSieveProvider` — bundles ONLY `RosserScalarProvider`,
  `PrimeHarmonicTupleProvider`, `PrincipalEulerProvider`, `HatReferenceApproximationProvider` and
  the inherited V16 `SourceClassDistributionProvider` (linear distribution-error functional,
  uniformly small on the bilinear source class). No finite CRT, positivity, colouring, contract or
  rational fact is a field.
- `SameWeightActualMeasureProvider` — the actual-measure / tensor decomposition
  `Pair/N ≤ M_new(Λ) + |DE(Λ)| + C_t √(E|A-B|²) + 90 + err` with the SAME `Λ` in `M_new` and `DE`
  (role of the frozen V20 `PairDecompositionProvider` for the new weight).

### LEAN CONDITIONAL
- `RepairedProvider.distribution_error_small` — a weight with a bounded source decomposition has
  eventually small distribution error.
- **`RepairedRouteCBaseline.repaired_routeC_baseline_of_providers`** — the bundle + the same-weight
  decomposition + geometry + rounding cells ⟹ the frozen V16
  `RouteCBaselineProvider τ W N (L_ij(F)/I) err`, i.e. `‖B_x‖² = Pair/N ≤ A_C W_F + 90 + err + η`
  eventually for every `η > 0`. The proof picks `S`, then `τ` (V23 `principal_budget_le_A_C`), and
  uses the SAME `LamFam S τ M` for the V16 error (`distribution_error_small` +
  `lamFam_source_decomposition`) and for the principal term; the tensor error is `o(1)` by the hat
  provider.
- `ConditionalPairBaseline.conditional_pair_baseline_after_repair` — the V20 `ThinPairBaselineBound`.
- `ConditionalPairBaseline.repaired_uses_frozen_normalization` — the `N` of the repaired principal
  term satisfies the frozen `S0Contract (S0 τ W) N`.
- **`ConditionalAsymptotic287.conditional_asymptotic_287_after_positive_sieve_repair`** —
  repaired baseline + S0 (from the same-normalization field) / S1 + thin score certificate + exact
  margin check + the frozen consumer chain (V20 `conditional_asymptotic_287_of_baseline` → V17 thin
  consumer → V16 compiler/contact/rigidity/harmonic) ⟹ `∃ M₀, ∀ M ≥ M₀, NoCounterexampleAt M`.
  **LEAN CONDITIONAL ONLY.**

### Firewalls (LEAN BANK / FINITE REGRESSION)
1. `fw1_spectator_square_not_raw_density` — `4/37 ≠ 1/10`;
2. `fw2_signed_coefficients` — negative coefficient with nonnegative divisor sums; monotonicity fails
   without them;
3. `fw3_literal_cell_convolution_multiplicity` — multiplicity `2 > 1` at `143`;
4. `fw4_support_below_three_fifths_no_provider` — `273/500 < 3/5` builds no provider;
5. `fw5_colouring_identity_not_distribution` — the source-class provider fails for a linear error
   functional, so the colouring identity does not prove distribution;
6. `fw6_same_weight_bound_not_V16` — likewise for the same-weight bound vs the V16 theorem;
7. `fw7_score_does_not_construct_baseline` — the pair baseline is falsifiable;
8. `fw8_conditional_asymptotic_no_explicit_M0`;
9. `fw9_explicit_M0_required_for_splice`.

## Final ledger (`Status.v24_final_status`, checked by `decide`)

| Item | Status |
|---|---|
| V16–V20 | FROZEN (LEAN BANK rows preserved verbatim; `v24_preserves_v23_ledger`) |
| Normalized sieve monotonicity | LEAN BANK |
| Spectator-conditioned quadratic domination | LEAN BANK |
| V17 density-invariance shortcut | REPAIRED / RETIRED (mod-11 counterfixture) |
| Rounded rough-sieve finite positivity | LEAN BANK |
| Completed positive weight | LEAN BANK (small-prime Rosser weight constructed; no provider) |
| Exact cell-colouring identity | LEAN BANK |
| Independent coefficient factorization | LEAN BANK |
| Packing/range margins | LEAN BANK |
| Rosser scalar asymptotic | EXTERNAL PROVIDER |
| Principal CRT probability | LEAN BANK |
| Singular-factor finite cancellation | LEAN BANK |
| Principal Euler/Mellin asymptotic | EXTERNAL PROVIDER |
| Exact rational principal slack | LEAN BANK |
| Same-weight signed-principal bound | LEAN CONDITIONAL (finite form LEAN BANK) |
| New weight satisfies V16 coefficient contract | LEAN BANK (algebraic factorization); analytic estimate EXTERNAL PROVIDER |
| Same-weight actual-measure / tensor decomposition | EXTERNAL PROVIDER |
| Repaired Route-C pair baseline | LEAN CONDITIONAL |
| Asymptotic #287 | LEAN CONDITIONAL ONLY |
| Explicit M0 | OPEN |
| Finite splice | OPEN |
| Global Erdős #287 | OPEN |

## Common trust section (V21–V24)

**Base commit:** `ce8a536` ("Initial commit").

**File headers.** The V21–V24 files use ordinary (non-`module`) Lean headers, like the frozen
V16–V20 files they import.

**Build commands (all succeeded):**

    lake build RequestProject.Erdos287.ResearchBankV21
    lake build RequestProject.Erdos287.ResearchBankV22
    lake build RequestProject.Erdos287.ResearchBankV23
    lake build RequestProject.Erdos287.ResearchBankV24
    lake build RequestProject.Erdos287.ResearchBankV21.AxiomAudit   (and V22, V23, V24)
    lake build                                                       (full: 8839 jobs, success)

**Theorem counts / `#print axioms` summary** (every theorem of every V21–V24 file is listed in the
corresponding `AxiomAudit.lean`):

| Bank | Theorems | `[propext, Classical.choice, Quot.sound]` | `[propext, Quot.sound]` | no axioms |
|---|---|---|---|---|
| V21 | 43 | 40 | 0 | 3 |
| V22 | 106 | 102 | 1 | 3 |
| V23 | 53 | 43 | 7 | 3 |
| V24 | 52 | 44 | 4 | 4 |
| **Total** | **254** | 229 | 12 | 13 |

No theorem depends on `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler` or any custom axiom.

**Forbidden-token scan** of all V21–V24 sources and aggregators for `sorry`, `admit`, `axiom`,
`native_decide`, `bv_decide`, `unsafe`, `implemented_by`, `opaque`, `skipKernelTC`,
`trustCompiler`: no occurrence in code. The only textual hits are the words "axiom audit" in the
`AxiomAudit.lean` headers and "constructed without any axiom" in a V22 docstring. Only ordinary
kernel-reduced `decide` is used (ledger lookups, the `143` regression, small finite facts).

**External checker.** `leanchecker` is installed (`/root/.elan/bin/leanchecker`); `lean4checker`
is NOT installed, so it was not used. Commands:

    lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV21
    lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV22
    lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV23
    lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV24

Result: all four runs exited with code 0 and printed no error (run in parallel; fresh re-check of every
declaration in the transitive import closure, including Mathlib and V2–V20).

| Module | leanchecker exit | wall time |
|---|---|---|
| `RequestProject.Erdos287.ResearchBankV21` | 0 | 2136 s |
| `RequestProject.Erdos287.ResearchBankV22` | 0 | 2167 s |
| `RequestProject.Erdos287.ResearchBankV23` | 0 | 2141 s |
| `RequestProject.Erdos287.ResearchBankV24` | 0 | 2201 s |

**Comparator.** `lake comparator` reports `error: unknown command 'comparator'`:
comparator not installed. It was not emulated.

**Append-only git audit.** `git diff --name-status ce8a536 HEAD` lists only `A` (added) entries:
the 41 V21–V24 Lean files (37 module files and 4 aggregators) and the four reports. No V2–V20 file was modified, `ARISTOTLE_SUMMARY.md` is unchanged, and no historical
report was rewritten.

Added files (`git diff --name-status ce8a536 HEAD`, all status `A`):

```
A	ERDOS287_RESEARCH_BANK_V21_REPORT.md
A	ERDOS287_RESEARCH_BANK_V22_REPORT.md
A	ERDOS287_RESEARCH_BANK_V23_REPORT.md
A	ERDOS287_RESEARCH_BANK_V24_REPORT.md
A	RequestProject/Erdos287/ResearchBankV21.lean
A	RequestProject/Erdos287/ResearchBankV21/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV21/ConditionalDensity.lean
A	RequestProject/Erdos287/ResearchBankV21/DensityCounterfixture.lean
A	RequestProject/Erdos287/ResearchBankV21/FiniteSieveSetup.lean
A	RequestProject/Erdos287/ResearchBankV21/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV21/NormalizedSieveMonotonicity.lean
A	RequestProject/Erdos287/ResearchBankV21/QuadraticDomination.lean
A	RequestProject/Erdos287/ResearchBankV21/SpectatorStates.lean
A	RequestProject/Erdos287/ResearchBankV22.lean
A	RequestProject/Erdos287/ResearchBankV22/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV22/CellColouring.lean
A	RequestProject/Erdos287/ResearchBankV22/CompletedPositiveWeight.lean
A	RequestProject/Erdos287/ResearchBankV22/ExceptionalPrimeSet.lean
A	RequestProject/Erdos287/ResearchBankV22/FirstForbiddenPrefix.lean
A	RequestProject/Erdos287/ResearchBankV22/IndependentFactorization.lean
A	RequestProject/Erdos287/ResearchBankV22/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV22/PackingRanges.lean
A	RequestProject/Erdos287/ResearchBankV22/PositiveSieveParameters.lean
A	RequestProject/Erdos287/ResearchBankV22/RosserCostProvider.lean
A	RequestProject/Erdos287/ResearchBankV22/RoundedRoughSieve.lean
A	RequestProject/Erdos287/ResearchBankV22/SmallPrimeUpperSieve.lean
A	RequestProject/Erdos287/ResearchBankV23.lean
A	RequestProject/Erdos287/ResearchBankV23/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV23/FullLCMPrincipal.lean
A	RequestProject/Erdos287/ResearchBankV23/GoodPrimeEulerFactor.lean
A	RequestProject/Erdos287/ResearchBankV23/HatApproximationProvider.lean
A	RequestProject/Erdos287/ResearchBankV23/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV23/PrincipalBudget.lean
A	RequestProject/Erdos287/ResearchBankV23/PrincipalCRTMeasure.lean
A	RequestProject/Erdos287/ResearchBankV23/PrincipalEulerProvider.lean
A	RequestProject/Erdos287/ResearchBankV23/SameWeightPrincipal.lean
A	RequestProject/Erdos287/ResearchBankV23/SingularFactors.lean
A	RequestProject/Erdos287/ResearchBankV24.lean
A	RequestProject/Erdos287/ResearchBankV24/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV24/ConditionalAsymptotic287.lean
A	RequestProject/Erdos287/ResearchBankV24/ConditionalPairBaseline.lean
A	RequestProject/Erdos287/ResearchBankV24/FinalFirewalls.lean
A	RequestProject/Erdos287/ResearchBankV24/RepairedCompletedSieveProvider.lean
A	RequestProject/Erdos287/ResearchBankV24/RepairedRouteCBaseline.lean
A	RequestProject/Erdos287/ResearchBankV24/Status.lean
```

