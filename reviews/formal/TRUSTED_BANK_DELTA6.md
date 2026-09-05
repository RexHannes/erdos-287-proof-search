# ARISTOTLE Δv6 — trusted bank update: audit report

**Headline: `TRUSTED_BANK_DELTA6_PARTIAL_SOURCE_FIELDS_MISSING`.**

Gate 1A is **OPEN**, Gate 1B is **OPEN**, ACBV45 / RLS45 / mixed-start NSE are **OPEN**,
R9's analytic mass question is **OPEN**, and Erdős #287 is **OPEN**.  Nothing in this
repository claims otherwise, and no theorem in `RequestProject/TrustedBank/` depends on
an open analytic statement.  No `axiom` was introduced.

The headline is `PARTIAL_SOURCE_FIELDS_MISSING` because three inputs that the Δv6 brief
asks about are *not present in this repository* and therefore were **not invented**:

* the Gate-1A source identity `Ctilde^{gen}_{r,k,m} = H·S_{r,m}(k) + negligible`;
* the actual (nonseparable) source weight `W(d,p)` and its decomposition;
* the exact Ford-certificate definitions (γ-window and the full `H_g` formula).

Each is carried as an explicit hypothesis of a conditional theorem, or as a
specification record with no inhabitant.

---

## 1. Repository archaeology (state *before* this run)

```
TOOLCHAIN         : leanprover/lean4:v4.28.0        (unchanged)
MATHLIB_REVISION  : rev v4.28.0 as pinned in lake-manifest.json   (unchanged)
BUILD BEFORE EDITS: `lake build` succeeded (8062 jobs)
EXISTING_SORRIES  : none
STALE_STATUS_LABELS : none found; every #287 statement is conditional on a
                    `Gap2CE` structure or on explicit numerical hypotheses
DUPLICATE_DECLARATIONS : one duplicated *definition* only —
                    `Erdos287.lcmUpto` (Universal.lean) vs `Erdos287.lcmUpTo`
                    (RoughPrime.lean), identical bodies; left as-is (merging would
                    silently rewrite existing statements), flagged again here
```

`EXISTING_PROVED` (reused, not re-proved): the Erdős-287 package
(`Erdos287/{Defs,Cnum,TopLayer,Window,Counterexample,PrimeFree,Uniform,Blocker,Fiber,
Universal,BadPrimes,Chain,SFTAudit,ChenP2Audit,CeilingCRT,RoughPrime,NonAdjacentHoles,
KernelAPBlocker}.lean`) and the earlier trusted bank
(`TrustedBank/{FixedAffine,Interfaces,Erdos287}`).  Load-bearing reused items:
`Erdos287.topLayer_congruence`, `Erdos287.primePower_window_exclusion`,
`Erdos287.C_values`, `Erdos287.C_mono`, `Erdos287.ExcludedPP`,
`Erdos287.Gap2CE.blockerPair_contradiction`, `Erdos287.Gap2CE.notMem_of_excludedPP`.

`EXISTING_OPEN_INTERFACES` (unchanged, still open, still not imported by the bank):
`Challenges/{Gate1A_SBNu, Gate1B_SourceOpenedSWYang, AffineSourceGlue,
FordBlockerCompiler}.lean`.

The pinned toolchain was **not** changed.

---

## A. Build status

`lake build` completes successfully (8074 jobs).  The lakefile builds the glob
`RequestProject.+`, so every file listed below is built by a plain `lake build`.

## B. Files modified / added

Added:

```
RequestProject/TrustedBank/Gate1A/ScaleLedger.lean
RequestProject/TrustedBank/Gate1A/RowConservation.lean
RequestProject/TrustedBank/Gate1A/AvgJDRInterface.lean
RequestProject/TrustedBank/Gate1B/CenteredRho.lean
RequestProject/TrustedBank/Gate1B/MobiusCollapse.lean
RequestProject/TrustedBank/Gate1B/SeparableWeights.lean
RequestProject/TrustedBank/Gate1B/StartInjectivity.lean
RequestProject/TrustedBank/R9/Certificate.lean
RequestProject/TrustedBank/Erdos287/GoodPrime.lean
RequestProject/Challenges/Delta6Interfaces.lean      (OPEN statements only)
RequestProject/Status/Delta6Ledger.lean              (data: ledger + bibliography)
RequestProject/Validation/Delta6HostileTests.lean
TRUSTED_BANK_DELTA6.md                               (this file)
```

Modified: `RequestProject/Audit/BankStatus.lean` (imports + `#print axioms` for every
new permanent theorem).  No existing theorem was edited, renamed, weakened or deleted.

## C. New kernel-proved theorems

**Gate 1A — scale ledger** (`TrustedBank.Gate1A`):
`naturalEnergy_sub_targetEnergy`, `missingRatioExp_eq`, `missingRatio_V1`,
`missingRatio_V2`, `missingRatio_V3`, `missingRatio_vertices`, `missingRatio_pos`,
`expH_eq`, `expK_eq`.

**Gate 1A — M-row conservation**: `massSq_nonneg`, `massSq_rowVec`,
`total_massSq_rowVec`, `total_massSq_pos`, `massSq_comp_equiv`,
`massSq_diagonal_unit`, `massSq_sum_type`, `massSq_unitary`,
`total_massSq_reorganisation_invariant`.

**Gate 1A — AVG-JDR closure interface (conditional)**: `normSq_add_le_two`,
`avgJDR_transfer_exact`, `avgJDR_transfer`, `avgJDR_normalized`.

**Gate 1B — centered product algebra** (`TrustedBank.Gate1B`): `rho_sum_period`,
`rho_mul_of_coprime`, `rho_not_multiplicative_of_not_coprime`, `rho_test_2_3_6`,
`rho_test_2_3_5`, `rho_test_4_3_8`, `rho_fail_6_4_12`.

**Gate 1B — Möbius collapse**: `moebius_of_prime_times_squarefree`,
`coprime_div_prime`, `moebius_div_prime`, `mmd_clean_collapse`,
`moebius_prime_sq_eq_zero`, `moebius_div_prime_fails_at_prime_square`,
`moebius_div_prime_test_six`.

**Gate 1B — SOURCE-MMD / separable weights**: `mem_cleanCell`, `sourceMMD_clean_cell`,
`SeparableWeightDecomposition.sum_expand`, `SeparableWeightDecomposition.mmd_cost_bound`,
`productDecomposition_cost`.

**Gate 1B — start injectivity**: `sameStart_injective`, `sameStart_injective_mod`,
`mixedStart_not_diagonal`, `mixedStart_not_diagonal'`.

**R9** (`TrustedBank.R9`): `altSum_eq` (= −70), `altSum_terms`,
`Hg_value_of_formula`, `Hg_value_one`, `Hg_independent`.

**Erdős #287** (`TrustedBank.Erdos287Good`): `GoodPrime.excludedPP`,
`goodPrimeExclusion`, `goodPrime_fibre_empty`, `goodPrime_six_five`,
`goodPrime_six_five_excludes`, `not_goodPrime_six_two`,
`Gap2CE.goodPrime_adjacent_holes`, `Gap2CE.goodPrime_adjacent_blocker`,
`Gap2CE.goodPrime_adjacent_blocker_upper_half`, `Gap2CE.goodPrime_of_window_bound`,
`Gap2CE.logCofactor_finite_blocker`.

**Hostile tests** (`Validation.Delta6`): `row_mass_small_test`, `rho_test_9_2_18`,
`sameStart_small_test`, `synthetic_sum_six`, `synthetic_exclusion_six`,
`synthetic_sum_twelve`, `goodPrime_twelve_eleven`, `synthetic_exclusion_twelve`,
`goodPrime_not_dvd_max`, `goodPrime_not_dvd_min`.

## D. Repaired / false statements

No statement banked in this run turned out to be false, so no theorem header had to be
repaired and nothing was retired.  Three *deliberate* negative results are banked as
counterexamples, and each is the reason a hypothesis appears in the corresponding
positive theorem:

| negative result | what it kills | hypothesis it forces |
|---|---|---|
| `rho_not_multiplicative_of_not_coprime` (d = p = 2, N = 2), `rho_fail_6_4_12` | multiplicativity of `rho` without coprimality | `Nat.Coprime d p` |
| `moebius_div_prime_fails_at_prime_square` (q = 4, p = 2), `moebius_prime_sq_eq_zero` | the collapse in the repeated-prime sector | `Squarefree q` |
| `mixedStart_not_diagonal` (u = 10, T = 3, θ = 5, θ′ = 4) | `MIXED_START_SD45_DEAD` as a corollary of same-start injectivity | mixed start stays OPEN |

Carried over from the earlier audit (unchanged, still valid): the blocker threshold
`C(2j−1)` is *not* sufficient on its own; the banked versions use `C(2j)` or add the
sharp-window hypothesis.

## E. `#print axioms` results

`RequestProject/Audit/BankStatus.lean` prints axioms for every theorem listed in C
(and for the 94 previously banked ones).  Every new theorem reports **only** Mathlib
foundational axioms:

```
propext, Classical.choice, Quot.sound
```

with two stricter cases: `TrustedBank.Erdos287Good.GoodPrime.excludedPP` reports only
`propext`, and the pre-existing `Erdos287.C_values` (the C(1..8) certification) still
reports *no* axioms.  **Project-created axioms: none** — the project declares no
`axiom`, and a full-source scan finds no `sorry`, `sorryAx`, `admit`, `axiom`,
`unsafe`, `native_decide`, `@[implemented_by]` or `skipKernelTC`.

## F. Gate 1A bank update

* Scale ledger formalized in exact rationals: `M = X^{1/3}`, `R = X^a`, `L = X^b`,
  `H = X^{a+2b−2/3}`, `K = X^{1/3−a}`; `(natural energy)/(target energy) = M/H`
  symbolically, with the three vertex gaps `1/18`, `1/36`, `1/24` verified exactly.
* M-row conservation proved exactly, with invariance under permutation, unitary maps,
  direct-sum relabelling and unit-modulus diagonals.  It establishes *only* that
  reorganisation does not erase the row `L²` mass; the file explicitly does **not**
  encode "therefore AVG-JDR is impossible".
* AVG-JDR closure is banked as a **conditional kernel theorem**: the energy bound and
  the source identity are hypotheses.
* Superseded routes (pointwise SB-ν, SRB-only closure, M-SYNC-WEAK as primary target,
  `U^5/U^3` bookkeeping) are recorded as non-controlling in
  `Status/Delta6Ledger.lean`; no correct old proof was deleted.

## G. Gate 1B bank update

* Centered divisibility identity proved exactly over ℚ, with the coprimality hypothesis
  shown to be load-bearing.
* `μ(d) = −μ(q)` for `q = dp` (p prime, d squarefree, coprime), and the clean collapse
  `∑ μ(d)·logW(p)·DW(d)·PW(p) = −μ(q)·Λ♯(q)` for **product-separable weights only**.
  The theorem is *not* extended to arbitrary `W(d,p)`.
* SOURCE-MMD on a clean cell: the `(d,p)` expression equals the `q = dp`
  Möbius-modulus expression, under exactly the hypotheses proved above.
* `SeparableWeightDecomposition` + `mmd_cost_bound`: a nonseparable weight inherits the
  clean reduction with at most the factor `cost` (number of modes).  It is **not**
  asserted that the actual source weight admits such a decomposition.
* `SourceMMDRequirements` records the missing source fields; **no theorem instantiates
  it**.
* Same-start injectivity proved; mixed-start shown not to follow.

## H. R9 bank update

`R9_CERTIFICATE_OBSTRUCTION: FINITE_PROVED` for the binomial part:
`∑_{j=5}^{9} (−1)^j C(9,j) = −70`, hence `H = 70·g(∅)` and `H = 70` under `g(∅) = 1`,
for any functional whose *supplied* formula has that shape — the formula is an explicit
hypothesis, because the exact Ford-certificate definitions are absent here.
`R9_FRACTION45: OPEN_ANALYTIC_INTERFACE`.  Nothing is claimed about positive analytic
mass.  Range guard recorded: `CURRENT_ENGINE_TYPEII_RANGE ≈ up to exponent 1/6`;
`FORD_NU_1_5_CERTIFICATE: EXTERNAL_CANDIDATE / RANGE_COMPATIBILITY_OPEN`.

## I. Erdős #287 bank update

* `GoodPrime M q` and **Good Prime Exclusion** — no denominator of a reciprocal
  representation bounded by `M` is divisible by a good prime, via the banked maximal
  `q`-adic fibre congruence (`primePower_window_exclusion` at exponent 1).
* **Adjacent good-factor blocker** — `x`, `x+1` in the denominator span with good prime
  factors are adjacent holes, contradicting gap ≤ 2.  The literal `M/2 < x` form is
  banked separately; that hypothesis is stated because the brief states it, and is
  documented as unused by the proof.
* **Finite log-cofactor blocker** (abstract `J`) — from `M ≤ 2J·qᵢ`, `qᵢ² > M`,
  `qᵢ > C(2J)` the same contradiction follows (`goodPrime_of_window_bound` supplies the
  window bound `⌊M/qᵢ⌋ ≤ 2J` and `C`-monotonicity).
* `LCB_η` (global adjacent log-cofactor prime supply) and the asymptotic step
  `J ≤ η log M / log log M` are recorded **OPEN**; #287 is not derived from them.

## J. Open analytic interfaces

Stated (never assumed, no inhabitant) in `Challenges/Delta6Interfaces.lean`:
`SourceAvgJDR`, `MixedStartNSE`, `RLS45`, `ACBV45`, `JointAffineCorrelation45`,
`BCrossUniversal`, `LCBeta`, `LogCofactorAsymptoticInterface`.  Metadata recorded:
ACBV45 is **not** currently a direct corollary of the published 5/8-type distribution
results — their coefficient-class hypotheses must be mapped separately.  The retracted
routes are enumerated in `RetractedRoute`.

## K. Source-field-missing items

```
SOURCE_AVG_JDR_SOURCE_IDENTITY : SOURCE_FIELD_REQUIRED
ACTUAL_SOURCE_WEIGHT_MMD       : SOURCE_FIELD_REQUIRED  (SourceMMDRequirements)
FORD_R9_Hg_FORMULA             : SOURCE_FIELD_REQUIRED  (carried as a hypothesis)
```

## L. Updated dependency DAG

Machine-readable in `RequestProject/Status/Delta6Ledger.lean` (`ledger`); summary:

```
GATE 1A   source identity              SOURCE_FIELD_REQUIRED
          M-CONSV                      LEAN_PROVED
          scale ledger / gaps          LEAN_PROVED
          SOURCE-AVG-JDR               OPEN_ANALYTIC
          AVG-JDR -> Gate target       CONDITIONAL_KERNEL_THEOREM
GATE 1B   centered rho identity        LEAN_PROVED
          clean Mobius collapse        LEAN_PROVED
          separable SOURCE-MMD         LEAN_PROVED
          nonseparable cost inheritance LEAN_PROVED
          actual source weight MMD     SOURCE_FIELD_REQUIRED
          same-start SD45 diagonal     LEAN_PROVED
          ACBV45 / mixed-start NSE / RLS45 / B_cross   OPEN_ANALYTIC
R9        finite value 70              CONDITIONAL_KERNEL_THEOREM
          R9 fraction estimate         OPEN_ANALYTIC
          nu = 1/5 compatibility       EXTERNAL_CANDIDATE / OPEN
ERDOS 287 top-layer fibre              EXISTING_BANK (LEAN_PROVED)
          good-prime exclusion         NEW_BANK (LEAN_PROVED)
          adjacent blocker             NEW_BANK (LEAN_PROVED)
          log-cofactor finite blocker  NEW_BANK (LEAN_PROVED)
          log-cofactor asymptotics     OPEN (external)
          global LCB_eta supply        OPEN
          finite completion            OPEN_UNTIL_EFFECTIVE_THRESHOLD
```

## M. First remaining theorem for Gate 1A

Supply the authoritative source identity `Ctilde^{gen}_{r,k,m} = H·S_{r,m}(k) +
negligible` **from the source** (currently absent), then prove
`SourceAvgJDR` for the actual centered operator, i.e. remove the `M/H` gap of
`1/18`, `1/36`, `1/24` at V1, V2, V3.  M-row conservation says this cannot be done by
reorganisation alone.

## N. First remaining theorem for Gate 1B

Exhibit a `SeparableWeightDecomposition` (with a controlled cost) for the *actual*
smooth source weight `W(d,p)`, together with the remaining fields of
`SourceMMDRequirements` (gcd routing, repeated-prime sector, dyadic boundary, unary
`B_D`/`B_P` routing, source normalization).  Until then the clean MMD reduction applies
only to product-separable cells.

## O. First remaining global input for Erdős #287

A proof of the global adjacent supply `LCB_η`: for every sufficiently large `M`, an
`x` in the denominator span such that `x` and `x+1` each carry a prime factor satisfying
the finite blocker hypotheses (`q ≥ M/(2J)`, `q² > M`, `q > C(2J)`).  It must come with
an **effective threshold** plus a finite verification below that threshold; only then
does the banked finite blocker close the argument.

---

**Never claimed anywhere in this repository:** `GATE1A_CLOSED`, `GATE1B_CLOSED`,
`FULL_TYPEII_CLOSED`, `TWIN_PRIMES_PROVED`, `ERDOS287_SOLVED`.
