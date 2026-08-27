# Summary of changes for run 0d849f24-cf9b-47cd-9af8-65f6801a897e
## Erdős #287 — V14: exact Vaughan source / prime-modulus two-outer structural spine

**Erdős #287 remains OPEN.** Nothing in this run proves it, nor `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`, smallness of the k = 0 smooth-parity packet, FCL, Gate 1A/1B closure, `WindowPairSupply` for all large M, or the Twin Prime Conjecture.

### Workspace guard
All eight named files (the four singleton V13 files and the four earlier fixed-certificate files) were verified present before any mathematics. `ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does not apply; work resumed in place, append-only.

### Files added
`RequestProject/Erdos287/FordGeneratedDepth.lean`, `AffineVaughanIdentity.lean`, `AffineVaughanPrimeOuter.lean`, `AffineTwoOuterSource.lean`, `AffineTwoOuterCompiler.lean`, `RequestProject/Status/Erdos287VaughanV14Status.lean`, `ERDOS287_VAUGHAN_V14_REPORT.md`. (One file more than the suggested plan: the Part-2 finite arithmetic is kept separate from the Vaughan algebra.)

### Files edited
`RequestProject/Main.lean` — six import lines only. No historical statement was modified.

### What was proved (all sorry-free, kernel-checked)
- **Ford depth (PROVED_FINITE):** `general_ford_depth_le_112`, `fixed_certificate_depth_le_76` (+ factored form), `k0_depth_le_40`, with sharpness witnesses. The three input bounds (s ≤ 20, k ≤ 6, ell ≤ 12) are explicit hypotheses classified as published external input; Ford–Maynard Lemma 7.17 is not reproved.
- **Exact Vaughan identity (PROVED_ALGEBRAIC):** `vaughan_identity_abstract` in any commutative ring from `μ∗1 = ε` and `Λ∗1 = log`, instantiated as `vaughan_identity_exact` in the Dirichlet ring with Mathlib's genuine von Mangoldt/Möbius/log/zeta — no coefficientwise postulate, no axiom. Pointwise divisor-sum form `vaughan_pointwise` with `I1/I2/II`, and `vaughan_pointwise_of_lt` proving the `Λ_{≤V}` term vanishes *from* the size hypothesis.
- **Affine specialisation (PROVED_ALGEBRAIC):** `AffineSign`, `affineNat`, `affineNat_cast` (the ℕ-subtraction firewall for s = −1), `vaughan_affine_pointwise`.
- **Outer router (PROVED_FINITE):** prime vs proper-prime-power partition of the Λ-support, exhaustive and disjoint, plus the rational exponent ledger 1 − (1/3)/2 = 5/6. The analytic prime-power bound is the uninhabited `PrimePowerOuterBound`.
- **Prime-outer source cell:** `AffineVaughanPrimeCell` with only finite factorisation data; elementary consequences (divisibility, p odd, p ≥ 3).
- **Cofactor fold (PROVED_ALGEBRAIC):** `lambdaU_eq_neg_truncMobius` for q > 1, tying the new `d > U` cutoff to the banked `truncMobius` `d ≤ T` cutoff explicitly; `lambdaU_prime = −1`.
- **Support no-go (PROVED_FINITE):** `prime_support_obstruction_to_balanced_convolution` and `vaughan_cofactor_balanced_factorization_impossible`, scoped strictly to the stated balanced-support hypotheses.
- **Prime-modulus orientation (PROVED_ALGEBRAIC):** congruence, unique residue class in `ZMod p` under the explicit invertibility hypothesis, and the two coprimality consequences of the unit shift.
- **Two-outer quotient/packet:** `deltaMuOne` with exact unfolding, and `AffinePrimeModulusTwoOuterPacket` as a finite interface with no analytic field.
- **Determinant-one line (PROVED_ALGEBRAIC):** coprimality from the unit shift, both directions as an iff, and uniqueness of the parameter.
- **Exponent kernel:** strict bound 1/6 < 1 − exp(M) − exp(P), explicit-margin form, and the endpoint equality stated separately.
- **Conditional compiler (PROVED_COMPILER):** `singletonTypeII_of_vaughan_twoOuter`, `smoothParity_of_vaughan_twoOuter`, `parentLeakage_of_vaughan_twoOuter`, keeping the Type-I, prime-power, two-outer and comparison channels separate (error `E_I + C·X^{5/6} + E₂`, never merged).

### Open / blocked
Uninhabited interfaces: `PrimePowerOuterBound`, `AffinePrimeModulusMuTwoOuterInput`, `VaughanTypeIGeneratedKappaInput`, `Affine287ToTwoOuterF3Adapter`. Source-blocked: `Affine287TwoOuterComparisonMatch`, and (unchanged) `K0CellIdentitySource`, `SingletonPacketReduction`. No Gate/F3 provider is inhabited by nomenclature.

### Audit
`lake build` succeeds (8111 jobs, no errors). A repository-wide search of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code** — every match is documentation prose. `#print axioms` is emitted at build time for all principal new theorems by the V14 status file; each reports only a subset of `[propext, Classical.choice, Quot.sound]`.

### Failed targets
None. No statement was found false; the one honest caveat is that the Part-2 depth model `2s + k·ell` is a definition chosen to reproduce the audited constants, and the `76` bound follows from the halved high-prime budget supplied as a hypothesis.

The sixteen hostile checks are answered individually in the docstring of the V14 status file, and the full ledger, source map and theorem list are in `ERDOS287_VAUGHAN_V14_REPORT.md`. Everything is committed and pushed.


# Summary of changes for run 3f26f1c6-6a1d-42e1-a3b1-69c782fc5917
## Workspace check

All six named files were verified present in the working tree before any mathematics was done, so `ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does not apply: `RequestProject/Erdos287/FixedCertificateFordData.lean`, `FixedCertificateThreeError.lean`, `FixedCertificateSmoothParity.lean`, `FixedCertificateOrderCounterguard.lean`, `KummerDegeneracyRouters.lean`, and `RequestProject/Status/Erdos287GoldV12Status.lean`. Work resumed in place on the existing branch.

**Erdős #287 remains OPEN.** Nothing here proves it, nor Gate 1A/1B closure, H8/H9 smallness, the seven-prime Kummer bound, full fixed-certificate leakage, or the Twin Prime Conjecture.

## Source archaeology (A) — key finding

`nu0`, `truncMobius`, `FixedCertificateSmoothParityPacket` (with its `cell_identity` field), the parent leakage compiler, the three-error transference theorem and the balanced-cell counterguard are all present and were reused unchanged. But there is **no** `gStar`, **no** `eps`/`epsilonStar`, and **no Ford factorisation or canonical split** anywhere in the tree, and no coagulation/forbidden-region abstraction. The full object-by-object map is in `ERDOS287_SINGLETON_V13_REPORT.md`.

## B — verdict: `K0_CELL_IDENTITY_SOURCE_STILL_EXTERNAL`

Because the canonical split is not encoded, the `k = 0`, `J = ∅` specialization could only be assumed, not proved. No fake Ford factorisation was created; `cell_identity` is left uninhabited; the missing statement is named exactly as `K0CellIdentitySource` and carried as an explicit antecedent by every downstream theorem.

## What was proved (all sorry-free, kernel-checked)

- **D — rational ledger** (exact ℚ, no floating point): `sigma_pos`, `epsilon_lt_sigma`, `epsilon_lt_sigma_div_three`, `sigma_lt_one_sixth`, `two_sigma_div_three_lt_one`, `two_sigma_lt_one`, `six_sigma_lt_one`, `seven_mul_sigma_gt_one`, plus `nu0R_eq_cast_nu0` tying the ledger to the previously banked ν₀ = 16623/100000, and `admissibleEps_nonempty`.
- **C — `exists_subset_sum_in_typeII_window`**, the purely combinatorial smooth-vector lemma, by the two-case argument. The requested coagulation statement was *not* built: no such abstraction exists in the repository, and the missing object is recorded rather than invented.
- **E — `FordSmoothFragmentCertificate`**, classified `CONDITIONAL_INTERFACE / PUBLISHED_SOURCE`, never inhabited. Lemma 7.17 is not reproved. A clearly-labelled toy witness certifies the specification is *satisfiable*, so no downstream conclusion is vacuous.
- **F — `canonical_singleton_typeII`**, `canonical_singleton_card_eq_one`, `singleton_supersedes_depth_five`. Verdict `CANONICAL_SINGLETON_E45_KERNEL_PASS`.
- **G — `singleton_real_power_window`** and its shifted form: the real-power translation was completed, so the "pending" fallback was not needed.
- **H — `SingletonClass`** (tag only) and `singleton_complement_depth_le_39`, which also certifies the complement equals depth − 1.
- **I — `SingletonGeneratedTypeIIInput`**, uninhabited; Λ, B, W, ξ, κ are abstract parameters, not claimed to be the analytic objects.
- **J — `smoothParity_of_singletonTypeII`, `parentLeakage_of_singletonTypeII`, `primeMassPos_of_singletonTypeII`**: `PROVED_COMPILER / CONDITIONAL_ON_OPEN_ANALYTIC_INPUT`. The three error channels stay separate; `E2` is never merged into the sign region.

## Hostile checks — one downgrade

Check 3 failed as stated and was downgraded honestly. The interface does not force a singleton side to be terminal, so the requested `1 ≤ 2σ/3` route needs an extra hypothesis; it is kept as `fragment_singleton_terminal_contradiction`. The route actually used is the unconditional, strictly stronger `fragment_seven_le_card` (`s + r ≥ 7`, from `1 ≤ (s+r)σ` and `6σ < 1`). Check 6 passes only because the terminal-position convention is recorded explicitly as a field. All ten answers are in the status file's docstring.

## Audit

`lake build` succeeds (8105 jobs). Repository-wide scans find **zero** Lean-code occurrences of `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` — every match is documentation prose. All 41 principal new theorems print `[propext, Classical.choice, Quot.sound]`, emitted at build time by the status file.

## Files

Added: `RequestProject/Erdos287/FixedCertificateSingletonParameters.lean`, `FixedCertificateSingletonFragment.lean`, `FixedCertificateSingletonCompiler.lean`, `RequestProject/Status/Erdos287SingletonV13Status.lean`, `ERDOS287_SINGLETON_V13_REPORT.md`. Edited: `RequestProject/Main.lean` (four import lines only). No historical theorem statement was touched. Everything is committed and pushed.

## Final ledger

`K0-SMOOTH-LEAKAGE-SOURCE45: SOURCE_BLOCKED` · `MU-SPLITTABLE45: PUBLISHED_EXTERNAL_INPUT` · `CANONICAL-SINGLETON-E45: PROVED_ALGEBRAIC` · `SINGLETON-COMPLEMENT-DEPTH39: PROVED_FINITE` · `287-SMOOTH-PARITY-FRAGMENT-TO-SINGLETON-TYPEII45: PROVED_COMPILER` · `287-SMOOTH-PARITY-SINGLETON-GENERATED-TYPEII45: OPEN_ANALYTIC` · `SMOOTH-PARITY: CONDITIONAL_INTERFACE / OPEN_ANALYTIC` · `FCL: OPEN_ANALYTIC` · `ERDOS287: OPEN_ANALYTIC`.

# Summary of changes for run 65719825-9f98-4322-874e-6644b235a32e
## Erdős 287 — V11 finalization + V12 gold reproof / Leanify run

Everything is committed and pushed; `lake build` completes successfully (8101 jobs) with no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe` or `@[implemented_by]` anywhere in Lean code (all matches are documentation prose). Every new theorem prints `depends on axioms: [propext, Classical.choice, Quot.sound]`.

**Terminal status: ERDOS287 OPEN.** Nothing here proves #287.

### Files added this run (append-only; only `RequestProject/Main.lean` was edited, import lines only)
- `RequestProject/Erdos287/FixedCertificateFordData.lean` — Part G1: ν₀ = 16623/100000 as an exact rational, the four branch definitions (two-variable coefficient kept as a parameter, since only its support is given), window arithmetic (`twoVarWindow_nonempty`, `twoVarWindow_width`), the shrink and `shrink_le`, plus the never-inhabited `CertificatePinned` / `PositiveComparisonMargin` predicates.
- `RequestProject/Erdos287/FixedCertificateThreeError.lean` — Part G2: four-region partition with **three separate errors**, `sum_a_P_identity4`, `sum_a_P_lower4` (`≥ (1+C)B − ET − EL − E2 − EM`), `sum_a_P_pos4`, `sum_a_P_pos4_fraction` (constant saving suffices), `transference4_nonvacuous`. N2 is never merged into the sign region.
- `RequestProject/Erdos287/FixedCertificateSmoothParity.lean` — Parts G3/I: `truncMobius`, `truncMobius_prime`, `truncMobius_eq_zero_of_le`, the `FixedCertificateSmoothParityPacket` interface, `smoothParity_prime_normalization`, `smoothParity_missing_source`, and the parent leakage compiler `parent_leakage_of_children` / `parent_leakage_two_children` / `parent_prime_mass_pos`.
- `RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean` — Part G4: `alternating_partial_binomial` (∑_{j≤r}(−1)^j C(k,j) = (−1)^r C(k−1,r)), the balanced-cell model and cut lemma, `balancedCellWeight_ne_zero`, the explicit values at k = 7…12 (−20, −35, 70, 126, −252, −462; the k = 9 value matches the banked 70), and `finite_H8H9_only_census_fails`.
- `RequestProject/Erdos287/KummerDegeneracyRouters.lean` — Part F: the four formalizable strata as predicates, `generic_disjoint_strata`, `generic_not_square`, `generic_not_pmExceptional`, `repeatedRoot_router_nonvacuous`.
- `RequestProject/Status/Erdos287GoldV12Status.lean` — Part J route firewall + `#print axioms` for all new theorems.
- `ERDOS287_GOLD_V12_REPORT.md` — the full A–M report (source map in the requested format, verdicts, file/axiom audit, final ledger). The earlier `ERDOS287_GOLD_V11_REPORT.md` was also committed.

### Firewall finding
Neither the V11 nor the V12 dossier is present in the repository (no `.tex`/`.pdf`, no `H8`/`H9`/Ford-(7.23)/principal-mode/conductor identifiers). All literal source-transcription obligations are therefore reported SOURCE BLOCKED and nothing was reconstructed.

### FINAL LEDGER
```
LCBETA PLACEMENT: REPAIRED
LOG-COFACTOR-ASYMPTOTIC287: KERNEL PASS
FIXED-CERTIFICATE287-PIN: SOURCE BLOCKED
FIXED-CERTIFICATE-TRANSFERENCE287: KERNEL PASS
FIXED-CERTIFICATE-SMOOTH-PARITY PACKET: SOURCE BLOCKED
FINITE-H8/H9-ONLY-CENSUS: FAIL (counterguard compiles)
HIGH-ORDER COUNTERGUARD: KERNEL PASS
QUADRATIC-KUMMER FINITE COMPILER: KERNEL PASS
ROOT-STABILIZER ALGEBRA: KERNEL PASS
WEIL / INTERVAL COMPLETION: EXTERNAL INTERFACE
SEVEN-PRIME EXPONENT LEDGER: KERNEL PASS
KUMMER DEGENERACY ROUTERS: PARTIAL
SEVENPRIME-KUMMER: CONDITIONAL CHILD PASS
H8H9-SOURCE-TO-KUMMER45: SOURCE BLOCKED
287-FIXED-CERTIFICATE-SMOOTH-PARITY45 ANALYTIC ESTIMATE: OPEN
FIXED-CERTIFICATE LEAKAGE COMPILER: KERNEL PASS
287-FIXED-CERTIFICATE-LEAKAGE45 ANALYTIC ESTIMATE: OPEN
GENERATED-(7.23) FIXED-gStar SPECIALIZATION: MAY STILL BE NEEDED
ERDOS287: OPEN
```

```
EXACT FIRST OPEN AFTER THIS RUN:
287-FIXED-CERTIFICATE-SMOOTH-PARITY45 — the two fields of
Erdos287.SmoothParity.FixedCertificateSmoothParityPacket (first the source
obligation `cell_identity`, then the analytic bound).

NEXT MATHEMATICAL ACTION:
Obtain the literal Ford factorisation of G_{g*}(m;n) and prove that its k = 0,
J = ∅ cell equals ∑_{d | n, d ≤ n^(1/2−ε)} μ(d) on the smooth sector, i.e.
inhabit the `cell_identity` field.
```

The Properties table has been updated with the new V11 and V12 deliverables and their statuses.

# Summary of changes for run fbe73b56-3c29-4b1a-926b-1a4159cafede
**Erdős #287 is NOT solved, and nothing in the project claims it is.** All work is committed and pushed; `lake build` passes (8086 jobs) with no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `@[implemented_by]` anywhere, and every new theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. No existing theorem was edited, renamed, weakened or deleted; the full written audit (sections A–AD, the Q1–Q30 matrix, counterguard check and final verdict block) is `ERDOS287_END_TO_END_CLOSURE_REPORT.md`.

**Files added**
- `RequestProject/Erdos287/ProblemStatement.lean` — the exact public predicate `Erdos287Counterexample` (card ≥ 2, all denominators > 1, reciprocal sum 1, all gaps ≤ 2), the **one-way** bridge `toGap2CE`, the junk inhabitant `gap2CE_one` (`A={1}`) showing the historical type is strictly broader, `three_le_max`/`four_le_max`, the ordered-sequence form of the public statement (with `k ≥ 2` derived, not assumed), and two non-vacuity guards.
- `RequestProject/Erdos287/FiniteMasterReduction.lean` — the requested patch: sign-sensitive `PlusSophieWitness` (`M/3 < q ≤ (M−1)/2`, `2q+1` prime) and `MinusSophieWitness` (`M/3 < q ≤ ⌊M/2⌋`, `2q−1` prime), both with `q ≥ 5`, their floor-form equivalences, the master theorem `Erdos287Counterexample → SophieWitness (max A) → False`, the retained `39 ≤ M ≤ 250` sweep, and the new free blocker `maxDivisorPrime_blocker` (hence: no counterexample has a prime maximum, none has `M = 2q`). The hypothesis `q² > M` proposed for that blocker is unnecessary — it follows from `M < 3q`, `q ≥ 4` — so it was dropped rather than carried.
- `RequestProject/Erdos287/FiniteRemainder.lean` — the interval-certificate engine: the certified table `CVal` with `C_le_CVal` (from the banked `C 1 … C 9`), and `Gap2CE.blocker_window`, which turns one certificate into exclusion of a whole interval `[L,U]` of maxima.
- `RequestProject/Erdos287/FiniteRangeExtension.lean` — a chain of 34 certificates: **no counterexample with `3 ≤ M ≤ 4·10⁹`** (previously `39 ≤ M ≤ 250`). All primality is discharged by `norm_num` (largest prime used 1 546 710 859); elaboration ≈ 25 s.
- `RequestProject/Erdos287/ClosureInputs.lean` — `WindowPairSupply M`, proved to be implied by a Sophie witness (so the frontier is *weaker* than Sophie–Germain), the non-circular `Erdos287ClosureInputs` (explicit threshold inside the verified range + the supply statement; no field is or implies the conclusion) and the deterministic compiler `Erdos287ClosureInputs → Erdos287Statement`, plus its ordered form.
- `RequestProject/Status/Erdos287EndToEndStatus.lean` — axiom prints for all new theorems and for the preserved V1/V2 bank; also the rational check `1/6 > 1663/10000`.
- Appended to `RequestProject/TrustedBank/R9/Certificate.lean`: `lowSum_eq` (`∑_{j=0}^{4}(−1)^j C(9,j) = 70`) and the cancellation of the two halves — labelled explicitly as binomial identities, **not** `H(n) = 70`.

**Answers to the key questions.** Public statement: represented exactly. `Gap2CE`: broader, not equivalent; only the needed direction is proved. Unconditional finite range: `3 ≤ M ≤ 4·10⁹`. R9 leakage, `H(n)=70`, fresh `c₉`, convolution/multiplicity, `f+δ`, Full-Nine bridge, SW2 shell, Gate-1A/1B, the 287 generated-packet census, generated-(7.23), `C_FM`, Gate-0 Type I, (b.2), N2, prime mass: **not banked / open** — the Ford–Maynard source definitions (Def. 4.3, (7.17), Prop. 7.22, (7.23), Thm 8.3) exist in this repository neither as Lean objects nor as text, so instantiating them would have meant inventing a schematic substitute; nothing was fabricated and no uninhabited interface is used by a proved theorem. `GATE1A_REQUIRED_FOR_287`: unknown (answerable only by the census). No `erdos287` theorem is declared, since the closure structure has no inhabitant.

**Verdict:** `ERDOS287_ALL_INTERNAL_COMPILERS_CLOSED_EXTERNAL_ANALYTIC_INPUTS_REMAIN`. **First exact remaining blocker:** `Erdos287ClosureInputs.supply`, i.e. `∀ M ≥ M₀, WindowPairSupply M` — for every large `M`, two consecutive integers in `[⌈M/2⌉, M]` each divisible by a prime power `> M/10`; an almost-prime-pair statement of Ford–Maynard type, weaker than the Sophie-Germain-type supply used before, and not proved here.

# Summary of changes for run 1453135a-faad-46d6-a201-4be69b18608e
Confirmed receipt of the Erdős-287 material in the project and worked only from it (no external sources were loaded). Both requested runs were carried out proof-first; **#287 is not claimed solved**, and no statement is made anywhere about the supply of Sophie-Germain-type primes for large M. The full written audit is in `ERDOS287_SOPHIE_V1_V2_REPORT.md`.

**Files added** (append-only; no existing theorem edited, weakened or deleted):
- `RequestProject/Erdos287/SophieOptimal.lean` — V1 route
- `RequestProject/Erdos287/SophieBandCompiler.lean` — V1 band
- `RequestProject/Erdos287/V2SophieFinite.lean` — V2 finite/top-layer route
- `RequestProject/Erdos287/V2SophieBand.lean` — V2 band compiler
- `RequestProject/Erdos287/V2BandSupplyChecks.lean` — maximal band + finite sweeps
- `RequestProject/Status/Erdos287V2Status.lean` — status ledger with axiom prints
- `RequestProject/Main.lean` — import lines only

**Source pins (printed before proving).** TL_PIN: `Erdos287.topLayer_congruence` (`Erdos287/TopLayer.lean`), general layer, `Finset ℕ`/`ZMod p` types, cofactors `ordCompl[p] a`, nonemptiness via `1 ≤ topExp A p`, with corollaries `topLayer_card_ne_one`, `topLayer_two_obstruction`, `topLayer_three_obstruction`. ISOLATED_HOLES_PIN: `Erdos287.Gap2CE.holes_isolated` on the closed window `[N,M]`, hole = `∉ A`. No pin failure.

**V1 (threshold route).** `Gap2CE.N_le_of_M_lt_two_mul` (the archive's `e` is literally `Real.exp 1`, so `2 < e` is legitimate — no mismatch); `excludedPP_of_window_two`; `Gap2CE.plus_sophie_blocker`, `Gap2CE.minus_sophie_blocker` (both strictly stronger than the banked `safePrime_blocker`); `band_hypotheses`, `band_exact`, `window_ge_two_of_two_mul_le`; conditional band compiler stated with the supply as an explicit hypothesis (never an axiom). C(2) pin: definition, `C_two` proved by kernel `decide`, `C_spec` greatest — **C2_PIN_PASS**.

**V2 (finite/top-layer only, superseded inputs avoided).** `Gap2CE.halfRange_min_le` (`N ≤ ⌊M/2⌋`), `topExp_le_one_of_lt_sq`, `topHalf_prime_hole`, `q_and_two_mul_q_holes`, `Gap2CE.v2_plus_sophie_blocker`, `Gap2CE.v2_minus_sophie_blocker`, `v2Band_hypotheses`, `Gap2CE.v2_band_plus_blocker` / `v2_band_minus_blocker` / `v2_finite_compiler`, `Gap2CE.v2_exact_compiler`, `no_Gap2CE_M_eq_104`, `sophieWitness_sweep` and `no_Gap2CE_of_M_in_39_250`. The V2 files import only `TopLayer.lean` and `Counterexample.lean`, so neither the `e(N−1)<M` placement nor the `C` threshold is a dependency; both stay in the bank untouched as redundant historical lemmas.

**Repairs found.** (1) `halfRange_min_le` is false without `2 ≤ M`: `A = {1}` satisfies every field of the counterexample structure and there `N = 1 > 0 = ⌊M/2⌋`; the hypothesis was added. (2) The fixed bands `(3/4,4/5)` and `(7/10,24/25)` have real supply gaps — kernel-checked witness `v2Band_supply_gap_152` at `M = 152` — so the finite sweep uses the maximal admissible band `M/3 < q ≤ (M−1)/2`; its small-`M` gap ends at 38 (`not_sophieWitness_35`).

**New unconditional finite consequence.** No gap-≤2 counterexample has `39 ≤ M ≤ 250` (`no_Gap2CE_of_M_in_39_250`), by kernel `decide` over the maximal band. A wider scan was exploratory only and is flagged as unverified in the report.

**Kernel audit.** BUILD: succeeds (8080 jobs). SORRY/ADMIT: none in the new files, none anywhere in `RequestProject`. No `axiom`, `unsafe`, `native_decide`, or `@[implemented_by]`; all finite certifications use ordinary kernel `decide`. AXIOMS: every new theorem reports only `propext, Classical.choice, Quot.sound` (two report less), printed by the status file.

**Verdicts.** V1: `ERDOS287_SOPHIE_FINITE_COMPILER_PASS_WITH_REPAIRS`. V2: `ERDOS287_V2_FINITE_COMPILER_PASS_WITH_REPAIRS`.

**Exact surviving interface** (Lean: `Erdos287.Gap2CE.v2_exact_compiler` / `Erdos287.no_Gap2CE_of_sophieWitness`): for a hypothetical gap-≤2 counterexample with maximum denominator M, the existence of a prime q with M/3 < q ≤ (M−1)/2 and 2q−1 or 2q+1 prime yields a contradiction. This condition is finite and decidable for each fixed M and is verified for 39 ≤ M ≤ 250; nothing is claimed about its validity for large M. All work is committed and pushed.

# Summary of changes for run ca26ff1f-8d7d-4b5e-956c-2175ae3c0a68
**TRUSTED_BANK_DELTA6_PARTIAL_SOURCE_FIELDS_MISSING**

Gate 1A, Gate 1B, ACBV45 / RLS45 / mixed-start NSE, the R9 analytic-mass question and Erdős #287 all remain **OPEN**; nothing in the project claims otherwise. Work was done inside the existing Lean project (toolchain and Mathlib pin unchanged). The full report, in the requested A–O format, is `TRUSTED_BANK_DELTA6.md`.

**A. Build status.** `lake build` succeeds (8074 jobs). Archaeology before editing: build succeeded, no sorries, no stale status labels, one long-standing duplicated *definition* (`lcmUpto` / `lcmUpTo`, identical bodies) left as-is and re-flagged.

**B. Files added:** `RequestProject/TrustedBank/Gate1A/{ScaleLedger,RowConservation,AvgJDRInterface}.lean`, `TrustedBank/Gate1B/{CenteredRho,MobiusCollapse,SeparableWeights,StartInjectivity}.lean`, `TrustedBank/R9/Certificate.lean`, `TrustedBank/Erdos287/GoodPrime.lean`, `Challenges/Delta6Interfaces.lean` (open statements only), `Status/Delta6Ledger.lean` (ledger + bibliographic records), `Validation/Delta6HostileTests.lean`, `TRUSTED_BANK_DELTA6.md`. Modified: `Audit/BankStatus.lean` (axiom prints). No existing theorem edited, renamed, weakened or deleted.

**C. New kernel-proved results.** Gate 1A: exact rational scale ledger with `(natural)/(target) = M/H` and the three gaps `1/18, 1/36, 1/24` at V1/V2/V3; M-row conservation `∑‖X‖² = (∑|w|²)(∑‖x‖²)` with invariance under permutation, unitary maps, direct-sum relabelling and unit-modulus diagonals (establishing only that reorganisation does not erase the row L² mass); AVG-JDR closure as a *conditional* theorem. Gate 1B: the centered identity `ρ(dp) = ρ_d ρ_p + ρ_d/p + ρ_p/d` for coprime d,p; `μ(q/p) = −μ(q)` for squarefree q; the clean collapse to `−μ(q)Λ♯(q)` for product-separable weights; SOURCE-MMD on a clean cell; `SeparableWeightDecomposition` with cost inheritance; same-start injectivity. R9: `∑_{j=5}^{9}(−1)^j C(9,j) = −70` and hence certificate value `70·g(∅)` under the supplied formula. Erdős #287: `GoodPrime`, Good Prime Exclusion, the adjacent good-factor blocker, and the finite (abstract-J) log-cofactor blocker.

**D. Repaired / false statements.** None of the new statements was false. Three deliberate counterexamples are banked and each forces a hypothesis: non-coprime ρ-pairs (d=p=2), the repeated-prime sector (q=4) for the Möbius collapse, and a mixed-start collision showing `T < u` does not give a cross-start diagonal (so mixed-start stays open).

**E. Axioms.** Every new theorem reports only `propext, Classical.choice, Quot.sound` (one reports only `propext`; the C(1..8) certification still reports none). A full scan finds no `sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`, `native_decide` or `@[implemented_by]` anywhere.

**K. Source fields missing** (never invented, always hypotheses or empty specification records): the Gate-1A source identity `Ctilde = H·S + negligible`, the actual nonseparable source weight (`SourceMMDRequirements`, no inhabitant), and the exact Ford `H_g` formula.

**M/N/O — first remaining inputs.** Gate 1A: the authoritative source identity, then SOURCE-AVG-JDR itself. Gate 1B: a separable decomposition (with cost) of the actual smooth weight plus the remaining source fields. #287: the global `LCB_η` adjacent supply with an effective threshold and finite verification below it.

All work is committed and pushed.

# Summary of changes for run 961652a0-7e81-4f59-90e5-e00c79ffb600
**Headline: TRUSTED_BANK_EXTENDED.** Erdős #287, Gate 1A and Gate 1B remain **OPEN**; nothing in the project claims otherwise.

Work was done inside the existing Lean project (toolchain `leanprover/lean4:v4.28.0`, Mathlib rev `v4.28.0`, both unchanged). Full details are in the new `TRUSTED_BANK_AUDIT.md`.

**Archaeology (state before the run).** `lake build` succeeded. The existing Erdős-287 package (18 files under `RequestProject/Erdos287/`, ~130 theorems) was sorry-free except for **three sorries in `RequestProject/Erdos287/Uniform.lean`**. No stale/retracted theorems; one duplicated *definition* (`lcmUpto` in `Universal.lean` vs `lcmUpTo` in `RoughPrime.lean`, identical bodies, confusable names) — left as-is and flagged rather than silently merged.

**The project is now completely sorry-free.** The three remaining sorries were closed: `Erdos287.C_le_lcm_mul_harmonic` (C(j) ≤ lcm(1..j)·H_j), `Erdos287.harmonic_le_nat` (H_j ≤ j), `Erdos287.C_le_U` (C(j) ≤ j·j!). The uniform window-exclusion and forced-hole results that rested on them are now unconditional.

**Banked this run** (all under `RequestProject/TrustedBank/`, all kernel-checked, none importing anything open):
- Bank A `FixedAffine/Basic.lean` — a₁·L₂(n) = a₂·L₁(n) + Δ over any commutative ring, good-prime root transport, and the unit −a₂/Δ sending the two forbidden roots to {0,1}.
- Bank B `FixedAffine/UnitTransport.lean`, `Interfaces/FiniteSumTransport.lean` — unit-multiplication bijectivity, sum/ℓ²-energy invariance, and the exact Kloosterman-shaped reindexing S(A,B;q) = S(Aλ, Bλ⁻¹; q).
- Bank C `Interfaces/ZeroSetTransport.lean` — fixed-unit twists preserve simultaneous zero sets, their cardinalities and weighted sums.
- Banks D+E `Erdos287/BoundedCofactor.lean` — the Bézout parametrisation e·Q − d·P = 1 with the full coprimality package, and the local criterion **admissible ⟺ d·e even**, tested on small examples.
- Bank F `FixedAffine/SingularFactors.lean` — local root counts ν(ℓ) = 1 / 2 and the (ℓ−1)/(ℓ−2) correction (no infinite Euler product).
- Bank G `FixedAffine/CofactorIntensity.lean` — J(n) ≤ J(2) with equality iff n = 2, hence {d,e} = {1,2}.
- Bank H `FixedAffine/SymmetricPacket.lean` — odd-character ± cancellation, instantiated for Dirichlet characters.
- Erdős #287: `Erdos287/CarryTower.lean` (lcm² ∣ ∏a and lcm ∣ ∏ pairwise differences, for reciprocal-sum-1 sets) and `Erdos287/TopLayerConsequences.lean` (generalized fixed-cofactor blocker with every numerical hypothesis explicit).

**Repairs found (section B).** (1) The requested blocker threshold `C(2j−1)` is **not sufficient on its own** — with p = j·q ± 1 and M < 2p the window ⌊M/q⌋ can equal 2j; the repaired theorems use `C(2j)`, and a sharp-window variant keeps `C(2j−1)` under the added hypothesis ⌊M/q⌋ ≤ 2j−1. (2) "lcm² ∣ product" and "lcm ∣ pairwise-difference product" are **false for general finite sets** (A = {2,3}, counterexamples banked) and true under the reciprocal-sum hypothesis, which is the form banked. No statement was weakened.

**Open lines, isolated in `RequestProject/Challenges/`** (Prop-valued targets and interface structures, so no `sorry` and no `axiom`, and never imported by the bank): Gate 1A SB-ν (`SubpolynomialFibre`, plus a proof of its invariance under fixed-unit twists); Gate 1B with the exact one-completion source, β = μ_D·Λ_P linear, the 1/104 margin arithmetic, and the Gate conclusion derived from an explicit convolution-BV interface (NPCF-2C38 recorded dead, not revived); the affine source glue; and a Ford-type blocker-supply dependency specification (Ford–Maynard is *not* postulated as a Lean fact). Note: the authoritative Gate-1A/1B source definitions are not present in this repository, so those challenges are stated against abstract interfaces — this is recorded in the files.

**Audit artefacts.** `RequestProject/Audit/BankStatus.lean` prints axioms for 94 banked theorems — every one reports only `propext, Classical.choice, Quot.sound` (the C(1..8) certification depends on none). `RequestProject/Validation/BankStatements.lean` restates 26 banked results in unfolded form for an independent comparator.

**Final status:** `lake build` completes successfully (8062 jobs); a scan of all Lean sources finds no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `skipKernelTC` or `@[implemented_by]`; new-file linter warnings were fixed at the root. All work is committed and pushed.


# Summary of changes for run 840a104e-1f96-4573-b622-5c483c1e8808
Continued Erdős #287, proof-first and machine-checked. #287 is NOT claimed solved. No prime-distribution / analytic input was used. Both follow-up requests were completed; the whole project builds (`RequestProject.Main`) and every new theorem depends only on the allowed axioms `propext`, `Classical.choice`, `Quot.sound`, with no `sorry`/`axiom`/`unsafe`/`native_decide`.

## Files added
- `RequestProject/Erdos287/NonAdjacentHoles.lean` — the distance-`d` hole investigation.
- `RequestProject/Erdos287/KernelAPBlocker.lean` — the Kernel AP-blocker.
- `RequestProject/Erdos287/NONADJACENT_HOLES.md` — written analysis answering all targets.
- `RequestProject/Main.lean` — imports the two new files.

## Part A — do two holes at distance d > 1 force a contradiction?
Verdict: **No — no non-adjacent-hole contradiction survives.** The gap-≤2 constraint (`holes_isolated`, symbolically `LocallyAdmissible`) is a nearest-neighbour rule whose only forbidden pattern is two *adjacent* holes; that is exactly why the existing `blockerPair_contradiction` works only at distance 1.

Theorems (all in namespace `Erdos287`):
- `twoHoleWord`, `twoHoleWord_has_two_holes`, `twoHoleWord_locallyAdmissible` (d ≥ 2 admits two holes at distance d — refutes the distance-d claim), `twoHoleWord_one_not_admissible` (d = 1 is the unique local contradiction), `no_nonadjacent_local_contradiction`, `distance_band_admissible` (covers the whole band d ∈ {2,…,246}).
- Stronger variants, all shown compatible: `many_holes_block` + `altWord_block_locallyAdmissible` + `altWord_holes_nonadjacent` (a block of 123 forced non-adjacent holes inside an interval of length 246); `mod3HoleWord` + `mod3HoleWord_locallyAdmissible` + `mod3HoleWord_both_parities` (dense holes in both parity classes); `gcd_controlled_models` (coprime and non-coprime endpoints); `exists_residue_in_interval` and `exists_crt_at_distance` (the CRT mechanism can *produce* two hole-forcing multiples at any prescribed distance d ≥ 1, but for d ≥ 2 they are non-adjacent, so `blockerPair_contradiction` never fires).

Local models (counterexamples) provided: `twoHoleWord` (distance d), `altWord` (one parity / dense block), `mod3HoleWord` (both parities) — each proven `LocallyAdmissible`.

## Part B — the Kernel AP-blocker
Formalized and proved. For a `Gap2CE` with M ≥ 8152 and a prime p, with `qₚ = ceilMod p` and kernel modulus `Qₚ = kernelMod p` (= q₂ for p = 2, else 2·qₚ):
- `Gap2CE.HoleForcing.of_dvd`, `Gap2CE.ceilMod_dvd_kernelMod`, `Gap2CE.one_le_kernelMod`, `Gap2CE.kernelMod_holeForcing`.
- `Gap2CE.AP_prime_kills_holeForcing_add` (the +1 companion of the existing −1 lemma).
- `Gap2CE.kernel_AP_blocker` — no prime r ∈ [N+1, M−1] has r ≡ ±1 (mod Qₚ) (stated as Qₚ ∣ (r−1) ∨ Qₚ ∣ (r+1)); and `Gap2CE.kernel_AP_blocker_modEq`, the same in literal `Nat.ModEq` form. Proof: Qₚ ∣ (r∓1) ⟹ qₚ ∣ (r∓1) so r∓1 is a ceiling hole, r is a prime hole by `primeFree`, giving two adjacent holes, contradiction.

## Status
- Build: succeeds. Placeholders in the new files: none. Pre-existing `sorry`s in the unrelated `Erdos287/Uniform.lean` were left untouched (out of scope). Minor lint warnings in other pre-existing files are unchanged.
- A note on faithfulness: `exists_crt_at_distance` needed the extra hypothesis `1 ≤ d` (without it the statement is false in a degenerate N > M / d = 0 case); the intended use is d ≥ 2.

# Summary of changes for run 04a37366-3621-404e-9539-e5aed97ab049
Formalized the Ceiling–CRT Pairing package and the Large-Ceiling / rough-prime reduction for Erdős #287, proof-first and machine-checked. #287 is NOT claimed solved. No analytic number theory, no Sophie-Germain / BP★ / Chen-P₂ / Bateman–Horn were used.

Files changed:
- `RequestProject/Erdos287/CeilingCRT.lean` (new) — ceiling-modulus package and AP reduction.
- `RequestProject/Erdos287/RoughPrime.lean` (new) — rough-prime top-layer exclusion.
- `RequestProject/Main.lean` — added imports of the two new files.

Definitions added (in namespace `Erdos287`, most under `Gap2CE`): `ceilMod p := p^(topExp A p + 1)` (the ceiling modulus qₚ), `HoleForcing Q`, `isCeilModOfPrime`, `minCeil` (= minₚ qₚ), `APPrimeInInterval`; and `lcmUpTo j := (Finset.Icc 1 j).lcm id`.

Theorems proved (Ceiling–CRT):
- `ceilingMultiples_are_holes` — if p prime, x∈[N,M], qₚ∣x then x∉A (Target 1).
- `exists_crt_adjacent` — CRT interval-residue lemma: coprime Q₁,Q₂≥1 with Q₁Q₂≤M−N give x∈[N,M−1] with Q₁∣x, Q₂∣(x+1).
- `coprimeHoleModuli_CRT_pair` (Target 2/4) — coprime positive hole-forcing moduli with Q₁Q₂≤M−N give a contradiction; alias `coprime_holeForcing_contradiction`.
- `coprime_ceilMod`, `ceilingCRT_contradiction`, and `ceilingCRT_pairing` (Target 3) — for distinct primes p,r: qₚ·q_r > M−N; alias `ceilMod_mul_gt`.
- `atMostOne_small_ceiling` (Target 4, ℕ form: not both qₚ²,q_r² ≤ M−N), `at_most_one_ceilMod_le_sqrt` (√ form), `ceilMod_two_three_gt` (q₂q₃>M−N), `max_ceilMod_two_three_gt_sqrt`.
- `minCeil_isCeilMod`, `minCeil_holeForcing`, `AP_prime_kills_holeForcing`, `AP_prime_kills_ceiling`, `AP_prime_kills_minCeil` (Target 5), `LargeCeilingReduction` (Target 6), `no_Gap2CE_of_APPrime` (optional Target 6).

Theorems proved (rough prime):
- `lcmUpTo_pos`, `num_div_nat_le`, `num_le_j_mul_lcm`, `C_le_j_mul_lcm` (the crude bound C j ≤ j·lcm(1..j)), and `roughPrime_topLayer_empty` — for prime ℓ with ℓ²>M and j=⌊M/ℓ⌋≥1, if ℓ > j·lcm(1..j) then no element of A is divisible by ℓ (reduced to the certified `primePower_window_exclusion` at exponent 1 via the crude bound).

Build status: the project builds successfully (`RequestProject.Main`).

Placeholders: none in the two new files — no `sorry`, `axiom`, `unsafe`, or `native_decide` (the C 0 base case uses ordinary kernel `decide`). Representative theorems were checked to depend only on the allowed axioms `propext`, `Classical.choice`, `Quot.sound`.

No statement was found to be false, so no counterexample was needed. Notes: in `roughPrime_topLayer_empty` the hypothesis ℓ²>M is kept because the problem states it but is not needed by the proof (documented in the docstring); likewise `ceilingMultiples_are_holes` keeps x∈[N,M] as requested though divisibility alone forces the hole. Pre-existing `sorry`s in the unrelated `Erdos287/Uniform.lean` were left untouched (outside this task's scope).

# Summary of changes for run d1ddc5ae-e548-4cee-ae41-d8843d248054
Audited the Chen / P₂ relaxation of the blocker-pair contradiction in the Erdős #287 kernel. Work is proof-first and machine-checked; #287 is not claimed solved. All results build and use only the allowed axioms (`propext`, `Classical.choice`, `Quot.sound`), with no `sorry`/`axiom`/`unsafe`/`native_decide`.

Verdict: No — one side of a blocker pair cannot be relaxed from a prime power to a P₂ (semiprime / controlled almost-prime) while still forcing a hole via the top-layer / prime-power exclusion theorem. The natural relaxation is false.

Files changed/added:
- `RequestProject/Erdos287/ChenP2Audit.lean` (new) — the formal audit.
- `RequestProject/Erdos287/CHEN_P2_AUDIT.md` (new) — the written audit answering Tasks 1–4.
- `RequestProject/Main.lean` — now also imports `ChenP2Audit`.

Task 1 (exact relaxed statements): `IsP2`; `ExcludedP2Naive M q` (the most favourable literal analogue of `ExcludedPP`: `q = p₁·p₂`, product window `⌊M/q⌋`, threshold `C(⌊M/q⌋) < p₁`); the relaxed exclusion primitive `P2ForcesExclusion`; and the relaxed blocker-pair theorem `RelaxedBlockerPair` (one side P₂, other side prime power).

Task 2 (attempt): the exclusion proof (`primePower_window_exclusion`) is intrinsically single-prime — divisibility by pᵉ forces the top p-adic layer, whose numerator is ≤ C(⌊M/pᵉ⌋) yet ≡ 0 (mod p). A semiprime provides no single dominant modulus, so the top-layer congruence has nothing to run against; the relaxation is not provable.

Task 3 (false — concrete configuration): `not_P2ForcesExclusion` refutes the primitive. Witness: A = {2,3,6} with ∑ 1/a = 1 (`p2_witness_sum`), M = 6, semiprime q = 6 = 2·3. Its favourable product window ⌊6/6⌋ = 1 gives C 1 = 1 < 2, so the naive P₂ rule predicts a hole at 6 (`p2_six_excludedNaive`), yet 6 ∈ A, so no hole is forced. `p2_window_illegitimate` isolates the fallacy: the argument only ever legitimately offers an individual prime factor's window ⌊M/pᵢ⌋, and both fail here (C(⌊6/2⌋)=11≥2, C(⌊6/3⌋)=3≥3); the relaxation illegitimately shrinks ⌊M/pᵢ⌋ to ⌊M/q⌋. The only sound way a P₂ forces a hole is when a prime factor is itself an excluded prime power (`P2_excluded_via_prime_factor`), which reduces to the existing prime case and is not a genuine relaxation.

Task 4 (Chen tail): No usable infinite tail. A Chen-type theorem yields infinitely many (prime, P₂) neighbours, but converting them to blocker pairs needs the P₂ side to force its hole (`RelaxedBlockerPair`/`P2ForcesExclusion`), which is false (`chen_no_usable_tail`). The prime side gives one hole, the P₂ side none, so no adjacent double hole arises. Since the P₂ relaxation fails, the sound blocker inputs remain the genuine prime-power / large-prime-factor pairs already certified. (Per the instructions, Bateman–Horn and Sophie-Germain are not needed here; the existing `safePrime_blocker` already handles the genuine large-prime case.)

Build: succeeds (`RequestProject.Main`, 8040 jobs). Pre-existing lint warnings in other files are unchanged; the new file is warning-free.

# Summary of changes for run a1eae949-bf51-4fea-812e-515df0bc4c32
Completed the requested audit of the "Fable SFT / follower-graph" proposal for Erdős #287 (no claim that #287 is solved), backing every conclusion with machine-checked Lean.

Verdict: Fable's SFT schema matches the certified kernel only partially. The kernel splits into a genuinely local (radius‑1 SFT) *gap layer* and an essentially *non‑local* arithmetic layer that depends on the global parameters N, M, q = pᵉ, ⌊M/q⌋ and the top‑layer maximum. A fixed finite alphabet with a scale‑invariant local rule captures the gap layer but not the arithmetic layer, so the literal SFT schema is not valid for the whole kernel.

First mismatch: the exclusion rule is not scale‑invariant and the alphabet is not finite. The same prime power q = 2 is excluded at M = 3 but not at M = 4 (`excludedPP_three_two` vs `not_excludedPP_four_two`), and the residue modulus ranges over all primes (`modulus_alphabet_unbounded`).

New files:
- `RequestProject/Erdos287/SFTAudit.lean` — formalizes the audit. Local layer: `Cell`, `LocallyAdmissible`, `Gap2CE.word`, `word_eq_hole_iff`, `Gap2CE.word_locallyAdmissible` (the gap constraint IS a nearest‑neighbour SFT forbidding the block (hole,hole)). Dichotomy (A): `Gap2CE.holes`, `Gap2CE.holes_card_le_A`, `Gap2CE.two_mul_holes_le` (boundedly many holes). Dichotomy (B): `altWord`, `altWord_periodic`, `altWord_locallyAdmissible`, `altWord_has_hole` (the local subshift has periodic "fakes", so local rules alone cannot refute a counterexample). Non‑locality obstructions: `modulus_alphabet_unbounded`, `excludedPP_three_two`, `not_excludedPP_four_two`.
- `RequestProject/Erdos287/SFT_AUDIT.md` — the written audit answering Tasks 1–4, including the recommended sound replacement (the interval / blocker‑pair‑chain certificate graph already formalized in `Erdos287/Chain.lean`: `ChainLink`, `chainFrom`, `BlockerChain`, `BlockerChain.refutes`).
- `RequestProject/Main.lean` — now also imports `SFTAudit`.

Task 4 required output:
- Schema match: partial (local gap layer yes; arithmetic layer no).
- First mismatch: scale‑dependence of exclusion + unbounded prime modulus (theorems named above).
- Theorems formalized: all listed above.
- Build: succeeds (`RequestProject.Main`, 8039 jobs).
- Placeholders: none — no `sorry`, `axiom`, `unsafe`, or `native_decide`; all audited theorems reduce to only `propext`, `Classical.choice`, `Quot.sound` (verified).

Note: this turn built on the reusable certificate framework added earlier in the session (`Blocker.lean`, `Fiber.lean`, `Universal.lean`, `BadPrimes.lean`, `Chain.lean`), which is likewise complete and placeholder‑free; the audit's recommended replacement graph is the `Chain.lean` API.

# Summary of changes for run 35c8cb58-6495-4e1c-af75-56e158c4889f
Certified the elementary structural / prime-power-exclusion package for Erdős #287. The project builds cleanly and is free of `sorry`, `axiom`, `unsafe`, and `native_decide`; every result depends only on the allowed axioms (`propext`, `Classical.choice`, `Quot.sound`), and the certified `C` values depend on no axioms at all. #287 itself is NOT claimed solved — the open blocker-pair (BP) input was deliberately left untouched, as requested.

## Files changed
- `RequestProject/Main.lean` — now imports the whole package (previously just options).
- `RequestProject/Erdos287/Defs.lean` (new) — definitions.
- `RequestProject/Erdos287/Cnum.lean` (new) — the numerator bound `C`.
- `RequestProject/Erdos287/TopLayer.lean` (new) — targets 1–2.
- `RequestProject/Erdos287/Window.lean` (new) — target 4.
- `RequestProject/Erdos287/Counterexample.lean` (new) — target 5.
- `RequestProject/Erdos287/PrimeFree.lean` (new) — targets 6–7.

## Theorems proved (by task target)
Definitions: `topExp`, `topLayer` (with `mem_topLayer`, `topLayer_subset`); `addF`, `sumP`, `numOf`, `denOf`, `C` (a kernel-reducing list computation).

1. `topLayer_congruence` — ∑ over the top p-adic layer of the mod-p inverse cofactors is 0 in `ZMod p`.
2. `topLayer_card_ne_one`; `topLayer_two_obstruction` (p ∣ m₁+m₂); `topLayer_three_obstruction` (p ∣ m₁m₂+m₁m₃+m₂m₃).
3. Bridge `sumP_spec`, `numOf_eq_num` (links the computation to `Rat.num`); explicit values `C_one…C_eight` and bundled `C_values` proving `C(1..8) = (1,3,11,25,137,137,1019,2143)` by kernel `decide`; `C_seven_witness` verifying `C 7 = 1019` is attained by `{1,2,3,4,5,7}` (via `norm_num`); plus faithfulness `num_le_C`, `C_attained`, `C_spec` (`IsGreatest`), and `C_mono`.
4. Helper `dvd_num_of_sum_inv_zero`; `primePower_window_exclusion`.
5. `Gap2CE` structure with `N`, `M`, `N_mem`, `M_mem`, `mem_Icc`, `holes_isolated`, `exp_lower` (e·(N−1) < M), `exp_upper` (M ≤ e²·(N+1)), and `N_gt_M_div_eight` (M ≥ 97 ⇒ M < 8·N, i.e. N > M/8).
6. `Gap2CE.primeFree` — for M ≥ 8152, no denominator is prime (via `primePower_window_exclusion` with e=1, `C_mono`, `C_seven`, and N > M/8, using (7+1)·C(7) = 8152).
7. `Gap2CE.blockerPair_contradiction` — two consecutive holes in [N,M] are impossible.

## Build / soundness status
- Build: succeeds (only lint warnings remain — see below).
- No `sorry`/`axiom`/`unsafe`/`native_decide`/`admit`. The C-value certifications use ordinary kernel `decide` on a bespoke reducing computation (`Rat` arithmetic does not reduce in the kernel, so a list-based reduced-fraction fold, proven equal to `Rat.num`, is used instead).
- No statement was found to be false, so no counterexample was needed.

## Notes
- `primePower_window_exclusion` keeps the hypothesis `hqM : p^e ≤ M` because the problem states it, but the proof does not need it (documented in its docstring); this yields one `unused variable` lint warning.
- A handful of `unused simp argument` lint warnings remain inside machine-generated proofs; they are informational only and do not affect correctness. Everything else is complete.