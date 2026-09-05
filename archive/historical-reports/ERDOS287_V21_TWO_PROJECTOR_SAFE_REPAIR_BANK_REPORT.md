# ERDŐS #287 — V21 TWO-PROJECTOR SAFE REPAIR BANK REPORT

`3221-TWO-HIGHPROJECTOR-FIVEBOX-SIEVE45`

Append-only continuation of the V20 bank. Nothing in V20 was deleted, rewritten or
silently mutated; `ARISTOTLE_SUMMARY.md` was not modified.

---

## A. Repository baseline

The repository was inspected before any V21 declaration was written.

* Toolchain: Lean 4.28.0 with the pinned Mathlib revision in `lake-manifest.json`.
* Baseline build (V20 head, before V21): `lake build` — **success, 8148 jobs, 0 errors**.
  This confirms the V20 report quoted in the request; the number of jobs is the
  number reported by `lake` for this configuration.
* The V20 principal files named in the request are all present:
  `RequestProject/Erdos287/HighConductorCharacterGram3221.lean`,
  `FiveBoxCharacterFactorization3221.lean`, `ConductorRouter3221.lean`,
  `HighQuotientShiftedGram3221.lean`, `HighConductorSixthMoment3221.lean`,
  `BalancedSevenV20Compiler.lean`, `RequestProject/Status/Erdos287V20Status.lean`,
  `RequestProject/Status/AxiomAuditErdos287V20.lean`.

Namespaces actually used by the V20 material (V21 adapts to them rather than
inventing names): `Erdos287.CharGram3221`, `Erdos287.V20Gram`, `Erdos287.V20FiveBox`,
`Erdos287.V20HHH`, `Erdos287.V20Compiler`, `Erdos287.HighCond3221`,
`Erdos287.V19Compiler`, `Erdos287.Grouping3221`, `Erdos287.PrePoisson3221`.

---

## B. V20 objects preserved

All of the following remain in the repository, unedited, and are *reused* by V21:

`shortMGram`, `autocorr`, `charSrc`, `charSource_variance_eq_gram`,
`inverseSampledVariance_eq_characterGram`, `gram_parseval`, `separateL2_compiler`,
`mem_highSet_iff_lt_conductor`, the conductor router, the separate-`L²` death
certificate, the Burgess capacity firewall, `HighQuotientFiveBoxShiftedGram3221Input`,
the sixth-moment bridge, and the same-`B0` comparison firewall
(`MuLogComparisonAtCutoff`, `comparison_cutoff_must_match`).

The V20 controlling compiler `logVar_of_four_channels` is kept as historical
infrastructure; V21 adds `logVar_of_twoHighProjectorPackage` beside it.

Status recorded in Lean (`RequestProject/Status/Erdos287V21Status.lean`):

* `v20_hhh_route_not_controlling_v21` — V20 HHH representation is
  `VALID / HISTORICAL / NOT CONTROLLING`.
* `v21_twoProjector_route_controlling` — the two-high-projector representation is the
  current controlling *conditional* route.

`HighQuotientFiveBoxShiftedGram3221Input` was **not** deleted: it is marked superseded
as controlling, and its socket remains open.

---

## C. Why the old HHH closure proof was retracted

The old route decomposed the high–high character sum by a conductor-cell
inclusion–exclusion over quotient conductors and then applied a Burgess-type bound
cell by cell. Two defects make it unusable *as a closure proof*:

1. the inclusion–exclusion cells were indexed by quotient conductors that are not a
   partition of the ambient character set actually used by orthogonality, so the
   decomposition carried an unquantified omitted/overlapping cell risk; and
2. the bad-character count that fed the log budget was the heuristic
   `#Bad_q ≪ D·τ(q)`, which is not a proved finite bound in this repository.

`oldHHH_closure_proof_retracted` records the retraction as kernel-checked status data.
The underlying *representation* is not claimed false, and the V20 objects stay.

The V21 replacement needs no quotient conductor and no conductor-cell
inclusion–exclusion: it is a two-variable indicator identity (section D).

---

## D. Two-high-projector exact algebra

File: `RequestProject/Erdos287/TwoHighProjector3221.lean` (namespace
`Erdos287.V21TwoProj`).

One ambient finite character set `ambientSet α = Finset.univ`, one `Bad : Finset α`,
and `highSetOf Bad = ambientSet α \ Bad`. Indicators `badInd`, `highInd` valued in `ℂ`.

Proved:

* `highIndicator_eq_one_sub_badIndicator : highInd Bad a = 1 - badInd Bad a`
* `twoHighProjector_pointwise :`
  `highInd Bad a * highInd Bad b = 1 - badInd Bad a - badInd Bad b + badInd Bad a * badInd Bad b`
* `highHighSum_eq_AA_sub_BA_sub_AB_add_BB : HH3221 Bad K = AA3221 K - BA3221 Bad K - AB3221 Bad K + BB3221 Bad K`

with the four children defined separately as `AA3221`, `BA3221`, `AB3221`, `BB3221`
(full sums over the *same* ambient set, weighted by the appropriate indicators).

No-omission / no-overlap / no-double-counting are proved explicitly and not left to
prose: `high_bad_disjoint`, `high_union_bad`, `high_card_add_bad_card`,
`twoProjector_no_double_counting`, `sum_eq_indicator_sum`, `HH3221_eq_indicator_sum`.

### Pre-projector variance reconstruction (section 3 of the request)

The finite expression was recovered from the actual V20 character source, not from
memory. `gramKernel` and `preProjectorVariance` reproduce

```
V_hi = Σ_q μ(q)²/φ(q)² Σ_m Φ(m/M) Σ_{χ,ψ ∈ H_q} χ(-2 s m) conj(ψ(-2 s m)) ĉ_q(χ) conj(ĉ_q(ψ))
```

in the repository's own conventions, with the conjugation on the `ψ` side, the sign
`s` inside the argument, the `1/φ(q)²` normalisation carried by the channel weight,
and the ambient character set equal to `ambientSet`. The V20 source uses an
equivalent `ξ = χ·conj ψ` representation; the finite equivalence is **proved**, not
assumed: `preProjectorVariance_eq_xiForm`. Support on the high set is
`preProjectorVariance_highSet_support`; `preProjectorVariance_eq_AA` identifies the
pre-projector object with the `AA` child.

Channels at the physical level: `VhiHigh`, `AAChannel`, `BAChannel`, `ABChannel`,
`BBChannel`, with `VhiHigh_eq_channels` and
`AAChannel_eq_weighted_preProjectorVariance`.

---

## E. Ambient-character firewall

`TwoProjectorAmbientCompat3221` (same file) is a structure stating exactly that the
ambient set used by orthogonality is the one that `High` and `Bad` partition, and that
every remaining character restriction — primitivity, parity, unit sector, exceptional
convention, quotient-conductor conditions — is *inside* `Bad` or inside the ambient
set, not silently outside.

* `ambientCompat_of_source` builds an inhabitant **only** from source definitions that
  already establish the partition (it takes those hypotheses; it does not manufacture
  them).
* `ambientCompat_not_automatic` records that no inhabitant is produced by V21 itself.
* `highHigh_decomposition_under_ambientCompat` is the decomposition stated under the
  compatibility hypothesis.

---

## F. Safe bad-character cardinality repair

File: `RequestProject/Erdos287/BadCharacterCount3221.lean` (namespace
`Erdos287.V21BadCount`).

The heuristic `#Bad_q ≪ D·τ(q)` is **not** banked. Proved instead, with no asymptotic
notation inside the statements:

* `badCharacter_card_le_sum_totient` (alias `badCharacter_card_le_totientSum`):
  `#Bad ≤ Σ_{r ≤ D} (number of characters of conductor r) + #Exc`, bounded through
  `φ_prim(r) ≤ φ(r) ≤ r`;
* `two_mul_sum_range_succ_id` — the finite triangular identity;
* `badCharacter_card_le_triangular` and `badCharacter_card_le_triangular_div`:
  `#Bad ≤ D(D+1)/2 + #Exc`;
* `badCharacter_card_le_sq`: `#Bad ≤ (D+1)²` for `D ≥ 1` with a single exceptional
  character;
* specialised to Dirichlet characters: `badSet`, `highSetOf_badSet_eq_highSet`
  (the `Bad`/`High` split agrees with the V20 conductor split), `dirichletBad_card_le_sq`.

This is a genuine repair: the safe count carries **two** powers of `D`.

---

## G. Five-box double orthogonality

File: `RequestProject/Erdos287/DoubleOrthogonalityFiveBox3221.lean` (namespace
`Erdos287.V21DoubleOrth`). The V20 factorisation
`fiveBox_characterTransform_eq_prod_five` and `highCoeff_fiveBox` are reused; this
layer adds no analytic input.

Proved, source-exactly and with both signs `s = ±1` handled without coercion errors
(`sign_sq_iff`, `affine_divisor_sign_pos`, `affine_divisor_sign_neg`):

* `fullFull_orthogonality_left` — the `χ` side forces `-2 s m W ≡ 1 (mod q)`;
* `fullFull_orthogonality_right` — the `ψ` side forces `-2 s m W' ≡ 1 (mod q)`;
* `doubleOrthogonality_congruence` — hence `W ≡ W' (mod q)`;
* `doubleOrthogonality_shift_exists` — hence `∃ t, W - W' = q t`;
* `doubleOrthogonality_affineDivisor` — `q ∣ 2 m W' + s`;
* `doubleOrthogonality_coprime` — `(q, W') = 1`;
* `fiveProduct`, `fiveProduct_eq_prod`, `char_fiveProduct`, `fiveBox_shift_exists` —
  the same statements with `W = p₁⋯p₅`, `W' = p₁'⋯p₅'` labelled products.

---

## H. Short-shift geometry

`ShortShiftGeometry` (in `ShortShiftSieve3221.lean`) is the finite geometric packet
`W = W' + q t`, `(q, W') = 1`, `q ∣ 2 m W' + s`, and
`shortShiftGeometry_of_doubleOrthogonality` derives it from section G. This part is
proved.

---

## I. External sieve interface

`ShortShiftRoughSieve3221Input` (same file) encodes the audited physical implication

```
#{admissible t} ≤ C_sieve · (T / log X) · q/φ(q)
```

with the exact sieve metadata stored as data: `sieveDimension = 1`
(`sieveDimension_eq_one`), `sieveLevelExponent = 1/20` i.e. `z = T^{1/20}`
(`sieveLevelExponent_value`), and the `z²`-remainder-negligible condition as a field.

The interface is **uninhabited**. It is a `structure`, not an `axiom`.
`shortShiftSieve_not_automatic` records that V21 supplies no inhabitant.
`probeSieveData` is only a data probe (parameters), not an inhabitant of the input.

Status: `SELBERG/ROUGH-LINE-SIEVE287 : EXTERNALLY AUDITED CANDIDATE / NOT AXIOMATIZED`.

---

## J. External Shiu interface

File: `RequestProject/Erdos287/ShiuDivisorAverage3221.lean`.

Elementary parts **proved**:

* `totient_two_mul_of_odd : Odd n → φ(2n) = φ(n)`;
* `shiuLocalFactor W = 2W/φ(2W)` and `shiuLocalFactor_eq : Odd W → shiuLocalFactor W = 2W/φ(W)`,
  i.e. the convention-correct collapse of the local factor for odd `W'`.

Analytic part **uninhabited**: `ShiuLinearDivisorAverage3221Input` for the progression
`n = 2 W' m + s`, requiring
`Σ_{m∼M} τ(2W'm+s) ≤ C_shiu · M · log X · localFactor(W')`.
`shiuInput_localFactor_collapsed` rewrites the local factor of an assumed input;
`shiuInput_not_automatic` records non-inhabitation. Shiu's theorem is not proved and
not axiomatised.

---

## K. Prime-box normalization source audit (FIRST EXACT RESIDUAL)

A literal source search was performed for a *physical* `ω_i(p)`.

**Finding: the repository contains no physical `ω_i(p)` definition.** What exists is
abstract polarisation apparatus — `Erdos287.FactorialEuler` (`FactorialEulerPolarization`,
with an abstract coefficient family `om : ℕ → Fin 7 → K`) and
`Erdos287.BalancedSevenPolarization.labelledPolynomial`. These do not pin a physical
convention (`ω_i(p)` vs `Λ(p)` vs `log p · ω_i(p)` vs normalised prime indicator), and
in particular **no bounded physical `ω_i` may be inferred from the abstract factorial
coefficient-extraction theorem**.

Consequently `BalancedSevenPrimeBoxNormalization3221`
(`RequestProject/Erdos287/PrimeBoxNormalization3221.lean`) is left **uninhabited** and

```
BALANCED7-PRIMEBOX-L1-NORMALIZATION45 : SOURCE_OPEN
```

is the **current first exact residual** (`first_exact_residual_is_primeBoxNormalization`).

Proved in that file (all conditional, none inhabiting the interface):

* `primeBoxL1_of_pointwise_and_count` — the conditional compiler from a pointwise
  bound plus a prime-count input to `Σ_{p∼Y} |ω_i(p)| ≪ Y/log Y`;
* the phase-alignment repair of the circular provenance problem:
  `aligningPhase`, `aligningPhase_norm`, `aligningPhase_mul`,
  `phaseUniformBound_implies_sum_abs_omega_le_seven`,
  `phaseUniformBound_implies_each_abs_omega_le_seven` — the abstract finite lemma
  “uniform phase bound `|(1/7)Σ z_i ω_i(p)| ≤ 1` for all `z ∈ T⁷` implies
  `Σ_i |ω_i(p)| ≤ 7`”;
* `phaseUniformBound_not_automatic`, `primeBoxNormalization_not_automatic` — the
  antecedent is *not* claimed physically.

---

## L. Cutoff compatibility audit

File: `RequestProject/Erdos287/HighProjectorCutoff3221.lean`.

`D = log X` is **not** silently set. One shared cutoff datum
`sharedCutoff B0 X = (log X)^{B0}` is defined and shown to agree with the V20
`highConductorCutoff` (`sharedCutoff_eq`). `HighProjectorCutoffCompat3221` certifies

* the same cutoff on the analytic-projector and physical-comparison sides
  (`cutoffCompat_cutoffs_match`),
* that changing the cutoff does not alter unaccounted exceptional/principal pieces
  (`cutoffCompat_unaccounted_invariant`),
* that low-conductor reassembly remains valid (field `lowCond_reassembly`),
* agreement with the V20 firewall `MuLogComparisonAtCutoff`
  (`cutoffCompat_matches_v20_comparison`).

`cutoffCompat_does_not_fix_B0` shows the structure does not pin `B0`.
`cutoffCompat_not_automatic`: uninhabited. Status
`3221-HIGHPROJECTOR-CUTOFF-COMPAT45 : SOURCE_OPEN`.

---

## M. Physical log-prefactor audit

File: `RequestProject/Erdos287/PhysicalLogBudget3221.lean`.

`PhysicalLogPrefactorData` records every scalar between the physical Balanced7 packet
and the normalised `V_hi = AA − BA − AB + BB` object: powers of `log X`, powers of
`log Y`, `∏ log p_i`, `7⁷`, factorial constants, `5!`, Mellin factors, dyadic
multiplicity, the two-sign factor and the Cauchy normalisation.
`canonicalPrefactorConstants_values : (7⁷, 5!) = (823543, 120)` prints the constants.
`constantFactors` aggregates them; `prefactor_enters_log_ledger` proves that any fixed
positive power `(log X)^{C_ext}` enters the log ledger.

`PhysicalLogPrefactor3221` is **uninhabited** (`physicalLogPrefactor_not_automatic`):
literal source reconstruction did not establish `C_ext = 0` or any other exact value.
Status `3221-PHYSICAL-LOG-PREFAC45 : SOURCE_OPEN`.

### Exponent ledger (kernel-checked rational arithmetic)

`Mexp = 2/7`, `W5exp = 5/7`, `Qexp = 3/5`, `Texp = 4/35`, and

* `physicalShiftScale_exponent : Texp = W5exp - Qexp`
* `twoProjector_naturalExponent : 2/7 + 5/7 + 4/35 = 39/35`
* `outerCauchy_exponent : 3/5 + 2/7 = 31/35`
* `physicalSquareRoot_exponent : 31/35 + 39/35 = 2`
* `exponent_ledger` — the three together.

No analytic theorem is derived from these.

---

## N. BA / AB / BB ownership

The four children are **separate** objects throughout, never bundled into one abstract
HHH child: `AA3221`, `BA3221`, `AB3221`, `BB3221` (exact finite source expressions,
with the `1/φ(q)²` normalisation printed in the channel definitions), and separate
bound interfaces `AAChannelBound3221`, `BAChannelBound3221`, `ABChannelBound3221`,
`BBChannelBound3221` in `BalancedSevenV21Compiler.lean`.

`BA` is one-bad/one-full, `AB` is the symmetric orientation, `BB` is both-bad; the
orthogonality that remains on the full side is exactly what section G proves.

No statement of the form `BA/AB ≪ log^{-8}` or `BB ≪ log^{-8}` is asserted. The
required bounds are hypotheses of the compiler, and the repaired log arithmetic under
the safe `D²` count is banked separately in
`RequestProject/Erdos287/BadCharacterLogLedger3221.lean`:
`bb_logExponent B0 = 20 - 8 B0`, `ba_logExponent B0 = 15 - 4 B0`,
`2·Cvar(B0) = min(10, 15-4B0, 20-8B0)`, with kernel samples `Cvar(1)=5`, `Cvar(2)=2`,
`Cvar(3) = -2` and `cvar_decreasing_sample`. In particular `B0 < 5` is **not**
hard-coded anywhere.

---

## O. Prime-density anti-double-spending

File: `RequestProject/Erdos287/OuterTwoPrimeBlock3221.lean`. The seven physical prime
boxes are partitioned using the repository's own `Erdos287.Grouping3221` labels:
`outerBoxes = blockM = {1,2}`, `innerBoxes = {0,3,4,5,6}`.

* `outerInnerBox_disjoint : Disjoint outerBoxes innerBoxes`
* `outerInnerBox_cover : outerBoxes ∪ innerBoxes = univ`
* `sevenBox_partition_cardinality` — `2 + 5 = 7`
* `primeDensity_no_double_spending` — every label is owned by exactly one side
* `parametricOwnership` — the same firewall for an arbitrary outer choice.

Finite/source bookkeeping only; no density is claimed.

---

## P. Outer two-prime L²

Same file. `alphaOuter P1 P2 w1 w2 m = Σ_{p_i p_j = m} ω_i(p_i) ω_j(p_j)` over the two
actual labels, with representation multiplicity handled: `alphaOuter_labelled_swap`
(labelled vs unlabelled products, including `p_i = p_j` and overlapping dyadic boxes),
`alphaOuter_l1_le`, and the conditional `L²` compiler `outerL2_of_sup_and_l1`.

`OuterTwoPrimeL2Normalization3221Input` is the analytic antecedent
(`Σ_m |α(m)|² ≪ M/log²X`); it is **uninhabited**
(`outerTwoPrimeL2_not_automatic`), and `outerL2_input_of_sup_and_l1` only converts a
supplied density input.

---

## Q. Symbolic log-budget compiler

`projectorLogExponent cAA cBA cAB cBB = min4(...)` with the four
`projectorLogExponent_le_*` lemmas, `channel_bound_relax`, `highVarianceLogCompiler`
(if `AA, BA, AB, BB ≤ X^{39/35} log^{-c_•}` then `V_hi ≤ X^{39/35} log^{-min4}`), and
`outerCauchyLogCompiler` for the outer Cauchy combination. Inputs `C_AA, C_BA, C_AB,
C_BB, C_outer, C_external, B0` are all symbolic parameters; no exponent is guessed.

---

## R. LOGVAR conditional compiler

File: `RequestProject/Erdos287/BalancedSevenV21Compiler.lean`.

`TwoHighProjector3221ClosureInputs` contains only genuine antecedents: ambient
projector compatibility, the exact five-box source, the short-shift sieve input, the
Shiu divisor-average input, the prime-box normalization input, the `BA`, `AB`, `BB`
bounds, the outer two-prime `L²` input, shared cutoff compatibility and the physical
log-prefactor budget.

`twoHighProjector3221_closes_logVar` concludes the required LOGVAR bound only when the
supplied symbolic log inequality is strictly strong enough. It is Lean-proved; it is
**not inhabited**. `logVar_of_twoHighProjectorPackage` is the V21 preferred compiler,
added beside — not replacing — the V20 `logVar_of_four_channels`.

`3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45` is **not** marked CLOSED
(`logVar_open_conditional`).

---

## S. Sixth-moment fallback status

The sixth moment is neither deleted nor marked false.
`3221-HIGHCOND-RESIDUE-SIXTH-MOMENT45 : OPEN STRONGER SUFFICIENT FALLBACK`
(`sixthMoment_open_stronger_fallback`). The conditional
`sixthMoment_not_needed_if_twoProjectorClosed` states that it stops being needed as
controlling *only* once the two-projector physical closure inputs are inhabited.

---

## T. Comparison firewall

The V20 same-cutoff firewall is kept and reused; the elementary scalar identities
already proved in V20 are preserved. V21 analytic work does not inhabit comparison:
`twoProjectorCompiler_cannot_construct_comparison` and
`balancedSevenV21_cannot_construct_comparison`.

Status split: `COMPARISON-SMALLCOND-EXCEPTIONAL-SPLICE45 : SOURCE_OPEN`,
`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_OPEN`.

---

## U. Balanced7 compiler

`balancedSeven_of_v21_package` takes the two-projector/LOGVAR physical closure, the
same-cutoff comparison match, and the existing exact factorial/polarization source
inputs, and concludes the Balanced7 packet through the existing
`Erdos287.V19Compiler.balancedSeven_of_highCondLogVar` route. Comparison is left
uninhabited, so **BALANCED7 remains OPEN**.

---

## V. Current first exact residual

Ordered ledger (`residualRank` in `RequestProject/Status/Erdos287V21Status.lean`):

1. `BALANCED7-PRIMEBOX-L1-NORMALIZATION45 : SOURCE_OPEN`  ← first exact residual
2. `3221-HIGHPROJECTOR-CUTOFF-COMPAT45 : SOURCE_OPEN`
3. `3221-PHYSICAL-LOG-PREFAC45 : SOURCE_OPEN`
4. then `BA/AB/BB` analytic bounds under the repaired safe bad-character count;
   comparison only afterwards (`comparison_not_first_residual`).

---

## W. Build and trust audit

* `lake build`: **success, 0 errors**; 8160 jobs at the V21 head (baseline 8148 + the V21
  modules).  The V21 modules themselves emit **no** warnings; the warnings reported by a
  from-source rebuild all come from pre-existing V20-and-earlier modules (Mathlib linter
  notes such as `unusedSimpArgs`).
* Trust scan of all new V21 files for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
  `native_decide`, `@[implemented_by]`: **zero occurrences** in code (the only textual
  hits are the words “unsafe heuristic” and “sorry-free” inside documentation
  comments).
* `RequestProject/Status/AxiomAuditErdos287V21.lean` runs `#print axioms` on every
  principal new declaration (~90 of them). Every one reports exactly
  `[propext, Classical.choice, Quot.sound]`. No external analytic theorem enters
  through a user axiom.

---

## X. Final machine ledger

Kernel-decidable finite data in `RequestProject/Status/Erdos287V21Status.lean`
(`Node`, `Label`, `ledger`, all statements closed by `decide +kernel`):

```
V20 character Gram                  : BANKED
V20 HHH route                       : VALID REPRESENTATION / SUPERSEDED AS CONTROLLING
OLD HHH inclusion-exclusion closure : RETRACTED
TWO-HIGHPROJECTOR REASSEMBLY        : ALGEBRAIC PASS
DOUBLE ORTHOGONALITY                : EXACT PASS
SAFE BAD-CHARACTER COUNT            : FINITE PASS
SHIU                                : EXTERNAL ANALYTIC INTERFACE / UNINHABITED
SHORT-t SIEVE                       : EXTERNAL ANALYTIC INTERFACE / UNINHABITED
PRIMEBOX NORMALIZATION              : SOURCE_OPEN
CUTOFF COMPATIBILITY                : SOURCE_OPEN
PHYSICAL LOG PREFACTOR              : SOURCE_OPEN
TWO-PROJECTOR CLOSURE               : CONDITIONAL
LOGVAR                              : OPEN / CONDITIONAL
SIXTH MOMENT                        : OPEN STRONGER SUFFICIENT FALLBACK
COMPARISON                          : SOURCE_OPEN
BALANCED7                           : OPEN
FCL                                 : OPEN
GATE2                               : CONDITIONAL / NOT ACTIVATED
WINDOWPAIRSUPPLY                    : OPEN
ERDOS287                            : OPEN
```

---

## REQUIRED FINAL BLOCK

```
FILES ADDED:
RequestProject/Erdos287/TwoHighProjector3221.lean
RequestProject/Erdos287/DoubleOrthogonalityFiveBox3221.lean
RequestProject/Erdos287/BadCharacterCount3221.lean
RequestProject/Erdos287/PrimeBoxNormalization3221.lean
RequestProject/Erdos287/ShortShiftSieve3221.lean
RequestProject/Erdos287/ShiuDivisorAverage3221.lean
RequestProject/Erdos287/HighProjectorCutoff3221.lean
RequestProject/Erdos287/PhysicalLogBudget3221.lean
RequestProject/Erdos287/OuterTwoPrimeBlock3221.lean
RequestProject/Erdos287/BadCharacterLogLedger3221.lean
RequestProject/Erdos287/BalancedSevenV21Compiler.lean
RequestProject/Status/Erdos287V21Status.lean
RequestProject/Status/AxiomAuditErdos287V21.lean
ERDOS287_V21_TWO_PROJECTOR_SAFE_REPAIR_BANK_REPORT.md

FILES MODIFIED:
RequestProject/Main.lean   (import lines appended only)

V20 PRESERVED:
YES

OLD HHH CLOSURE PROOF:
RETRACTED

TWO-HIGHPROJECTOR ALGEBRA:
EXACT / ALGEBRAIC PASS (highIndicator_eq_one_sub_badIndicator,
twoHighProjector_pointwise, highHighSum_eq_AA_sub_BA_sub_AB_add_BB;
no omitted cell, no overlap, no double counting)

DOUBLE ORTHOGONALITY:
EXACT PASS (fullFull_orthogonality_left/right, doubleOrthogonality_congruence,
doubleOrthogonality_affineDivisor, doubleOrthogonality_shift_exists; s = ±1 both handled)

BAD-CHARACTER SAFE COUNT:
FINITE PASS (#Bad ≤ D(D+1)/2 + 1 ≤ (D+1)^2; the D·tau(q) heuristic is NOT banked)

PRIMEBOX NORMALIZATION:
SOURCE_OPEN / UNINHABITED (no physical omega_i definition exists in the repository)

CUTOFF COMPATIBILITY:
SOURCE_OPEN / UNINHABITED

PHYSICAL LOG PREFACTOR:
SOURCE_OPEN / UNINHABITED

SHIU INTERFACE:
EXTERNAL ANALYTIC INTERFACE / UNINHABITED (elementary phi(2W)=phi(W) proved)

SHORT-t SIEVE INTERFACE:
EXTERNAL ANALYTIC INTERFACE / UNINHABITED (z = T^(1/20), dimension 1 recorded as data)

BA:
SEPARATE CHANNEL / BOUND IS A HYPOTHESIS, NOT A THEOREM

AB:
SEPARATE CHANNEL / BOUND IS A HYPOTHESIS, NOT A THEOREM

BB:
SEPARATE CHANNEL / BOUND IS A HYPOTHESIS, NOT A THEOREM

OUTER TWO-PRIME L2:
ALGEBRA PROVED / ANALYTIC DENSITY ANTECEDENT UNINHABITED

TWO-PROJECTOR CLOSURE:
CONDITIONAL (compiler Lean-proved, no inhabitant)

3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45:
OPEN / CONDITIONAL — NOT CLOSED

SIXTH MOMENT:
OPEN STRONGER SUFFICIENT FALLBACK — not deleted, not marked false

COMPARISON:
SOURCE_OPEN

BALANCED7:
OPEN

ERDOS287:
OPEN

FIRST EXACT RESIDUAL:
BALANCED7-PRIMEBOX-L1-NORMALIZATION45 : SOURCE_OPEN

LAKE BUILD:
SUCCESS — 8160 jobs at the V21 head, 0 errors; 0 warnings from V21 modules
(pre-existing V20-and-earlier modules emit unrelated linter notes)

TRUST SCAN:
ZERO occurrences of sorry / admit / axiom / opaque / unsafe / native_decide /
@[implemented_by] in all new V21 files; #print axioms on every principal declaration
returns only [propext, Classical.choice, Quot.sound]

PUBLIC-MAIN SYNC:
RequestProject/Main.lean extended with the V21 imports only; full build clean
```

### FINAL FIREWALL

```
No source-open or external analytic interface was inhabited merely to make
the compiler execute.

No statement in V21 proves Erdős #287.

No statement in V21 proves Balanced7 unless the explicit analytic/source
antecedents are separately supplied.
```
