# Erdős #287 — V67–V71 append-only delta bank (PostV64V71)

**ERDŐS #287 REMAINS OPEN.**  This run makes the exact / finite / algebraic parts of the
V67–V71 chain kernel-visible, proves the conditional tail closure, and isolates every analytic
input as a named, uninhabited proposition.  The current research owner `DeterminantSupply287`
is **defined, never proved, never assumed globally**.

## BASE HEAD

`c617925` (Initial commit of this run's repository = the PostQSigma/V64 bank).

## NEW FILES

All under `RequestProject/Erdos287/` (append-only; no existing file modified):

| file | content |
|---|---|
| `PostV64V71.lean` | aggregator |
| `PostV64V71/ReciprocalFingerprint.lean` | `recipSums`, `Xi`, reciprocal congruence, good-row emptiness, integer size bank |
| `PostV64V71/SourceRows.lean` | `2N ≤ M`, V69 upper-half primes, V70 all good multiples, forced neighbours |
| `PostV64V71/ResidualDenominator.lean` | `E_H(M)`, `∏E ∣ Ξ_H`, `B_E ≤ log Ξ_H`, `D_lo`, `D₂`, `selected_dvd_D2` |
| `PostV64V71/DeterminantBox.lean` | determinant box, `det`, rough factor ⟺ tuple, owner multiplicity `≤ 2H`, good tuple ⇒ contradiction |
| `PostV64V71/ExceptionAccounting.lean` | `θ*`, `D_θ`, `D_Λ`, `D_θ^gg`, fibre lemma, exception loss, prime-power contamination |
| `PostV64V71/TailClosure.lean` | canonical height facts, `DeterminantSupply287`, `FingerprintLogBound287`, tail theorem, splices |
| `PostV64V71/FingerprintLogBudget.lean` | `LcmUpperBound12 → FingerprintLogBound287`, tail theorem with standard external input |
| `PostV64V71/RoughPart.lean` | `Λ_x(M,E)`, rough part `R_x`, `R_x(M,E_H) ∣ Ξ_H` |
| `PostV64V71/SourcePinned.lean` | V67 pinned identity `X(E) = P(D − Y(A))` and equivalences (with repair) |
| `PostV64V71/ComponentFactorisation.lean` | V67 free-component factorisation `N_τ = [z^τ] ∏ F_i` |
| `PostV64V71/LocalAdmissibility.lean` | gcd / parity / `q ≠ r`, Bézout parametrisation, resultant, `ν_ℓ`, local singular factor |
| `PostV64V71/WeightedCorrelation.lean` | `f_K`, `C_K`, `C_K ≤ D_Λ` (exact subbox dictionary) |
| `PostV64V71/CircleIdentity.lean` | `∫₀¹ e(hα) = [h=0]`, `C_K = ∫₀¹ 2cos(2πα)|S_M|²`, major/minor exact split |
| `PostV64V71/AnalyticFrontier.lean` | analytic providers, effectivity firewall, minor+major ⇒ supply |
| `PostV64V71/RegressionFixtures.lean` | finite exact fixtures |
| `PostV64V71/CurrentLedger.lean` | current ledger, `current_open_entries`, etc. |
| `PostV64V71/AxiomAudit.lean` | `#print axioms` on 51 declarations |

plus this report.

## EXISTING FILES MODIFIED

None.  (`PostQSigma/Ledger.lean` and its `open_entries` are untouched.)

## Status by item

| item | verdict | Lean declarations |
|---|---|---|
| V67 PINNED NORMALISATION | **LEAN BANK + REPAIR** | `pinned_selected_mass`, `pinned_selected_mass_iff`, `pinned_W_dvd_iff`, `pinned_D_dvd_iff_of_coprime`, `pinned_mass_bounds`, `pinned_D_dvd_counterfixture` |
| V67 COMPONENT FACTORISATION | LEAN BANK | `compPoly_union`, `compPoly_biUnion`, `component_coefficient_factorization`, `compCount_of_neg`, `forced_restricted_count_eq` |
| FINGERPRINT | LEAN BANK | `recipSums`, `Xi`, `num_dvd_Xi`, `exists_cofactor_set`, `good_large_prime_row_empty` |
| XI_H SIZE | integer bank LEAN BANK; log bound **LEAN PROVED CONDITIONAL** on external `LcmUpperBound12` | `Xi_le_BH_pow`, `Xi_le_BH_pow_two_pow`, `fingerprintLogBound_of_lcm` |
| D2 DIVISIBILITY | LEAN BANK | `Gap2CE.selected_dvd_D2` |
| D2 LOG BOUND | EXTERNAL / PAPER (not used by the tail chain) | `D2LogBound287` (uninhabited) |
| UPPER-HALF PRIMES | LEAN BANK | `Gap2CE.upper_half_prime_omitted`, `Gap2CE.upper_half_prime_neighbours` |
| ALL GOOD-q MULTIPLES | LEAN BANK | `Gap2CE.all_good_multiples_omitted` |
| FORCED NEIGHBOURS | LEAN BANK | `Gap2CE.forced_neighbours_selected` |
| ROUGH PART | LEAN BANK | `Gap2CE.roughPart_dvd_Xi`, `Gap2CE.log_roughPart_lt` |
| DETERMINANT PARAMETRISATION | LEAN BANK | `rough_factor_iff_determinant_tuple`, `det_eq` |
| OWNER MULTIPLICITY ≤ 2H | LEAN BANK | `owner_multiplicity_le_twoH_r`, `owner_multiplicity_le_twoH_q` |
| EXCEPTION LOSS | LEAN BANK | `exception_weight_loss` |
| VON MANGOLDT PRIME-POWER ERROR | LEAN BANK (constant 8, see audit) | `mangoldt_prime_power_error_exact`, `PPW_le`, `mangoldt_prime_power_error` |
| LOCAL ADMISSIBILITY | LEAN BANK | `local_determinant_admissibility`, `determinant_parametrisation`, `no_common_root`, `local_forbidden_residue_count`, `parity_collapse` |
| AVERAGE SINGULAR SERIES | EXTERNAL / PAPER (local factor LEAN BANK) | `AverageSingularSeries287` (uninhabited); `local_factor_ratio`, `singularSeries` |
| WEIGHTED CORRELATION C_K | LEAN BANK | `weighted_subbox_le_full_supply`, `weighted_subbox_le_full_supply_quarter` |
| CIRCLE IDENTITY | LEAN BANK | `circle_correlation_identity` |
| MAJOR/MINOR SPLIT | LEAN BANK (exact; no estimate) | `major_minor_exact_decomposition(_V71)` |
| MAJOR ARC | EXTERNAL-PAPER / UNINHABITED | `EventualMajorArc287`, `SiegelWalfiszLogModuli287`; effective form `EffectiveMajorArc287` OPEN |
| SIGNED MINOR ARC | **OPEN** | `MinorArcLowerBound287` |
| DeterminantSupply287 | **OPEN** | `DeterminantSupply287` |
| TAIL M ≥ 2^1500 | **CLOSED CONDITIONAL** | `determinant_supply_implies_no_tail'` (needs `DeterminantSupply287`, `LcmUpperBound12`) |
| HUANG FINITE BANK | **ABSENT** (external premise) | `HuangFiniteExclusion287` (uninhabited) |
| GLOBAL #287 | **OPEN** (conditional theorem only) | `erdos287_of_determinant_supply`, `erdos287_of_analytic_route` |

## The terminal chain (all Lean-proved implications)

```
DeterminantSupply287  (D_Λ > 13M/L³, M ≥ 2^1500)                 [OPEN]
  ─ mangoldt_prime_power_error + contamination_lt ─▶ D_θ > 12M/L³
  ─ exception_weight_loss + loss_lt + B_E ≤ log Ξ_H < 2M/L⁵ ─▶ D_θ^gg(E_H) > 0
       (log Ξ_H < 2M/L⁵  ⇐  LcmUpperBound12 [EXTERNAL], fingerprintLogBound_of_lcm)
  ─ some box tuple with both owners prime and ∉ E_H ─▶ both owners good (∤ Ξ_H)
  ─ all_good_multiples_omitted ─▶ kq ∉ A, tr ∉ A, |kq − tr| = 1, both in [N, M]
  ─ blockerPair_contradiction ─▶ False
```

`determinant_supply_excludes_source` uses no prime-distribution heuristic.  The canonical height
`Hcan M = ⌊(log M − 6 log log M)/log 2⌋₊` satisfies `1 ≤ H ≤ 3L/2` and `12L⁶ < √M` for
`M ≥ 2^1500` (`canonical_height_facts`, real analysis fully in Lean).

## Audit findings (hostile reproof)

1. **V67 third equivalence — REPAIR.**  `X(E) = 0 ⟺ Y(A) = D` is proved.  The literal third
   equivalent "`D ∣ X(E)`" is not valid from the identity alone: the shape `X = P(D − Y)`,
   `0 < Y < 2D` admits `P = D = 2`, `Y = 1` (`pinned_D_dvd_counterfixture`).  Proved
   replacements: `W ∣ X(E) ⟺ Y(A) = D` (`pinned_W_dvd_iff`), and `D ∣ X(E) ⟺ X(E) = 0` under
   `gcd(W/D, D) = 1` (`pinned_D_dvd_iff_of_coprime`).  No downstream V68–V71 statement uses the
   literal form, so nothing else changes.
2. **Prime-power contamination constant.**  The research text's `4 H √M L²` needs
   `ψ(M) − θ(M) ≤ √M log M`.  Mathlib proves `|ψ − θ| ≤ 2√x log x`, so the Lean bound is
   `8 H √M L²`.  The closure margin `8 H √M L² < M/L³` is proved for `M ≥ 2^1500`; the final
   implication `D_Λ > 13M/L³ ⇒ D_θ > 12M/L³` is unchanged.
3. **Fingerprint log budget.**  `log Ξ_H < 2M/L⁵` is *not* derivable from Mathlib's Chebyshev
   bound `ψ(x) ≤ log 4·x + 2√x log x` (`log 4/log 2 = 2` exactly meets the target constant and
   the error terms push it over).  It is proved in Lean from `LcmUpperBound12`
   (`lcm(1..n) ≤ e^{1.2n}`, i.e. `ψ(n) ≤ 1.2n`; Rosser–Schoenfeld give `ψ(x) < 1.03883x`),
   which is a named external input.
4. **Good-row emptiness hypotheses.**  The theorem needs only `⌊M/q⌋ ≤ H` (e.g. `q > M/H`) and
   `q ∤ Ξ_H`; neither `q > H` nor `q² > M` is needed (the cofactors of the top `q`-adic layer
   automatically lie in `[1, ⌊M/q⌋]` and are prime to `q`).  `q² > M` (as `M < (⌊M/H⌋+1)²`) is
   used only for `selected_dvd_D2`, `roughPart_dvd_Xi` and owner multiplicity.
5. **Effectivity.**  `effectivity_firewall` proves that an eventual statement does not imply a
   fixed-onset one; `minor_plus_effective_major_implies_supply` requires an explicit onset
   `≤ 2^1500`.  `EventualMajorArc287` is never used to produce a fixed-onset statement.
6. No V67–V71 exact statement was found false beyond item 1.

## Current-route independence

`determinant_supply_implies_no_tail'` has exactly two hypotheses, `DeterminantSupply287` and
`LcmUpperBound12`.  It does not use `ContactSupply`, `|Ddeep| ≤ 5`, the size-≤3 first-digit
classification, the `3M ≤ 8n` endpoint cap, composite-resonance / Croot firewalls, the physical
CRT fixture, `PG287` or `PsiLowerBound`.  These previous-run omissions were therefore not
worked on.

## RESEARCH OPEN ENTRIES (`CurrentLedger.research_open_entries`)

* `EffectiveMajorArc287` (effective major-arc lower bound with onset ≤ 2^1500)
* `SignedMinorArcLowerBound287` (`MinorArcLowerBound287`)
* `DeterminantSupply287` — **current sole research owner**
* plus the original Erdős #287 (`current_open_entries`)

## FORMAL UNINHABITED EXTERNAL ENTRIES (`CurrentLedger.formal_uninhabited_external_entries`)

* `D2LogBound287` (paper)
* `AverageSingularSeries287` (paper)
* `SiegelWalfiszLogModuli287` (known theorem, ineffective constants; not in Lean)
* `EventualMajorArc287` (paper; uses Siegel–Walfisz)
* `LcmUpperBound12` (`ψ(n) ≤ 1.2n`; known; not in Mathlib)
* `HuangFiniteExclusion287` (certificate absent)

Historical owners: SC287 RETIRED/REFUTED; PG287 historical open, superseded as current owner;
PZ, RNLCM, RP-RNLCM, V70 exception-quantified LDBS retired/superseded (no Lean declarations).

## AXIOM AUDIT

`PostV64V71/AxiomAudit.lean`: `#print axioms` on 51 declarations.  49 depend on a subset of
`[propext, Classical.choice, Quot.sound]` (`effectivity_firewall`: `[propext]` only); the two
ledger theorems depend on no axioms.  Finite fixtures use `decide` / `decide +kernel`
(kernel evaluation, no extra axioms).  No `sorry`, `admit`, `axiom`, `native_decide`,
`bv_decide`, `unsafe`, `implemented_by` or `opaque` in the new files; no interface proposition is
ever constructed.

## FINAL VERDICT

SUCCESS A (full V67–V71 exact bank) with one hostile REPAIR (V67 third equivalence).  The tail
`M ≥ 2^1500` is closed **conditionally** on `DeterminantSupply287` (OPEN) and the external
`LcmUpperBound12`; the major arc is paper-level/uninhabited, the signed minor arc is OPEN, the
Huang finite certificate is absent.  **Erdős #287 remains OPEN.**

## Build status

* `lake build RequestProject.Erdos287.PostV64V71` — succeeded (8090 jobs), no warnings in the new subtree.
* Full `lake build` — succeeded (8959 jobs).
* No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by` or `opaque` in the new subtree; all audited declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
