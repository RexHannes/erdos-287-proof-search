# ERDŐS #287 — 3221 SAFE BANK REPORT (V18)

**ERDŐS #287 REMAINS OPEN.** Nothing in this run proves it, nor Balanced7, nor the
factorial signed endpoint, nor the comparison match, nor any Kuznetsov /
Deshouillers–Iwaniec / Pascadi estimate. No `axiom` was added, no interface was inhabited,
and no `sorry` exists anywhere in the Lean sources.

This run is a **source-reconstruction and status-repair** run continuing the existing
repository in place. It follows the V17 3221 bank (see `ERDOS287_3221_V17_SAFE_BANK_REPORT.md`),
which is reused unchanged.

---

## 0. Workspace / regression guard

* Branch `main`, working tree clean at start; baseline `lake build`: **8131 jobs, 0 errors**.
* Final `lake build`: **8135 jobs, 0 errors**.
* All named prerequisites were located before any edit and **reused, never redefined**:
  `RequestProject/Erdos287/FactorialEulerPolarization.lean`, `FactorialEulerLocal.lean`,
  `FactorialPolarizationLinearity.lean`, `PascadiParameterLedger.lean`,
  `RequestProject/Status/Erdos287V16Status.lean`, and the declarations
  `factorialEulerPolarization`, `factorialEulerPolarization_seven`,
  `factorialPolarization_commutes_linearMap`,
  `Erdos287.V16Status.FactorialOmega7SignedEndpoint`,
  `Erdos287.V15Status.MuLogComparisonLowCondMatch`,
  `Erdos287.V16Status.BalancedSevenPacketInput`.
  The V17 3221 files (`Exponent3221Ledger`, `BalancedSeven3221Grouping`,
  `SourceAssistedDiagonal3221`, `OffDiagonal3221`, `EHNoWrap3221`,
  `DIKuznetsov3221Interface`, `BalancedSeven3221Compiler`, `Erdos287V17Status`) were also
  reused unchanged.
* Files **added** this run:
  `RequestProject/Erdos287/NormalForm3221.lean`,
  `RequestProject/Erdos287/MovingPhaseProvider3221.lean`,
  `RequestProject/Erdos287/FactorialEndpoint3221Adapter.lean`,
  `RequestProject/Status/Erdos287V18Status.lean`, this report.
* Files **edited**: `RequestProject/Main.lean` — four import lines only.

---

## A. Baseline factorial bank (unchanged, verified present)

| Item | Status |
|---|---|
| `OMEGA7-FACTORIAL-EULER-POLARIZATION45` (`factorialEulerPolarization`, `_seven`) | `LEAN_PROVED / PROVED_ALGEBRAIC` |
| `POLARIZED-EXPECTED-TERM-LINEARITY45` (`factorialPolarization_commutes_linearMap`) | `LEAN_PROVED / PROVED_ALGEBRAIC` |
| factorial local Euler-series identities (`FactorialEulerLocal`) | `LEAN_PROVED` (formal algebra) |
| repeated-prime coefficient cancellation (`fiber_card_eq`) | `LEAN_PROVED` |
| `PASCADI-Q3/5-Y1/7-PARAMETER-NOGO` | `LEAN_PROVED / PARAMETER_LEDGER` |
| `FactorialOmega7SignedEndpoint` | `UNINHABITED` analytic interface |
| `MuLogComparisonLowCondMatch` | `UNINHABITED / SOURCE OPEN` |

Nothing in the repository contradicted these statuses, so none was changed.

## B. 3221 labelled regrouping (V17, reused)

`Erdos287.Grouping3221`: blocks `{0} {1,2} {3,4} {5,6}`, `grouped_product_eq`
(`e·m·n·ℓ = p₀⋯p₆`), and the exact finite regrouping `sevenfold_regrouping` with the
convolution coefficients `eta, alpha, beta, gamma`. `BALANCED7-3221-GROUPING45 :
PROVED_FINITE`.

## C. Coefficient multiplicity

Injectivity is **not** asserted: `grouping_not_injective` exhibits two distinct prime
7-tuples with the same `(e,m,n,ℓ)`, and `alpha_not_one_bounded` shows `α(6) = 2`. The
legitimate majorant is `alpha_norm_le_card_divisors` (`‖α(a)‖ ≤ τ(a)`).

## D. Exponent ledger

`Erdos287.Ledger3221`, exact ℚ arithmetic (`CAPACITY_ONLY`, bookkeeping — not an analytic
theorem):

`E=1/7, M=N=L=2/7, Q=3/5`; `E+M+N+L=1`; `W=E+N+L=5/7`; `(N+L)−Q=−1/35`;
`W−Q=4/35`; `(W−Q)/2=2/35`; `H=Q−M=11/35`; `E+H=16/35<3/5` with margin `3/5−16/35=1/7`;
`T=W−Q=4/35`; plus the transcribed zero-ε margins `1/10, 2/21, 19/35, 4/35, 2/35`.

## E. Source-assisted diagonal (V17, reused)

`fiberwise_energy_le`, `productFibre_card_le` (`τ²` fibre majorant), `pushforward_energy_le`,
`modulus_divisor_count_le` **with** the separately routed zero case `modulus_count_zero_case`,
`diagonal_parent_bound`, `sourceAssisted_diagonal_finite`; exponent side
`diagonal_exponent_value : 1 + (Q−W)/2 = 1 − 2/35`.
`3221-SOURCE-ASSISTED-DIAGONAL45 : PROVED_FINITE / CAPACITY_ONLY` — the divisor-growth
majorants are explicit hypotheses, never analytic theorems, and no `X^{o(1)}` is encoded.

## F. Off-diagonal `t` (V17, reused)

Over ℤ throughout: `offdiag_existsUnique_t`, `offdiag_t_ne_zero`, `offdiag_ne_of_t_ne_zero`,
`offdiag_abs_t_le` (`|t|·Q_min ≤ 2 W_max`, factor 2 explicit) and `offdiag_abs_t_le_div`.
Exponent-only consequence `E N L / Q = X^{4/35}`.
`3221-OFFDIAGONAL-T-RANGE45 : PROVED_FINITE / CAPACITY_ONLY`.

## G. EH no-wrap (V17, reused)

`ratio_eq_iff_cross` (unit sector, hypotheses explicit), `ratio_eq_iff_cross_zmod`,
`nowrap_eq_of_dvd_of_abs_lt`, `nowrap_cross_eq`, capacity `EH = 16/35 < 21/35 = Q`.
No-wrap is applied only under a literal size hypothesis; it is never inferred from the
exponent comparison alone.

## H. EH ratio-fibre energy — hostile audit

Collisions after no-wrap were counted honestly: `ratioCollision_samePrime` (`e₁=e₂ ⇒ h₁=h₂`)
and `ratioCollision_distinctPrimes_param` (distinct primes ⇒ `h₁ = c e₁`, `h₂ = c e₂`),
giving `#collisions ≤ #E·#H + (#E)²·#C` and `ehRatioEnergy_le_explicit`.
Forced status: **`CONDITIONAL_FINITE`** — the bound holds under the explicit no-wrap
hypothesis; it is not unconditional. The firewall is preserved verbatim: **low
Hilbert–Schmidt energy does NOT imply low nuclear rank**, and no energy statement was
replaced by a rank statement.

## I. Completed source search (this run)

Searched the actual repository for: dispersion, completion, Poisson, Kloosterman source,
completed off-diagonal, gcd extraction, low-conductor projection.

* **Present**: `TrustedBank.UnitTransport.kloostermanLike` and its exact unit-change
  identity `kloostermanLike_unit_change` (an abstract Kloosterman-*shaped* finite sum);
  the V17 finite diagonal/off-diagonal/no-wrap packages; the V17 source data record
  `BalancedSeven3221CompletedSource`.
* **Absent**: any dispersion identity, any Poisson/completion identity, any additive
  character attached to the physical source, any gcd-extraction lemma for it, any
  low-conductor projection of it.

No theorem was reconstructed from chat nomenclature.

## J. Literal normal form

`Erdos287.NormalForm3221.BalancedSeven3221NormalForm` **pins** the schematic child

```
K_λ = ∑_{r,s} (∑_m a_{m,r,s}) (∑_n e(n ω_{r,s})) (∑_c g_λ(s,c) S(A,B; s c))
```

as an exact equality field on explicit finite data (boxes `R,S,M,N,C`; coprime modulus
factorisation `q = r s`; unit, gcd, zero-mode and low-conductor routing; the Kloosterman
leg literally equal to `kloostermanLike` of modulus `s c`). There is **no free `Prop`
field** and **no inhabitant**. Proved about the pinned data:
`kloostLeg_unit_change`, `modulus_above_cut`, `factorisation_is_data`.

**`3221-LITERAL-NORMALFORM-SOURCE-PIN45 : SOURCE_BLOCKED / UNINHABITED`** — a legitimate
successful outcome, since the derivation source is absent.

## K. `ω` formula status

No literal formula for `ω` is claimed (it cannot be derived without the completion step).
What is proved: the phase `e(x) = exp(2πix)` with **representative invariance mod 1**
(`phase_int_add`, `phase_fract`, `phase_congr`), unimodularity (`norm_phase`), and the
pinned form `phase_leg_congr` (each integer mode of the phase leg depends on `ω_{r,s}` only
mod 1). The dependence classification is recorded without being forced
(`OmegaDependsOnR / OnS / OnProduct / OnPair`), with the counterguard
`omega_product_strictly_stronger`: product dependence is strictly stronger than ordered-pair
dependence, because `1·6 = 2·3`.
**`3221-OMEGA-FORMULA45 : SOURCE_OPEN`** (phase infrastructure `PROVED_ALGEBRAIC`).

## L. Exceptional `Z` status

`Z_3221` is **not** given a numerical value. It exists only as a metadata field `Z` of the
pinned normal form, alongside the theorem parameters `R0, S0, M0, N0, C0` and `Qlevel`,
each with a positivity field. These are source/dictionary metadata plus rational
arithmetic — **not** analytic bounds.
**`Z_3221 : SOURCE_OPEN`.**

## M. Small-`Z` conditional compiler

* Range test `InSmallZRange Z Qlevel N0 : Z ≤ max(1, Qlevel/N0)`, with the exact algebraic
  characterisation `inSmallZRange_iff` (`N₀>0 ⇒ (Z ≤ 1 ∨ Z N₀ ≤ Q)`), the dichotomy
  `smallZ_or_large`, disjointness `not_smallZ_and_large`, and a nonvacuity witness
  `range_test_nonvacuous`.
* Unconditional levelwise algebra: `levelValue`, `completedValue_eq_sum_levelValue`,
  `completedValue_norm_le` (`‖K‖ ≤ #R · B` from a uniform per-level bound `B`).
* The analytic socket `PerLevelPhaseSmallZ3221Input` is **uninhabited**; the compiler
  `diKuznetsov_of_perLevelSmallZ` (small-`Z` input + explicit level-count budget
  `#R · levelTarget ≤ X^{39/35−η}`) yields the V17 socket `DIKuznetsov3221Input`.
**`3221-PERLEVEL-SMALLZ-ADAPTER45 : CONDITIONAL_COMPILER`** (Lean-proved; provider open).

## N. Large-range analytic firewall

`LevelwisePhaseLargeRange3221Input` is a separate **uninhabited** interface for regime D.
The proved firewall `smallZ_largeRange_firewall` shows the small-`Z` and large-range inputs
can never both apply to the same source, so a small-`Z` estimate cannot be relabelled as a
large-range one; `largeRange_regime_open` records that no published regime discharges it.
**`PASCADI101-LEVELWISE-PHASE-LARGERANGE45 : OPEN_ANALYTIC / UNINHABITED`.**

## O. Factorial endpoint compiler

`FactorialEndpoint3221SourceAdapter` (SOURCE_OPEN, uninhabited) carries exactly the missing
bridge: the V17 endpoint decomposition **plus** the level-count budget. The Lean-proved
compilers are `factorialEndpoint_of_smallZ` (⇒ `FactorialOmega7SignedEndpoint`) and
`balancedSeven_of_smallZ` (⇒ `BalancedSevenPacketInput`, reusing the V16 implication
unchanged, error channels kept separate as `E + err`). No bridge was fabricated; every
antecedent is uninhabited.

Non-vacuity firewall: `endpoint_not_automatic`, `comparison_not_automatic`,
`perLevelSmallZ_not_automatic` — each open interface genuinely constrains its data.

## P. Comparison firewall

`MuLogComparisonLowCondMatch` is reused, never re-proved and never inhabited. Coefficient
extraction commuting with the expected-term operator (`factorialPolarization_commutes_linearMap`)
is **not** the statement that the factorial expected term equals the physical comparison
term.
**`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_OPEN / UNINHABITED`.**

## Q. Retracted overclaims

Retracted **as controlling status** (provenance kept, nothing deleted):

* `PASCADI101-LEVELWISE-PHASE-LS45 : PASS` → `RETRACTED`;
* `PASCADI102-MOVINGPHASE45 : PASS` → `RETRACTED`;
* `PASCADI39-MOVINGPHASE-EXTENSION45 : PASS` → `RETRACTED`;
* `3221-SOURCE-MOVINGPHASE-DI45 : CLOSED` → `RETRACTED`, now `OPEN_ANALYTIC`.

None of these ever had a Lean witness here: a repository-wide search finds no declaration
mentioning a levelwise or moving phase, and no phase provider is inhabited. They are
replaced by the metadata-only regime dictionary A/B (published), C (conditional provider),
D (open analytic), formalised as labels — never as axioms or Props asserted true.

## R. Build / axiom audit

* `lake build`: **SUCCESS, 8135 jobs, 0 errors** (baseline 8131).
* Repository-wide scan of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, `native_decide`, `@[implemented_by]`: **zero occurrences in Lean code** — every
  match is documentation prose.
* `#print axioms` is emitted at build time for all 25 principal new theorems
  (`RequestProject/Status/Erdos287V18Status.lean`); each reports a subset of
  `[propext, Classical.choice, Quot.sound]` (one reports no axioms at all). **No user
  axiom anywhere.**

## S. First source open

The dispersion/completion (Poisson) identity for the physical balanced-seven source. Until
it exists in the repository, `BalancedSeven3221NormalForm` cannot be inhabited, `ω` has no
literal formula and `Z_3221` has no value.

## T. First analytic open

`PerLevelPhaseSmallZ3221Input` for the pinned source in the small-`Z` range (regime C); and,
strictly separately, `LevelwisePhaseLargeRange3221Input` (regime D) and the V17
`DIKuznetsov3221Input`.

## U. Next unique action

Derive, inside the repository, a completed finite Fourier/Poisson identity for the `m`-box
of the 3221 source expressed in the objects already defined here (`levelValue`, `phase`,
`kloostermanLike`), i.e. produce the first genuine inhabitant of
`BalancedSeven3221NormalForm` from repository definitions rather than from nomenclature.

## V. Final ledger

```
REGRESSION: PASS (no V15/V16/V17 statement edited; append-only + 4 import lines)
BUILD: SUCCESS (8135 jobs, 0 errors)
SORRY: NONE
USER AXIOMS: NONE

FACTORIAL EULER: PROVED_ALGEBRAIC
EXPECTED-TERM LINEARITY: PROVED_ALGEBRAIC
3221 GROUPING: PROVED_FINITE
3221 EXPONENT LEDGER: PROVED_ALGEBRAIC / CAPACITY_ONLY
SOURCE-ASSISTED DIAGONAL: PROVED_FINITE / CAPACITY_ONLY
OFFDIAGONAL t: PROVED_FINITE / CAPACITY_ONLY
EH NO-WRAP: PROVED_FINITE
EH RATIO ENERGY: CONDITIONAL_FINITE
LITERAL 3221 NORMAL FORM: SOURCE_BLOCKED
omega FORMULA: SOURCE_OPEN
Z_3221: SOURCE_OPEN
SMALL-Z RANGE ADAPTER: CONDITIONAL_COMPILER
LEVELWISE LARGE-RANGE PHASE: OPEN_ANALYTIC
3221 ANALYTIC CHILD: OPEN_ANALYTIC
FACTORIAL ENDPOINT: OPEN_ANALYTIC
COMPARISON: SOURCE_OPEN
BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```
