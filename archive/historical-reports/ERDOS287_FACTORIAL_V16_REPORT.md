# Erdős #287 — V16 report: the factorial Euler polarization bank

**ERDŐS #287 REMAINS OPEN.** Nothing in this run proves it, nor the balanced-seven packet,
nor any exponent-of-distribution statement, nor Pascadi's theorem, nor its negation.

## 0. Workspace guard

V15 was resumed in place. Every V15 object named in the task was located before any edit:

* `Erdos287.BalancedSeven.coeff_balanced_eq_perm_sum`, `coeff_balanced_scaled`,
  `balancedMonomial`, `balancedSevenMonomial`, `labelledPolynomial`,
  `SquarefreeEncoding` — `RequestProject/Erdos287/BalancedSevenPolarization.lean`,
  `BalancedSevenFinite.lean`;
* `Erdos287.V15Status.PolarizedOmega7SignedEoD`,
  `Erdos287.V15Status.MuLogComparisonLowCondMatch` —
  `RequestProject/Status/Erdos287V15Status.lean`.

No V15 (or earlier) theorem was deleted, weakened, renamed or rewritten. The work is
append-only apart from five import lines in `RequestProject/Main.lean`. No axiom was added.

## 1. Files changed

Added:

* `RequestProject/Erdos287/FactorialEulerPolarization.lean`
* `RequestProject/Erdos287/FactorialEulerLocal.lean`
* `RequestProject/Erdos287/FactorialPolarizationLinearity.lean`
* `RequestProject/Erdos287/PascadiParameterLedger.lean`
* `RequestProject/Status/Erdos287V16Status.lean`
* `ERDOS287_FACTORIAL_V16_REPORT.md` (this file)

Edited:

* `RequestProject/Main.lean` — five import lines only.

## 2. Retirement (task item 1)

The V15 working note *"complete multiplicativity is required for the polarized seven-box
encoding"* is **retired as controlling**. It is not deleted and nothing that was proved
under it is withdrawn: the squarefree labelled polarization and the `SquarefreeEncoding`
interface remain exactly as banked and remain valid mathematics. Only the status label
changes: the squarefree restriction is no longer the obstruction of record, because the
divided-power polarization below handles repeated primes head-on.

## 3. Theorems proved (all sorry-free, kernel-checked)

### 3.1 Factorial Euler polarization — `OMEGA7-FACTORIAL-EULER-POLARIZATION45 : PROVED_ALGEBRAIC`

File `RequestProject/Erdos287/FactorialEulerPolarization.lean`, over an arbitrary
characteristic-zero field `K` (so that `e!` is invertible; `ℂ` instantiated separately) —
never over a bare semiring.

| name | statement |
| --- | --- |
| `Erdos287.FactorialEuler.linForm`, `divPowerFactor`, `Fdiv` | `L_p = ∑_i ω_i(p) z_i`, `L_p^e / e!`, and its multiplicative extension |
| `Fdiv_primePow`, `Fdiv_one` | the extension really is `a^e/e!` at prime powers |
| `ordFact`, `mem_ordFact_iff` | the finset of **ordered** prime `N`-tuples with product `m`, certified to be exactly that |
| `count_eq_factorization` | in an ordered factorisation, `v` occurs `v_p(m)` times |
| `exists_perm_comp` | equal fibre cardinalities ⟹ the tuples differ by a permutation |
| `image_perm_eq_ordFact` | the permutation orbit of one listing is all of `ordFact N m` |
| `fiber_card_eq` | every fibre of `σ ↦ q∘σ` has cardinality `∏_p v_p(m)!` (via `DomMulAct.stabilizer_card'`) |
| `factorialEulerPolarization_of_listing` | core identity, given an explicit listing |
| `exists_prime_listing` | `Ω(m) = N` produces a listing |
| **`factorialEulerPolarization`** | `[z_1⋯z_N] Fdiv N om m = ∑_{f ∈ ordFact N m} ∏_i ω_i(f i)` for `Ω(m) = N` |
| `azForm`, `Fz7`, `Fz7_primePow`, `Fz7_eq_Fdiv` | the normalisation `a_z(p) = (1/7)∑_i z_i ω_i(p)` |
| **`factorialEulerPolarization_seven`** | `7^7 · [z_1⋯z_7] F_z(m) = ∑_{p_1⋯p_7 = m, ordered} ∏_i ω_i(p_i)` |
| `factorialEulerPolarization_seven_complex` | the same over `ℂ` |
| `cardFactors_128`, `const_two_mem_ordFact_128`, `factorialEulerPolarization_seven_128` | non-vacuity at the extreme repeated case `128 = 2^7` |

The identity **holds including repeated primes**: the denominators `∏_p v_p(m)!` cancel
exactly the number of permutations of equal prime occurrences, and that cancellation is
`fiber_card_eq`, not an assumption.

### 3.2 Local Euler algebra — formal only

File `RequestProject/Erdos287/FactorialEulerLocal.lean`:
`localSeries`, `coeff_localSeries`, **`localSeries_eq_rescale_exp`** (`∑_e F_z(p^e) T^e =
exp(a T)` as `PowerSeries`), **`derivative_localSeries`** (`d/dT S = a·S`), `localLambda`,
`localLambda_one` (`Λ_{F_z}(p) = a_z(p) log p`), `localLambda_of_two_le`
(`Λ_{F_z}(p^e) = 0`, `e ≥ 2`), `localLambdaSeries_eq_C`, and — so that the `Λ`-data is a
theorem rather than a convention — `localSeries_ne_zero`, `localLambdaSeries_unique` and
`lambda_coeffs_of_logDeriv`: any family satisfying the formal log-derivative equation is
forced to be `a` at `e = 1` and `0` for `e ≥ 2`.

**Not** called a class-`C` statement: this repository contains **no** class-`C` definition,
so per the instruction only the finite/formal prime-power coefficient identity is banked.
No analytic convergence is introduced anywhere.

### 3.3 Expected-term linearity — `POLARIZED-EXPECTED-TERM-LINEARITY45 : PROVED_ALGEBRAIC`

File `RequestProject/Erdos287/FactorialPolarizationLinearity.lean`:
`CoeffFamily`, `balancedExtract`, **`factorialPolarization_commutes_linearMap`**,
`factorialPolarization_commutes_linearMap_seven`, `arithExtend`,
`factorialPolarization_commutes_arith`, `weightedProjection`,
`factorialPolarization_commutes_weightedProjection`.

Abstract and conditional: instantiating `E` covers a principal-character projection, a
finite low-conductor character projection and exceptional-character linear terms. It is
**not** claimed that the physical comparison sequence equals the expected term.

### 3.4 Pascadi parameter no-go — `PASCADI-Q3/5-Y1/7-PARAMETER-NOGO : PROVED_ALGEBRAIC / PARAMETER_LEDGER`

File `RequestProject/Erdos287/PascadiParameterLedger.lean`:
**`pascadi_parameter_eta_le_one_div_4000`**, **`one_div_seven_gt_one_div_4000`**,
**`pascadi_Q_three_fifths_y_one_seventh_incompatible`**, `pascadi_margin_at_one_seventh`
(exact margin `−3993/280`). All arithmetic is exact over `ℚ`.

Pascadi's analytic theorem is **not** formalised, and nothing here says it fails; the
statements are about the parameters only.

### 3.5 Conditional compiler

File `RequestProject/Status/Erdos287V16Status.lean`:
**`balancedSeven_of_factorialEndpoint_and_comparison`** — factorial endpoint input **+**
comparison-match input **⇒** `BalancedSevenPacketInput`, with the two error channels kept
separate (`E + err`, never merged). Both antecedents are uninhabited, so the compiler
inhabits nothing.

## 4. Open / blocked interfaces (never inhabited)

| tag | object | status |
| --- | --- | --- |
| `AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45` | `Erdos287.V16Status.FactorialOmega7SignedEndpoint` | `OPEN_ANALYTIC` |
| `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` | `Erdos287.V15Status.MuLogComparisonLowCondMatch` | `SOURCE_BLOCKED / OPEN` |
| (superseded, kept) | `Erdos287.V15Status.PolarizedOmega7SignedEoD` | `OPEN_ANALYTIC` |
| `BALANCED7` | `Erdos287.V16Status.BalancedSevenPacketInput` | `CONDITIONAL / OPEN` |

No Bombieri–Vinogradov, DGS, Pascadi, Kuznetsov, large-value, Gate1A/1B, `WindowPairSupply`
or FCL statement is assumed or proved anywhere in V16.

## 5. Audit

* `lake build` succeeds: 8123 jobs, **zero errors**.
* Repository-wide scan of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, `native_decide`, `@[implemented_by]`: **zero occurrences in Lean code** — every
  match is documentation prose.
* `#print axioms` is emitted at build time for all 32 principal new theorems (V16 status
  file). Across the whole repository, all 443 printed reports list only
  `[propext, Classical.choice, Quot.sound]` (or a subset). No `sorryAx`.

## 6. Status ledger

```
OMEGA7-FACTORIAL-EULER-POLARIZATION45      : PROVED_ALGEBRAIC
OMEGA7-FACTORIAL-LOCAL-EULER45             : PROVED_ALGEBRAIC (formal power series only)
POLARIZED-EXPECTED-TERM-LINEARITY45        : PROVED_ALGEBRAIC
PASCADI-Q3/5-Y1/7-PARAMETER-NOGO           : PROVED_ALGEBRAIC / PARAMETER_LEDGER
AFFINE287-FACTORIAL-OMEGA7-SIGNED-ENDPOINT45 : OPEN_ANALYTIC
AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_BLOCKED / OPEN
BALANCED7                                  : CONDITIONAL / OPEN
ERDOS287                                   : OPEN
```

No statement was found false; no target failed.
