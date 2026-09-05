# ERDŐS #287 — V17 · 3221 SOURCE-ASSISTED DISPERSION SAFE BANK

**ERDŐS #287 REMAINS OPEN.**  Nothing in this run proves #287, Balanced7, the factorial
signed endpoint, the comparison match, or any Deshouillers–Iwaniec / Kuznetsov estimate.
No user axiom was introduced anywhere.

---

## A. BASELINE / REUSED V16 BANK

Baseline (before any edit): `lake build` succeeded with **8123 jobs, zero errors**, branch
`main`, single commit history.

Located and reused, unchanged:

* `RequestProject/Erdos287/FactorialEulerPolarization.lean` —
  `ordFact`, `mem_ordFact_iff`, `factorialEulerPolarization_seven` (the ordered seven-prime
  source of the regrouping);
* `RequestProject/Erdos287/FactorialEulerLocal.lean`,
  `FactorialPolarizationLinearity.lean`, `PascadiParameterLedger.lean`;
* `RequestProject/Status/Erdos287V16Status.lean` —
  `FactorialOmega7SignedEndpoint`, `BalancedSevenPacketInput`,
  `balancedSeven_of_factorialEndpoint_and_comparison` (reused, **not** re-proved);
* `RequestProject/Status/Erdos287V15Status.lean` — `MuLogComparisonLowCondMatch`.

**Search result — named prerequisites that do not exist in this repository.**
`UnconditionalDivisorBound.lean`, `FixedDepthConvolution.lean` and
`card_divisors_in_range_le_mul_rpow` are **absent**; so are any product-energy /
finite-fibre energy bank, any residue-class interval count theorem, and any completed
Fourier/Poisson identity.  Nothing was assumed to exist: the required finite divisor and
energy facts were proved from scratch in Phase B, and the missing Poisson source is
reported, not fabricated.

No V15/V16 theorem statement was edited.  Work is append-only apart from eight import
lines in `RequestProject/Main.lean`.

### Files added

```
RequestProject/Erdos287/Exponent3221Ledger.lean
RequestProject/Erdos287/BalancedSeven3221Grouping.lean
RequestProject/Erdos287/SourceAssistedDiagonal3221.lean
RequestProject/Erdos287/OffDiagonal3221.lean
RequestProject/Erdos287/EHNoWrap3221.lean
RequestProject/Erdos287/DIKuznetsov3221Interface.lean
RequestProject/Erdos287/BalancedSeven3221Compiler.lean
RequestProject/Status/Erdos287V17Status.lean
ERDOS287_3221_V17_SAFE_BANK_REPORT.md
```

Files edited: `RequestProject/Main.lean` (imports only).

---

## B. 1+2+2+2 LABELLED REGROUPING

`RequestProject/Erdos287/BalancedSeven3221Grouping.lean`.

* `blockE = {0}`, `blockM = {1,2}`, `blockN = {3,4}`, `blockL = {5,6}`;
  `block_card_sum : 1 + 2 + 2 + 2 = 7`, `blocks_disjoint`, `blocks_cover`.
* `grouped_product_eq : e · m · n · ℓ = p₀p₁p₂p₃p₄p₅p₆`.
* `prod_apply_tuples` — the exact expansion of an iterated Dirichlet convolution over
  **ordered** tuples with prescribed product (proved by induction with an explicit
  `Fin.cons` bijection).  This is the engine that keeps multiplicities exact and is
  reusable at any arity.
* `sevenfold_tuples_eq_ordFact` — the prime restriction lives in the coefficients, so the
  unrestricted tuple sum equals the sum over `ordFact 7 m` of the V16 bank.
* **`sevenfold_regrouping`** —
  `∑_{t ∈ ordFact 7 m} ∏ᵢ ωᵢ(tᵢ) = ∑_{e·a·b·c = m} η(e) α(a) β(b) γ(c)`
  with `η = g₀`, `α = g₁⋆g₂`, `β = g₃⋆g₄`, `γ = g₅⋆g₆` the exact prime-restricted
  convolutions.  `tuples_four_product` records `e·a·b·c = m` for every term.

Cross-check: at `m = 192 = 2^6·3` (`Ω = 7`) both sides of `sevenfold_regrouping` evaluate
to `1511208` for the test weights `ω_i(p) = p + i + 1`.

**MULTIPLICITY FIREWALL (mandatory, discharged).**  `grouping_not_injective` exhibits the
two distinct ordered prime seven-tuples `(2,2,3,3,3,3,3)` and `(2,3,2,3,3,3,3)` with the
same `(e,m,n,ℓ)`: the pair-product map is **not** injective, and no step in the bank uses
injectivity.  The regrouping is proved as a convolution identity, so repeated primes and
factor permutations are handled by the coefficients, not by a bijection.

Status: **`BALANCED7-3221-GROUPING45 : PROVED_FINITE / PROVED_ALGEBRAIC`.**

---

## C. COEFFICIENT MULTIPLICITY / DIVISOR BOUNDS

* `alpha_apply_prime_pairs`, `beta_apply_prime_pairs`, `gamma_apply_prime_pairs` —
  `α(a) = ∑_{p₁p₂ = a, both prime} ω₁(p₁)ω₂(p₂)`, etc.
* **`alpha_not_one_bounded`** — with all weights `1`, `α(6) = 2`.  So `α, β, γ` are
  provably **not** 1-bounded; the Pro run's phrasing must not be read that way.
* `alpha_norm_le_card_divisors` — the correct majorant for unimodular weights:
  `‖α(a)‖ ≤ τ(a)`.
* `productFibre_card_le` (Phase B) — the triple-product fibre `#{(e,n,ℓ) : enℓ = w} ≤ τ(w)²`.

No fixed-depth divisor majorant exists in the repository; the two bounds above are the
honest replacements and are proved, not assumed.  **No `X^{o(1)}` object is defined
anywhere in Lean.**

---

## D. EXACT EXPONENT LEDGER

`RequestProject/Erdos287/Exponent3221Ledger.lean` (exact `ℚ`).

| statement | theorem |
| --- | --- |
| `E+M+N+L = 1` | `exponents_sum_one` |
| `W = E+N+L = 5/7` | `Wexp_eq` |
| `W − Q = 4/35` | `Wexp_sub_Qexp` |
| `H = Q − M = 11/35` | `Hexp_eq` |
| `E + H = 16/35` | `Eexp_add_Hexp` |
| `E + H < Q`, margin `1/7` | `Eexp_add_Hexp_lt_Qexp`, `noWrap_margin` |
| `T = 4/35` | `Texp_eq` |
| `(W−Q)/2 = 2/35` | `diagonal_amplitude_margin` |

---

## E. STANDARD Q<NL DEFECT

At the aggregate triple point `M' = EM = X^{3/7}`, `N = L = X^{2/7}`, `Q = X^{3/5}`:

* `Mprimeexp_eq : M' = 3/7`, `Nexp_add_Lexp : N+L = 4/7`;
* **`range_defect : (N+L) − Q = −1/35`** — the unique first range-defect candidate;
* transcribed zero-epsilon margins, each proved exactly:
  `margin_Q_half = 1/10`, `margin_two_thirds = 2/21`, `margin_three_four = 19/35`,
  `margin_one_minus_Q = 4/35`, `margin_two_two = 2/35`.

The `θ = 7/32` spectral inequality margin was **not** formalised: the Pro input supplies the
value `θ = 7/32` but no transcribed inequality, and nothing was reconstructed.  Reported as
a source gap (§S).

Status: **`PASCADI41-3221-RANGE-LEDGER : PROVED_ALGEBRAIC / CAPACITY_ONLY`.**  Pascadi
Theorem 4.1 is not formalised and is not asserted to fail; the earlier V16
`PASCADI-Q3/5-Y1/7-PARAMETER-NOGO` ledger is untouched.

---

## F. SOURCE-ASSISTED DIAGONAL

`RequestProject/Erdos287/SourceAssistedDiagonal3221.lean`.

* `fiberwise_energy_le` — exact: `∑_j |∑_{g=j} c|² ≤ F · ∑ |c|²` when all fibres have `≤ F`
  elements (Cauchy–Schwarz per fibre + `sum_fiberwise`).
* `productFibre_card_le` — `#{(e,n,ℓ) : e n ℓ = w} ≤ τ(w)²` for `w ≠ 0`.
* `pushforward_energy_le` — `∑_w |u(w)|² ≤ D_v² ∑ |c|²` for `u(w) = ∑_{enℓ=w} c(e,n,ℓ)`.
* `diagonalParent`, `diagonalParent_eq`, `diagonal_parent_bound` —
  `∑_{q,m,w} |u(w)|² 1_{mw ≡ a (q)} ≤ D_max · #Mbox · ∑_w |u(w)|²`.
* `sourceAssisted_diagonal_finite` — the composition
  `≤ D_max · #Mbox · (D_v² · ∑ |c|²)`.
* Exponent level: `diagonal_exponent_identity`
  (`M√(QENL) = X√(Q/(ENL))`) and `diagonal_exponent_value` (`1 + (Q−W)/2 = 1 − 2/35`).

`D_max` and `D_v` are **hypotheses**, so the diagonal is banked as
**`3221-SOURCE-ASSISTED-DIAGONAL45 : PROVED_FINITE + CAPACITY_ONLY`**, never as an
unconditional analytic estimate.

---

## G. OFF-DIAGONAL t PARAMETER

`RequestProject/Erdos287/OffDiagonal3221.lean`, all over `ℤ`:

* `offdiag_existsUnique_t` — unique `t` with `w₁ − w₂ = q t` given `w₁ ≡ w₂ (q)`, `q ≠ 0`;
* `offdiag_t_ne_zero`, `offdiag_ne_of_t_ne_zero` — `t ≠ 0` exactly off the diagonal.

No truncated natural subtraction is used anywhere.

---

## H. t-RANGE

* Finite layer: `offdiag_abs_t_le : |t| · Q_min ≤ 2 W_max`, and the rational form
  `offdiag_abs_t_le_div : |t| ≤ 2 W_max / Q_min`.
* Dyadic layer: **only** `Texp = 5/7 − 3/5 = 4/35` (`texp_value`).  No asymptotic dyadic
  theorem is claimed: the repository has no interval/dyadic machinery to support one.

Status: **`3221-OFFDIAGONAL-T-RANGE45 : PROVED_FINITE + CAPACITY_ONLY`.**

---

## I. (e,h) NO-WRAP

`RequestProject/Erdos287/EHNoWrap3221.lean`:

* `ratio_eq_iff_cross` (arbitrary commutative ring, `e`'s literal units) and its `ZMod q`
  instance: `h₁e₁^{-1} = h₂e₂^{-1} ↔ h₁e₂ = h₂e₁`.  Every inverse-domain hypothesis is
  explicit.
* `nowrap_eq_of_dvd_of_abs_lt` — generic integer rigidity: `q ∣ a−b` and `|a−b| < |q|`
  imply `a = b`.  The size hypothesis is literal and is **not** inferred from exponents.
* `nowrap_cross_eq` — the physical instance.
* `eh_lt_q_capacity` — `E+H = 16/35 < 21/35 = Q`, margin `1/7`, **capacity only**: the
  repository has no "power beats fixed constants" lemma tying dyadic constants to the
  literal size hypothesis, so every no-wrap application below stays conditional on the
  literal hypothesis.

---

## J. RATIO-FIBRE ENERGY HOSTILE AUDIT

The Pro claim `∑_λ |∑_{he^{-1}=λ} a_e b_h|² ≪ E H X^{o(1)}` was **not** banked as stated.
It was re-derived from the arithmetic:

* `ratioCollision_samePrime` — `e₁ = e₂` forces `h₁ = h₂`;
* `ratioCollision_distinctPrimes_param` — for distinct primes, coprimality forces
  `e₁ ∣ h₁`, `e₂ ∣ h₂` and `h₁ = c e₁`, `h₂ = c e₂` with a **common** integer `c`;
  `ratioCollision_param_div` makes `c = h₁/e₁` explicit;
* `ratioCollision_card_bound` —
  `#{collision quadruples} ≤ #E·#H + (#E)²·#C`, `C = [−H_max/E_min, H_max/E_min]`,
  `cBox_card : #C = (2⌊H_max/E_min⌋+1)`;
* `card_collision_eq_sum_sq`, `energy_le_collision_card`,
  **`ehRatioEnergy_le_explicit`** — the energy is at most that count.

**Verdict.**  At the 3221 parameters `#E ≈ E`, `#C ≈ H/E`, so the bound reads
`≈ E H + E² · (H/E) ≈ E H`: the claimed order is reproduced **with no divisor factor and
no `X^{o(1)}` loss at all** — the finite result is *stronger* than the claim in that
respect.  No extra polynomial factor appears, so the Pro claim is **not retracted**.
However it is banked as **`3221-EH-NOWRAP-ENERGY45 : CONDITIONAL_FINITE`**, because the
no-wrap step is carried as the explicit hypothesis
`r x = r y → h₁e₂ = h₂e₁` (equivalently the literal `|h₁e₂ − h₂e₁| < |q|`), which the
exponent ledger does not discharge by itself.

---

## K. COMPLETED SOURCE STATUS

A repository-wide search for a completed Fourier/Poisson source
(`poisson`, `fourier`, additive characters, `e_q(·)`, `Complex.exp` phases) returns
**nothing**.  The post-Poisson expression of the Pro run was therefore **not** created as a
theorem.

Instead `Erdos287.DI3221.BalancedSeven3221CompletedSource` is a *source dictionary* whose
fields are concrete data and concrete conditions — boxes, shift, exact parent value, exact
completed value, the routed-error completion inequality, `t ≠ 0`, the `|t|` support (the
Phase C inequality), the `|h|` support, unit/inverse support, `h = 0` separation, nonunit
routing and low-conductor separation.  There is **no free `Prop` field**, and **no physical
instance is constructed**.  `parent_norm_le` and `t_range_of_source` are the only theorems
about it.

Status: **`3221-COMPLETED-SOURCE-DICTIONARY45 : SOURCE_OPEN`.**

---

## L. DI/KUZNETSOV SOCKET

`Erdos287.DI3221.DIKuznetsov3221Input S X η` — a `Prop`-valued structure attached to a
*specific* dictionary `S`, stating `‖S.completedValue‖ ≤ X^{39/35 − η}` with `η > 0`.
It is **never inhabited**, it is **not** an `axiom`, and it is not a generic Kuznetsov
statement.  `preSplice_target_gap` records that `39/35 − 1 = 4/35 = Texp`.

§17 metadata: `DISlotAssignment` records the `r,s,m,n,c` slots with modulus factorisation
and coprimality.  Proved counterguards:

* `slot_dependence_counterguard` — a coefficient family that genuinely depends on the `c`
  slot cannot be rewritten as a `c`-independent family;
* `zeroMode_separation_guard` — re-adding `h = 0` changes the sum unless the zero mode
  vanishes;
* `modulus_factorisation_not_unique` — `6 = 1·6 = 2·3` coprimely, so the `(r,s)` slots must
  be carried as data, never inferred.

Status: **`3221-DI-KUZNETSOV-LITERAL-SPLICE45 : OPEN_ANALYTIC / UNINHABITED`.**

---

## M. 3221 → FACTORIAL ENDPOINT COMPILER

`RequestProject/Erdos287/BalancedSeven3221Compiler.lean`.

The V16 `FactorialOmega7SignedEndpoint` could **not** be derived from the 3221 child
without an extra source decomposition, so that bridge was made explicit rather than
fabricated:

* `Endpoint3221Decomposition` (`SOURCE_OPEN`, never inhabited) — `|S_fac| ≤ ‖parent‖ +
  routedError` and `X^{39/35−η} + 2·routedError ≤ E`;
* `factorialEndpoint_of_3221` — dictionary + DI input + decomposition ⇒ the V16 endpoint;
* `balancedSeven_of_3221` — then + `MuLogComparisonLowCondMatch` ⇒
  `BalancedSevenPacketInput`, by **reusing** the V16 theorem
  `balancedSeven_of_factorialEndpoint_and_comparison` (error channels kept separate,
  `E + err`);
* `regrouping_is_unconditional` — the regrouping enters as a *fact*, not an antecedent.

Nothing in this phase inhabits any analytic or source antecedent.

---

## N. COMPARISON SOURCE AUDIT

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 : SOURCE_BLOCKED`.

The physical #287 comparison is **absent** from the repository.  Exactly missing (searched
by name and by shape): a definition of the physical comparison sequence `B(n)` (and
`4B(n)`), of `M_phys`, of the principal local density, of the small-conductor subtraction,
of the exceptional-character convention, and of the unit/nonunit routing at the physical
level.  Nothing was invented, no expected term was chosen retrospectively, and the
polarization was **not** redone: the V16 theorem
`factorialPolarization_commutes_linearMap` already covers every linear expected-term
operator and remains the only banked statement in that direction.  Phase G therefore
produced no new Lean file.

---

## O. RETRACTIONS / CORRECTIONS

* **No retraction.**  Every Pro candidate audited in this run either checks in the finite
  form banked here or is explicitly downgraded to `CAPACITY_ONLY` / `CONDITIONAL_FINITE`.
* Correction of emphasis: `α, β, γ` are **not** 1-bounded (`alpha_not_one_bounded`), and the
  grouped map is **not** injective (`grouping_not_injective`).  Any later argument using
  either property is invalid.
* `PASCADI41-UNIQUE-RANGE-FAIL45` is banked only as the rational ledger
  `PASCADI41-3221-RANGE-LEDGER`; the analytic theorem is neither proved nor refuted.
* Named prerequisites `UnconditionalDivisorBound.lean`, `FixedDepthConvolution.lean`,
  `card_divisors_in_range_le_mul_rpow` do not exist in this repository; the finite facts
  they were meant to supply were proved directly.

---

## P. AXIOM AUDIT

`#print axioms` is emitted at build time for the 68 principal new theorems in
`RequestProject/Status/Erdos287V17Status.lean`.  Across the whole repository every report
is a subset of `[propext, Classical.choice, Quot.sound]`.  A repository-wide scan of all
Lean sources for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`,
`@[implemented_by]` finds **zero occurrences in Lean code** (all matches are documentation
prose).

---

## Q. BUILD

`lake build` succeeds: **8131 jobs, zero errors**, no `sorryAx` in the build log
(baseline was 8123 jobs).

---

## R. FIRST FORMAL BLOCKER

None inside the safe bank: every finite/algebraic statement attempted in Phases A–F is
proved.  The first *formal* gap is the missing bridge that had to be introduced as
`Endpoint3221Decomposition`: the V16 endpoint value is a real number `S_fac` with no
declared relation to any complex completed sum, so no Lean derivation exists without that
extra field.

---

## S. FIRST SOURCE BLOCKER

The completed post-Poisson source: there is no Fourier/Poisson identity in the repository
from which the off-diagonal completed value can be derived, so
`BalancedSeven3221CompletedSource` remains a dictionary with no physical inhabitant.
Second source blocker (Phase G): the physical comparison objects `B(n)`, `M_phys`, the
principal local density, the small-conductor subtraction and the exceptional-character
convention.  The `θ = 7/32` spectral inequality is a third, minor, source gap: no formula
was supplied to transcribe.

---

## T. FIRST ANALYTIC BLOCKER

```
3221-DI-KUZNETSOV-LITERAL-SPLICE45
```

i.e. inhabiting `Erdos287.DI3221.DIKuznetsov3221Input S X η` for a physical dictionary `S`
— the bound `‖O_pre‖ ≤ X^{39/35−η}` for the completed nondegenerate off-diagonal sum.

---

## U. NEXT EXACT ACTION

Produce, in the repository, a **completed finite Fourier/Poisson identity** for the `m`-box
of the 3221 arrangement — an exact equality between the source parent value and the
completed value plus routed errors, in terms of objects already defined here (boxes, shift,
`t`, `h`).  That single object turns `BalancedSeven3221CompletedSource` from a dictionary
into a constructible record and reduces Balanced7 to the one analytic socket above.

---

## V. FINAL LEDGER

```
REGRESSION: NONE (8123 → 8131 jobs, no V15/V16 statement edited)
BUILD: SUCCESS (8131 jobs, 0 errors)
SORRY: NONE
USER AXIOMS: NONE

FACTORIAL EULER POLARIZATION: PROVED_ALGEBRAIC
3221 LABELLED GROUPING: PROVED_FINITE
3221 COEFFICIENT MULTIPLICITY: PROVED_FINITE
STANDARD Q<NL DEFECT: PROVED_ALGEBRAIC
SOURCE-ASSISTED DIAGONAL: PROVED_FINITE
OFFDIAGONAL t PARAMETER: PROVED_FINITE
t RANGE: PROVED_FINITE
EH<Q CAPACITY: CAPACITY_ONLY
EH NO-WRAP: PROVED_FINITE
EH RATIO ENERGY: CONDITIONAL_FINITE
COMPLETED SOURCE DICTIONARY: SOURCE_OPEN
DI/KUZNETSOV LITERAL SPLICE: OPEN_ANALYTIC
FACTORIAL ENDPOINT: OPEN_ANALYTIC
COMPARISON: SOURCE_BLOCKED
BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```
