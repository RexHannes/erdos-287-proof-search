# ERDŐS #287 — V19 SAFE BANK REPORT
## Pre-Poisson divisor density / high-conductor variance / Balanced7 compiler

**ERDŐS #287 REMAINS OPEN.  BALANCED7 REMAINS OPEN.**
Nothing in V19 proves either, and no analytic or source interface is inhabited anywhere.
No `axiom` was added.  Work is append-only.

---

## A. REGRESSION

Pre-edit state: branch `main`, working tree clean, `lake build` **succeeded, 8135 jobs, 0
errors**.

Every prerequisite named in the task was located and reused **unchanged**:

`RequestProject/Erdos287/FactorialEulerPolarization.lean`,
`FactorialEulerLocal.lean`, `FactorialPolarizationLinearity.lean`,
`PascadiParameterLedger.lean`, `NormalForm3221.lean`, `MovingPhaseProvider3221.lean`,
`FactorialEndpoint3221Adapter.lean`, `RequestProject/Status/Erdos287V18Status.lean`, and
the whole V17 3221 finite/exponent bank (`Exponent3221Ledger.lean`,
`BalancedSeven3221Grouping.lean`, `SourceAssistedDiagonal3221.lean`,
`OffDiagonal3221.lean`, `EHNoWrap3221.lean`, `DIKuznetsov3221Interface.lean`,
`BalancedSeven3221Compiler.lean`).

No existing theorem was restated under a new name, weakened, renamed or deleted.  The seven
prime polarization was **not** redone: `Erdos287.Grouping3221.grouped_product_eq` is reused
verbatim by `Erdos287.PrePoisson3221.prePoisson_grouping_product`, and the V17 exponents
`Erdos287.Ledger3221.*` are reused verbatim by the new `39/35` ledger.

Post-edit: `lake build` **succeeds, 8140 jobs, 0 errors** (five new modules).

### Exact files changed

Added:

* `RequestProject/Erdos287/PrePoissonDensity3221.lean`
* `RequestProject/Erdos287/HighConductorVariance3221.lean`
* `RequestProject/Erdos287/CharacterGram3221.lean`
* `RequestProject/Erdos287/BalancedSevenV19Compiler.lean`
* `RequestProject/Status/Erdos287V19Status.lean`
* `ERDOS287_V19_PREPOISSON_HIGHCOND_SAFE_BANK_REPORT.md` (this file)

Edited: `RequestProject/Main.lean` — **five import lines only**.

---

## B. FRONTIER RESET

The V18 record is preserved in full and is **not** declared false.  The new V19 layer marks
it *superseded as the controlling frontier*:

| node | V19 label |
|---|---|
| `V18_NORMALFORM_SMALLZ` | `HISTORICAL / SUPERSEDED AS CONTROLLING FRONTIER` |
| `3221-DI-NORMALFORM45` | `SOURCE_MISMATCH` for the reconstructed physical route |
| `PASCADI101-LEVELWISE-PHASE-SMALLZ45` | `CONDITIONAL PROVIDER METADATA, NOT CURRENTLY REQUIRED` |
| `3221-SPARSE-RECIPROCAL-KF-DICTIONARY45` | `RETIRED AS CURRENT ROUTE` |

These are recorded machine-readably as `Erdos287.V19Status.ledger`, a function on a finite
index type.  **No theorem converts a ledger value into a mathematical claim**, so no
analytic falsity is derived from metadata.  `v18_route_superseded_not_refuted` proves only
that the "superseded" label is distinct from the "proved", "open" and "open-analytic"
labels.

`controlling_analytic_node_unique` proves that
`3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45` is the **unique** node carrying `OPEN_ANALYTIC`.

---

## C. AFFINE DIVISOR IDENTITY  (Phase B, `PrePoissonDensity3221.lean`)

`Erdos287.PrePoisson3221.isCoprime_two_of_odd` — odd `q` is coprime to `2`.

`Erdos287.PrePoisson3221.affineResidue_iff_dvd_two_mul_add` — **load-bearing**.  For odd `q`
and any `a` with `2a ≡ −s (mod q)`:

```
m·w ≡ a (mod q)   ↔   q ∣ 2·m·w + s
```

`Erdos287.PrePoisson3221.balancedSeven_affine_divisor_condition` — the specialisation to
`s = ±1` used by the balanced-seven source, stated through the predicate `AffineSampled`.

`Erdos287.PrePoisson3221.exists_affineResidue` — the affine residue exists for every odd
`q` (non-vacuity).

No analytic estimate is used or produced.

---

## D. FIRST CAUCHY / MU-SIGN  (Phase C, `HighConductorVariance3221.lean`)

`Erdos287.HighCond3221.firstCauchy_sign_consumption`:

```
‖∑_q mu(q) X_q‖² ≤ (∑_q mu(q)²) · (∑_q ‖X_q‖²)
```

The right-hand side depends on `mu` **only through `mu(q)²`**.

`postCauchy_weight_sign_invariant` — the post-Cauchy weight is invariant under arbitrary
`q`-wise sign flips `mu ↦ ε·mu`, `ε = ±1`.

`moebius_sq_of_squarefree` — for squarefree `q`, `μ(q)² = 1` (Mathlib result, reused).

`firstCauchy_loses_sign_information` — **firewall**: explicit weight systems with identical
post-Cauchy energies but different pre-Cauchy values.  The original signed `μ(q)` is
provably not retained by the post-Cauchy variance.

Status: `3221-FIRST-CAUCHY-SIGN-CONSUMPTION45 : PROVED_FINITE / PROVED_ALGEBRAIC`.
No Möbius analytic property is formalised or assumed.

---

## E. HIGH-CONDUCTOR RESIDUE SOURCE  (Phase D)

`Erdos287.HighCond3221.residueSum q Wbox c a = ∑_{w ≡ a (q)} c(w)` — the exact finite
residue sum, with `residueSum_sum_over_classes` (`∑_a C_q(a) = ∑_w c(w)`).

Dirichlet-character infrastructure **is** available in this build (`DirichletCharacter`,
`DirichletCharacter.conductor`, full orthogonality), so **no free `Prop` placeholder was
created**.  The projection is defined *literally* in `CharacterGram3221.lean`
(`lowSet`, `highSet`, `cLow`, `cHigh`) and the decomposition

```
C_q = C_q^{≤D} + C_q^{>D}
```

is **proved** (`residueSum_eq_cLow_add_cHigh`) from the proved orthogonality expansion
`totient_mul_residueSum_eq_sum_char`.

---

## F. RR/RK/KK REASSEMBLY  (Phase D §7)

`Erdos287.HighCond3221.normSq_sub_reassembly`:

```
|R − K|² = |R|² − 2·Re(R·conj K) + |K|²
```

`Erdos287.HighCond3221.highConductorEnergy_reassembles_crossTerms` lifts this to the finite
weighted `(q, m)` energy: `RR − RK − KR + KK` is one square of the reconstructed
high-conductor remainder.

Status: `PROVED_ALGEBRAIC` only.  **No claim is made that the physical comparison term is
thereby matched.**

---

## G. DIVISOR-DENSITY COUNT  (Phase E §8)

`Erdos287.PrePoisson3221.sampled_q_card_le_divisorCount` — any finite family of natural
moduli dividing a fixed nonzero `n` has cardinality `≤ τ(|n|)` (`Nat.divisors` card).
No interval hypothesis is required, so the bound holds for the moduli in **any** interval.

`sampled_q_card_le_divisorCount_affine` — the affine instance: with `q ∣ 2mw + s` and
`2mw + s ≠ 0`, the admissible-`q` count is `≤ τ(|2mw + s|)`.

`τ(n) = X^{o(1)}` is **not** proved and **not** assumed.  It is exposed separately as the
uninhabited arithmetic input `DivisorGrowthInput eps n₀`; nothing above depends on it.

---

## H. SECOND-COPY COUNT  (Phase E §9)

`secondCopy_shell_iff` — `q ∣ w₁ − w₂ ↔ ∃ t, w₂ = w₁ − q·t`.

`congruence_interval_card_le` — the exact division-free count over `ℤ`:

```
q · #{x ∈ [a, b) : x ≡ r (mod q)} ≤ (b − a) + q      (0 < q, a ≤ b)
```

`congruence_interval_card_le_one_add_quotient` — the floor variant `# ≤ 1 + (b − a)/q`.

`secondCopy_card_le_one_add_quotient` — the shell form for `w₂` in a `ℤ` box.

All statements are `Nat`/`Int` interval theorems; **no informal real interval arithmetic is
used**.

**Combination (Phase E §10):** `sampledQuadBox_card_le`

```
#{(m, w₁, q, w₂)} ≤ (#m)·(#w₁)·divisorMultiplicity·secondCopyMultiplicity
```

with **no `X`-exponent inside the theorem**.

---

## I. 39/35 NATURAL-SCALE LEDGER  (Phase F §11)

Reusing `Erdos287.Ledger3221` exponents unchanged
(`Mexp = 2/7`, `Wexp = Eexp+Nexp+Lexp = 5/7`, `Qexp = 3/5`, `Texp = Wexp−Qexp = 4/35`):

* `Mexp_thirtyfifths : 10/35`, `Wexp_thirtyfifths : 25/35`, `Texp_thirtyfifths : 4/35`,
  `Qexp_thirtyfifths : 21/35`, `two_Texp : 8/35`;
* `thirtyfifths_sum : 10/35 + 25/35 + 4/35 = 39/35`;
* `prePoisson_density_exponent : Mexp + Wexp + Texp = 39/35`;
* `cauchy_prefactor_exponent : Qexp + Mexp = 31/35`;
* `highCond_naturalScale_exponent : Qexp + Mexp + 2·Texp = 39/35`;
* `naturalScale_matches_density` — the two `39/35` routes agree.

Status: `PROVED_ALGEBRAIC / CAPACITY_ONLY`.  No real-power asymptotic claim is hidden in any
finite theorem.

---

## J. RETIRED KF CAPACITY ARITHMETIC  (Phase F §12)

* `BC3221_capacity_deficit_arithmetic : 437/350 − 390/350 = 47/350 ∧ 0 < 47/350`
* `DRZ3221_capacity_deficit_arithmetic : 523/420 − 468/420 = 11/84 ∧ 0 < 11/84`

Status: `PROVED_ALGEBRAIC / EXTERNAL-THEOREM CAPACITY METADATA ONLY`.
**Bettin–Chandee and Duke–Rudnick–Zhang are not formalised, not assumed and not
axiomatised.  No conclusion about the applicability or non-applicability of any external
theorem is drawn from Lean.**

---

## K. INVERSE-SAMPLED VARIANCE SOCKET  (Phase G §13–§14)

`Erdos287.HighCond3221.InverseSampledHighCond3221Data` — **pure data**: `Qbox`, `Mbox`,
`Wbox`, `sign` (with `sign² = 1`), `coeff`, `CHigh`, `qWeight`, `mWeight`, `conductorCut`,
plus explicit arithmetic side conditions (`q_pos`, `q_odd`, `m_unit`, weight nonnegativity).
**No free `Prop` field.**

`samplePoint q m = −s·(2m)⁻¹` in `ZMod q`, and the load-bearing identification

`samplePoint_iff_affineSampled : (w : ZMod q) = samplePoint q m ↔ q ∣ 2·m·w + s`

which is exactly the Phase-B divisibility, so the socket and the divisor-density count
describe the same object.

`Vhi D = ∑_q qWeight(q) ∑_m mWeight(m) ‖CHigh q (samplePoint q m)‖²`, with `Vhi_nonneg`.

`InverseSampledHighCondLogVar3221Input D naturalScale Lsave` — the **open analytic input**,
whose substantive field is `Vhi D ≤ naturalScale / Lsave` with `0 < Lsave`.  A generic
positive saving parameter is used rather than faked asymptotic notation.

**It is never inhabited.**  A repository-wide search shows it occurs only as a structure
declaration and as a hypothesis.  `highCondLogVar_not_automatic` refutes it on explicit
probe data (`probeData`, `Vhi = 1`, scale `1`, saving `2`).

Status: `3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45 : OPEN_ANALYTIC`.

---

## L. CHARACTER GRAM EXPANSION  (Phase H §15)

Conductor infrastructure is present, so the target is **PROVED_FINITE**, not `SOURCE_OPEN`:

* `cHat q Wbox c χ = ∑_w c(w) χ(w)`;
* `totient_mul_residueSum_eq_sum_char : φ(q)·C_q(a) = ∑_χ χ(a⁻¹) ĉ_q(χ)` for unit `a`;
* `residueSum_eq_cLow_add_cHigh : C_q = C_q^{≤D} + C_q^{>D}` (literal projection equality);
* `gram_expansion` — the exact Gram identity for a finite family;
* `highResidue_energy_gram`:

```
∑_m |C_q^{>D}(a_m)|² = φ(q)^{-2} ∑_{χ,ψ high} ĉ(χ)·conj(ĉ(ψ))·G_M(χ, ψ)
```

* `inverseSampled_highResidue_gram` — the same identity substituted at
  `a = −s·(2m)⁻¹`.

**Nothing is estimated.**  No character-sum bound is proved or assumed.

---

## M. FIVE-BOX FACTORISATION  (Phase H §16)

* `sum_mul_sum4` — a four-fold product of finite sums expands exactly.
* `cHat_fiveBox_factorisation` — for the labelled `1+2+2+2` product box,

```
ĉ(χ) = (∑_e η(e)χ(e))·(∑_a α(a)χ(a))·(∑_b β(b)χ(b))·(∑_c γ(c)χ(c))
```

* `cHat_twoBox_factorisation` — the two-prime convolution inside a pair block factorises
  exactly under the character transform.

Finite algebra only; no character-sum bounds.

---

## N. COMPARISON FIREWALL  (Phase I §18)

`Erdos287.V15Status.MuLogComparisonLowCondMatch` is **reused unchanged and not inhabited**.
`Erdos287.V19Compiler.comparison_stays_independent` re-exposes the V18 refutation
(`Erdos287.EndpointAdapter3221.comparison_not_automatic`) at the V19 layer; it is not a
restatement, it is a reuse.  The two error channels remain separate (`E + err`, never
merged).

---

## O. CONDITIONAL BALANCED7 COMPILER  (Phase I §17–§18)

* `CauchyPrefactor3221Certificate D srcVal prefactor` — the post-Cauchy certificate
  (`0 ≤ prefactor`, `srcVal² ≤ prefactor · Vhi D`).  It is **realisable**, not postulated:
  `cauchyPrefactor_of_firstCauchy` produces it from `firstCauchy_sign_consumption` with
  `prefactor = ∑_q μ(q)²` — the unsigned weight.
* `highCond_source_bound_of_logVar : srcVal² ≤ prefactor · (naturalScale / Lsave)`.
* `highCond_source_abs_bound : |srcVal| ≤ E`, under the **explicit** budget
  `prefactor · (naturalScale / Lsave) ≤ E²`.  There is no hidden "sufficiently large".
* `factorialEndpoint_of_highCondLogVar ⇒ Erdos287.V16Status.FactorialOmega7SignedEndpoint`.
* `balancedSeven_of_highCondLogVar ⇒ Erdos287.V16Status.BalancedSevenPacketInput`, via the
  V16 implication reused unchanged.

Every antecedent of the chain is uninhabited, so **the compiler inhabits nothing**.

---

## P. NON-VACUITY / NON-CIRCULARITY  (Phase I §19)

Proved constructively:

* `Erdos287.HighCond3221.highCondLogVar_not_automatic` (the analytic input is refutable);
* `Erdos287.V19Compiler.cauchyPrefactor_not_automatic` (even the algebraic certificate
  constrains its data);
* `Erdos287.V19Compiler.balancedSeven_not_automatic` (the Balanced7 conclusion is
  refutable);
* `Erdos287.V19Compiler.comparison_stays_independent` (reuse of the V18 refutation);
* `Erdos287.HighCond3221.firstCauchy_loses_sign_information` (the Cauchy step really loses
  the `μ` sign).

No compiler proves its own analytic antecedent.

---

## Q. BUILD / AXIOM AUDIT

* `lake build` — **success, 8140 jobs, 0 errors, 0 warnings** in the new modules.
* Scan of all five new Lean files for `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
  `native_decide`, `@[implemented_by]`: **no occurrence** (the only textual matches are the
  words "axiom" and "sorry-free" inside doc comments).
* `#print axioms` is run on all 45 principal new theorems in
  `RequestProject/Status/Erdos287V19Status.lean`.  Every one reports only
  `[propext, Classical.choice, Quot.sound]` or a subset; two ledger theorems report
  *no axioms at all*.  No `sorryAx`, no `Lean.ofReduceBool`.
* No analytic or source interface is inhabited by `Classical.choice` or by any other
  constructor: `InverseSampledHighCondLogVar3221Input`, `DivisorGrowthInput`,
  `MuLogComparisonLowCondMatch`, `FactorialOmega7SignedEndpoint`,
  `BalancedSeven3221NormalForm` occur only as declarations and as hypotheses.

---

## R. FINAL STATUS TABLE

```
FACTORIAL EULER:                     PROVED_ALGEBRAIC / LEAN_PROVED
EXPECTED-TERM LINEARITY:             PROVED_ALGEBRAIC / LEAN_PROVED
3221 GROUPING:                       PROVED_FINITE
PRE-POISSON AFFINE DIVISOR IDENTITY: LEAN_PROVED
FIRST CAUCHY SIGN CONSUMPTION:       LEAN_PROVED / PROVED_ALGEBRAIC
RR/RK/KK REASSEMBLY:                 LEAN_PROVED / PROVED_ALGEBRAIC
PRE-POISSON DIVISOR DENSITY:         LEAN_PROVED FINITE
                                     + arithmetic divisor-growth input (uninhabited)
NATURAL-SCALE 39/35 LEDGER:          PROVED_ALGEBRAIC / CAPACITY_ONLY
V18 DI/SMALL-Z ROUTE:                SUPERSEDED AS CONTROLLING FRONTIER
KLOOSTERMAN-FRACTION BLACKBOX:       RETIRED / EXTERNAL CAPACITY AUDITED
INVERSE-SAMPLED HIGHCOND LOGVAR:     OPEN_ANALYTIC
CHARACTER GRAM EXPANSION:            PROVED_FINITE
COMPARISON:                          SOURCE_OPEN
BALANCED7:                           OPEN
FCL:                                 OPEN
WINDOWPAIRSUPPLY:                    OPEN
ERDOS287:                            OPEN
```

---

## S. FIRST SOURCE OPEN

`AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` — the physical low/principal/exceptional
comparison.  The comparison object is still not formalised in this repository, so the
interface stays uninhabited.

---

## T. FIRST ANALYTIC OPEN

`3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45`.

---

## U. NEXT UNIQUE ACTION

Attack the character-Gram form of the energy that is now kernel-banked: bound

```
V_hi = φ(q)^{-2} ∑_q μ²(q) ∑_{χ,ψ high} ĉ(χ) conj(ĉ(ψ)) G_M(χ, ψ)
```

by controlling the `m`-Gram factor `G_M(χ, ψ)` at the inverse sampling points
`−s(2m)⁻¹`, using the five-box factorisation of `ĉ(χ)` to keep the coefficient structure
explicit.  That is the single missing analytic input; everything surrounding it is now
kernel-checked, source-explicit and non-circular.

---

```
GATE / BALANCED7: OPEN
FCL: OPEN
WINDOWPAIRSUPPLY: OPEN
ERDOS287: OPEN
```

```
FIRST ANALYTIC OPEN:
    3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45.
```
