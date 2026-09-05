# ERDŐS 287 — V12 GOLD REPROOF / LEANIFY RUN — REPORT

**Terminal status: `ERDOS287 OPEN`.**  Nothing in this run proves Erdős #287, and no
theorem added here claims to.

This run is append-only.  No historical file was rewritten and no historical theorem
statement was changed; the only edit to an existing file is the addition of `import`
lines to `RequestProject/Main.lean`.

---

## 0. Firewall note on the V12 dossier

`ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V12.tex/pdf` is **not present in this
repository** (there is no `.tex` or `.pdf` file anywhere in the project; a full-text
search finds no `H8`, `H9`, Ford-(7.23), `SOURCE-ADAPTER45`, `QK56`, `ν₀`, or
`0.16623` occurrence in any pre-existing file).  Consequently:

* every *literal source-transcription* obligation is reported **SOURCE BLOCKED**;
* nothing was reconstructed from a schematic parent formula;
* candidate statements quoted in the request were formalized only as **definitions and
  interfaces**, never asserted.

The Lean bank controls throughout.

---

## A. Exact archaeology of the log-cofactor interface

(unchanged from the previous run; re-verified against the current sources)

```
OBJECT:            gap-≤2 counterexample structure
LEAN NAME:         Erdos287.Gap2CE
FILE:              RequestProject/Erdos287/Counterexample.lean
LITERAL STATEMENT: structure Gap2CE with a Finset ℕ of denominators, reciprocal sum 1,
                   all gaps ≤ 2, N := A.min', M := A.max'
USED BY:           the whole blocker chain, FiniteRemainder, GoodPrime, PlacedLCBeta
STATUS:            banked, kernel-checked

OBJECT:            N, M
LEAN NAME:         Erdos287.Gap2CE.N, Erdos287.Gap2CE.M
FILE:              RequestProject/Erdos287/Counterexample.lean
LITERAL STATEMENT: N = A.min' _, M = A.max' _
USED BY:           all placement lemmas
STATUS:            banked

OBJECT:            N ≤ ⌊M/2⌋
LEAN NAME:         Erdos287.Gap2CE.halfRange_min_le
FILE:              RequestProject/Erdos287/V2SophieFinite.lean:178
LITERAL STATEMENT: theorem halfRange_min_le (hM : 2 ≤ ce.M) : ce.N ≤ ce.M / 2
USED BY:           Gap2CE.N_le_of_M_le_two_mul, blocker_window
STATUS:            banked, kernel-checked (hypothesis 2 ≤ M is necessary: A = {1})

OBJECT:            WindowPairSupply
LEAN NAME:         Erdos287.WindowPairSupply
FILE:              RequestProject/Erdos287/ClosureInputs.lean:43
LITERAL STATEMENT: ∃ x pu au pv av, pu.Prime ∧ pv.Prime ∧ 1 ≤ au ∧ 1 ≤ av ∧
                   pu^au ∣ x ∧ pv^av ∣ (x+1) ∧ M / pu^au ≤ 9 ∧ CVal (M / pu^au) < pu ∧
                   M / pv^av ≤ 9 ∧ CVal (M / pv^av) < pv ∧ M ≤ 2*x ∧ x+1 ≤ M
USED BY:           Erdos287ClosureInputs, no_Erdos287Counterexample_of_closure
STATUS:            banked; DOES carry the lower placement M ≤ 2x

OBJECT:            LCBeta (abstract log-cofactor supply)
LEAN NAME:         Challenges.Delta6.LCBeta
FILE:              RequestProject/Challenges/Delta6Interfaces.lean:113
LITERAL STATEMENT: ∃ x q₀ q₁, q₀.Prime ∧ q₁.Prime ∧ M ≤ 2*J*q₀ ∧ M ≤ 2*J*q₁ ∧
                   M < q₀^2 ∧ M < q₁^2 ∧ q₀ ∣ x ∧ q₁ ∣ (x+1) ∧ x+1 ≤ M
USED BY:           Delta6 ledger/documentation only
STATUS:            banked, OPEN interface; lacks M ≤ 2x AND lacks C(2J) < qᵢ

OBJECT:            finite log-cofactor blocker
LEAN NAME:         TrustedBank.Erdos287Good.Gap2CE.logCofactor_finite_blocker
FILE:              RequestProject/TrustedBank/Erdos287/GoodPrime.lean:139
LITERAL STATEMENT: (hxN : ce.N ≤ x) (hxM : x+1 ≤ ce.M) (hq0 hq1 : prime)
                   (hlow0 hlow1 : ce.M ≤ 2*J*qᵢ) (hsq0 hsq1 : ce.M < qᵢ^2)
                   (hC0 hC1 : C (2*J) < qᵢ) (hd0 : q₀ ∣ x) (hd1 : q₁ ∣ x+1) : False
USED BY:           Gap2CE.no_of_placedLCBeta
STATUS:            banked, kernel-checked

OBJECT:            C(j)
LEAN NAME:         Erdos287.C
FILE:              RequestProject/Erdos287/Defs.lean:60
LITERAL STATEMENT: C j = max over nonempty sublists of [1..j] of the reduced numerator
USED BY:           the entire blocker chain
STATUS:            banked; C(1..8) = (1,3,11,25,137,137,1019,2143) certified by decide

OBJECT:            C(j) ≤ j·j!
LEAN NAME:         Erdos287.C_le_U   (with Erdos287.U j = j * j!)
FILE:              RequestProject/Erdos287/Uniform.lean:66  (U at :46)
LITERAL STATEMENT: theorem C_le_U (j : ℕ) : C j ≤ (U j : ℤ)
USED BY:           logCofactor_asymptotic287
STATUS:            banked, kernel-checked

OBJECT:            upper-half placement predicate
LEAN NAME:         Erdos287.PlacedLCBeta / Erdos287.UpperHalfLCBeta
FILE:              RequestProject/Erdos287/PlacedLCBeta.lean:48 / :55
LITERAL STATEMENT: LCBeta's conditions + C(2J) < q₀,q₁ + M ≤ 2x + x+1 ≤ M
USED BY:           Gap2CE.no_of_placedLCBeta, placedLCBeta_of_adjacent_large_prime_factors
STATUS:            added in the previous run, kernel-checked

OBJECT:            theorem repairing the missing lower placement
LEAN NAME:         Erdos287.Gap2CE.N_le_of_M_le_two_mul
FILE:              RequestProject/Erdos287/PlacedLCBeta.lean:82
LITERAL STATEMENT: (hM : 2 ≤ ce.M) (h : ce.M ≤ 2*x) : ce.N ≤ x
USED BY:           Gap2CE.no_of_placedLCBeta
STATUS:            proved
```

### A1. Hostile check of the historical `LCBeta`

**Verdict: `LCBETA_PLACEMENT_MISSING`** (unchanged, and now certified rather than
asserted).

`Challenges.Delta6.LCBeta` records `x + 1 ≤ M` but not `M ≤ 2x`, and it is genuinely
satisfiable below the half-way point: `Erdos287.lcBeta_witness_below_half` exhibits
`LCBeta 30 3` with `x = 13`, `2x = 26 < 30 = M`.  Hence no derivation of `N ≤ x` from
`LCBeta` is possible.  (A second gap is recorded: `LCBeta` also omits the numerator
threshold `C(2J) < qᵢ` demanded by the banked blocker.)

The repair is append-only and compiles: `PlacedLCBeta`, `placedLCBeta_imp_LCBeta`,
`Gap2CE.N_le_of_M_le_two_mul`, `Gap2CE.no_of_placedLCBeta`.

---

## B. `LOG-COFACTOR-ASYMPTOTIC287`

**`LOG_COFACTOR_ASYMPTOTIC287_KERNEL_PASS`** (proved in the previous run, re-verified
here).

`Erdos287.logCofactor_asymptotic287` (file
`RequestProject/Erdos287/LogCofactorAsymptotic.lean`) with
`Jlog eta M = ⌊η·log M / log log M⌋` and the *explicit* threshold
`M₀ = ⌈exp T⌉ + 257`, `T = max(17/(1−2η)², 4/η², 6)`.  Ingredients used: the banked
`C_le_U` (i.e. `C(j) ≤ j·j!`), `Nat.factorial_le_pow`, `log_le_two_sqrt`,
`log_sq_lt_self`.  No external asymptotic input; `#print axioms` shows only
`[propext, Classical.choice, Quot.sound]`.

---

## C. `FIXED-CERTIFICATE-TRANSFERENCE287`

**`FIXED_CERTIFICATE_TRANSFERENCE287_KERNEL_PASS`.**

Three-region version (previous run):
`Erdos287.Transference.sum_a_P_identity`, `sum_a_P_lower` (`≥ (1+C)B − 3E`),
`sum_a_P_pos`, `transference_nonvacuous`.

Four-region / three-error version required by V12 (this run, new file
`RequestProject/Erdos287/FixedCertificateThreeError.lean`):

* `Erdos287.Transference4.sum_a_P_identity4`;
* `Erdos287.Transference4.sum_a_P_lower4` — `∑_{p∈P} a p ≥ (1+C)B − ET − EL − E2 − EM`
  with **`N2` kept apart from the sign region `N1`** (no sign hypothesis on `N2`);
* `Erdos287.Transference4.sum_a_P_pos4` — positivity when `ET+EL+E2+EM ≤ δB`, `0 < B`,
  `δ < 1 + C`, with explicit bound `(1+C−δ)B`;
* `Erdos287.Transference4.sum_a_P_pos4_fraction` — the constant-saving variant: a fixed
  fraction suffices, no logarithmic saving is logically required;
* `Erdos287.Transference4.transference4_nonvacuous` — the hypotheses are simultaneously
  satisfiable, so none of the above is vacuous.

---

## D. Quadratic-Kummer backend

* **D1 finite compiler — KERNEL PASS.** `Erdos287.Kummer.kummer_bilinear_of_correlation_bounds`
  (`KummerFiniteCompiler.lean`), bound `(∑α²)(∑β²)(s·Mb + R·|In|)`.  Repair: the symmetry
  hypothesis on exceptional sets is restricted to `In`; the unrestricted form is false for
  the intended `±` sets.
* **D2 root-stabilizer — KERNEL PASS.** `Erdos287.Kummer.quadratic_scaling_square_criterion`
  over an arbitrary field, by a coefficient criterion — no splitting field, no assumption
  that the roots lie in `ZMod p`, `n₁,n₂ ≠ 0` explicit, and the repeated-root case
  separated (`repeated_root_scaling_square` shows the criterion genuinely fails there).
  Stabilizer cardinality `≤ 2`: `scalingSquareStabilizer_ncard_le_two`.
* **D3 Weil input — `WEIL_INPUT_EXTERNAL_INTERFACE_REQUIRED`.**  A search of Mathlib and
  of the project finds no Weil / interval-completion bound of the required strength.  The
  local interface `Erdos287.Kummer.QuadraticKummerCorrelationBound` is defined and
  **never inhabited**; `kummer_bilinear_of_interface` derives the bilinear bound from it.

---

## E. Seven-prime `5|2` exponent ledger

**KERNEL PASS.**  `RequestProject/Erdos287/KummerExponentLedger.lean`:
`exponent_ledger`, `exponent_ledger_max`, the two endpoints (`θ = 5/2` → `−5/4`,
`θ = 8` → `−1`, tight), `exponent_ledger_fails_above_eight`, the real-analytic
`kummer_savings_bound` (`≤ √3 · Y^{−1/2}`, an explicit constant in place of `Y^{o(1)}`),
and the fixed-power margin `margin_Y_eq_X` (`Y^{−1/2} = X^{−1/18}` for `X = Y⁹`) plus
`margin_exponent` (`9·(−1/18) = −1/2`).

---

## F. Degeneracy routers

New file `RequestProject/Erdos287/KummerDegeneracyRouters.lean`.

```
ROUTER:                  repeated-root / discriminant-zero sector
EXACT CONDITION:         Erdos287.Kummer.RepeatedRootStratum a b c :  b² − 4ac = 0
DIMENSION/VARIABLE LOSS: the scaled product becomes a square for EVERY pair of scalings
TARGET THEOREM:          generic_not_repeatedRoot, repeatedRoot_router_nonvacuous
LEAN STATUS:             PASS (finite, kernel-checked)
ANALYTIC INPUT NEEDED:   none for the routing; the sector must be handled separately

ROUTER:                  nonunit scaling (n ≡ 0 mod p)
EXACT CONDITION:         Erdos287.Kummer.NonUnitStratum n₁ n₂ :  n₁ = 0 ∨ n₂ = 0
DIMENSION/VARIABLE LOSS: one bilinear variable collapses
TARGET THEOREM:          generic_not_nonUnit
LEAN STATUS:             PASS (finite)
ANALYTIC INPUT NEEDED:   none

ROUTER:                  collision / root-stabilizer stratum
EXACT CONDITION:         Erdos287.Kummer.CollisionStratum n₁ n₂ :  n₂ = n₁ ∨ n₂ = −n₁
DIMENSION/VARIABLE LOSS: diagonal, at most 2 partners per n₁ (pmExceptional_card_le_two)
TARGET THEOREM:          generic_not_collision, generic_not_pmExceptional
LEAN STATUS:             PASS (finite)
ANALYTIC INPUT NEEDED:   the trivial diagonal bound Mb only

ROUTER:                  degenerate leading coefficient
EXACT CONDITION:         Erdos287.Kummer.DegenerateLeadStratum a :  a = 0
DIMENSION/VARIABLE LOSS: the "quadratic" drops to degree ≤ 1
TARGET THEOREM:          generic_not_degenerateLead
LEAN STATUS:             PASS (finite)
ANALYTIC INPUT NEEDED:   none

ROUTER:                  isolated pure multiplicative-character mode
EXACT CONDITION:         (absent from this repository)
DIMENSION/VARIABLE LOSS: unknown here
TARGET THEOREM:          none
LEAN STATUS:             SOURCE BLOCKED — no H8/H9 audit object exists in the project
ANALYTIC INPUT NEEDED:   the literal source definition first

ROUTER:                  principal / zero mode
EXACT CONDITION:         (absent from this repository)
LEAN STATUS:             SOURCE BLOCKED
ANALYTIC INPUT NEEDED:   the literal source definition first

ROUTER:                  repeated-prime / conductor-loss strata
EXACT CONDITION:         partially related banked objects exist
                         (TrustedBank.FixedAffine.SingularFactors.nu_eq_one for the
                          collision of the two affine roots mod l,
                          TrustedBank.FixedAffine.LocalRoots.no_two_nearby_roots)
LEAN STATUS:             PARTIAL — no conductor bookkeeping exists in the project
ANALYTIC INPUT NEEDED:   the literal conductor-loss definition
```

The disjointness statement actually proved is
`Erdos287.Kummer.generic_disjoint_strata` together with its payoff
`Erdos287.Kummer.generic_not_square`: a generic packet's scaled product is not a square,
so it is outside the exceptional set of the correlation interface.

**Verdict: `KUMMER DEGENERACY ROUTERS — PARTIAL`** (four routers PASS, two SOURCE
BLOCKED, one PARTIAL).

---

## G. Explicit fixed certificate + smooth-parity census (the new controlling task)

### G1. Pinning the literal Ford certificate — **SOURCE BLOCKED**

New file `RequestProject/Erdos287/FixedCertificateFordData.lean` transcribes the data
exactly as given in the request and proves its finite arithmetic:

* `Erdos287.FordData.nu0 = 16623/100000` (exact rational), `nu0_bounds`;
* `twoVarLow = (1 − ν₀)/2 = 83377/200000`, `twoVarWindow_nonempty` (`< 1/2`),
  `twoVarWindow_width` (`= ν₀/2`);
* `fordCandidate c₂` — `g₀(∅) = 1`, one-variable branch `−1_{x ≤ 1/2}`, two-variable
  branch supported on `((1−ν₀)/2, 1/2)` with coefficient carried as a **parameter** `c₂`
  (the request pins that branch's *support*, not its sign — nothing invented), and
  three-variable branch `−1_{x₁+x₂+x₃ ≤ 1/2}`; with branch-value and sample-point lemmas;
* `shrink delta g = (1−δ)·g` with `shrink_le`; no effective decimal `ε`/`δ` is invented,
  since the source proves admissibility only through `C* = C₀ + O(ε)`;
* `CertificatePinned` — the predicate "this data is the published certificate", **never
  inhabited**; `PositiveComparisonMargin` — the source positivity `1 + C* > 0`, **never
  proved**.

Because the source dossier is absent from the repository, `FIXED_CERTIFICATE287_PIN` is
**SOURCE BLOCKED**, not PASS.

### G2. Finite arithmetic weight interface with three errors — **KERNEL PASS**

See Part C above (`Transference4`).  `N2` is never merged into the sign region, and the
constant-saving variant `sum_a_P_pos4_fraction` is proved.

The abstract `H*(n) = ∑_{d ∣ n} G*(d;n)` with prime normalization `H*(p) = 1` is realized
concretely in Part G3: `SmoothParity.smoothParity_prime_normalization` derives `H*(p) = 1`
from the packet, i.e. the `P`-normalization required by the transference theorem is a
*consequence* of the packet, not an extra assumption.

### G3. The smooth Möbius-parity packet — **SOURCE BLOCKED (first analytic open)**

New file `RequestProject/Erdos287/FixedCertificateSmoothParity.lean`:

* `Erdos287.SmoothParity.truncMobius n T = ∑_{d ∣ n, d ≤ T} μ(d)` with
  `truncMobius_one`, `truncMobius_prime` (`= 1` for a prime above the cut),
  `sum_moebius_divisors_eq_zero`, `truncMobius_eq_zero_of_le` (inactive cut ⇒ 0);
* the interface `Erdos287.SmoothParity.FixedCertificateSmoothParityPacket`, whose fields
  are exactly (i) `cell_identity`: the `k = 0`, `J = ∅` cell identity
  `H_{g*}(n) = ∑_{d ∣ n, d ≤ cut n} μ(d)` on the smooth sector, and (ii)
  `analytic_bound`: the estimate `ERDOS287_FIXED_CERTIFICATE_SMOOTH_PARITY45`.
  **No inhabitant is constructed.**
* consequences proved from the interface: `smoothParity_prime_normalization`,
  `smoothParity_inactive_cut`, and `smoothParity_missing_source`, which states in Lean
  exactly what the missing source theorem must deliver.

**Hostile finding.**  The literal Ford factorisation of `G(m;n)` is *not encoded anywhere
in this repository* — the same gap is already documented inside
`TrustedBank/R9/Certificate.lean` ("the exact Ford-certificate definitions … are not
present in this repository").  Therefore the cell identity was **not** proved and was
**not** asserted; it is carried as an interface field.  Missing source theorem, stated
exactly:

> *For the fixed certificate `g*`, the cell `k = 0`, `J = ∅` of the Ford factorisation of
> `G_{g*}(m;n)` contributes, on the smooth-prime-factor sector, exactly the truncated
> Möbius weight `H_{g*}(n) = ∑_{d ∣ n,\; d ≤ n^{1/2−ε}} μ(d)`.*

### G4. Kernel-checked H8/H9-only counterguard — **KERNEL PASS, census FAILS**

New file `RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean`:

* `alternating_partial_binomial` — `∑_{j=0}^{r} (−1)^j C(k,j) = (−1)^r C(k−1,r)` for
  `k ≥ 1` (the requested identity; proved for all `r`, in particular for `r < k`);
* `balancedCellWeight k r` — the subset-lattice model of the truncated Möbius divisor
  weight on a balanced `k`-factor cell, with `balancedCellWeight_eq_sum` and the closed
  form `balancedCellWeight_eq`;
* `balancedCellCut` — the exact finite content of the truncation cut: for
  `r ≤ γk < r+1`, a divisor with `j` prime factors survives iff `j ≤ r`;
* `balancedCellWeight_ne_zero` — nonzero for every `r < k`;
* explicit instances at the balanced cut `r = ⌊(k−1)/2⌋` (valid for rational `γ` just
  below `1/2`):

  | k | r | weight |
  | --- | --- | --- |
  | 7 | 3 | −20 |
  | 8 | 3 | −35 |
  | 9 | 4 | 70 |
  | 10 | 4 | 126 |
  | 11 | 5 | −252 |
  | 12 | 5 | −462 |

  with `counterguard_k9_matches_bank` checking `70 = TrustedBank.R9.lowSum`;
* `finite_H8H9_only_census_fails` — orders `k = 7, 10, 11, 12` all carry nonzero weight;
  `balancedCellWeight_halfCut_ne_zero` — *no* order is annihilated.

Hence **`FINITE_H8_H9_ONLY_CENSUS = FAIL`**, exactly as V12 predicts.  No theorem named
`FullNine` (or any other) is used to imply exhaustiveness anywhere in the project.

---

## H. Quadratic-Kummer backend as a child provider only

The V11 Kummer results are retained with the V12 interpretation: `SEVENPRIME_KUMMER` is a
**CONDITIONAL ANALYTIC CHILD PASS** (conditional on the never-inhabited
`QuadraticKummerCorrelationBound`), and it does **not** imply fixed leakage closure — no
theorem in the project connects it to the parent estimate.  `H8H9-SOURCE-TO-KUMMER45`
remains an open child/source interface: **SOURCE BLOCKED**, the literal packet formula
being absent.

---

## I. Fixed-certificate leakage parent

`RequestProject/Erdos287/FixedCertificateSmoothParity.lean`:

* `parent_leakage_of_children` — leakage over `U = ⋃ᵢ Uᵢ` is bounded by `∑ᵢ Eᵢ`;
* `parent_leakage_two_children` — the smooth-parity child plus everything else;
* `parent_prime_mass_pos` — all child bounds + total correlation + `N2` bound +
  comparison margin ⇒ `0 < ∑_{p ∈ P} a p`.

Every analytic input is an explicit antecedent; none is hidden inside a definition.  The
parent analytic estimate `287-FIXED-CERTIFICATE-LEAKAGE45` stays **OPEN**: its
smooth-parity child is unproved, and the enumeration of the remaining children is itself
source-blocked.

---

## J. Route firewall

`RequestProject/Status/Erdos287GoldV12Status.lean` records the single logical fact
`fixedCertificateRoute_sufficient_V12`: the fixed-certificate wrapper suffices *when its
own hypotheses are present*.  The alternative routes (`FullFMTypeII_1/6`, the generated
Ford (7.23) route, `SOURCE-ADAPTER45`, the global replacement certificate `C_FM`) are
preserved untouched and remain valid sufficient alternatives.  The stronger claim that
the fixed-certificate route is *analytically shorter* is **not made**; the Part G4
counterguard is precisely the obstruction to it.

---

## K. File plan, build and axiom audit

### Files added in this run (append-only)

| File | Role |
| --- | --- |
| `RequestProject/Erdos287/FixedCertificateFordData.lean` | G1 certificate data, pin predicate |
| `RequestProject/Erdos287/FixedCertificateThreeError.lean` | G2 three-error transference |
| `RequestProject/Erdos287/FixedCertificateSmoothParity.lean` | G3 packet + I parent compiler |
| `RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean` | G4 counterguard |
| `RequestProject/Erdos287/KummerDegeneracyRouters.lean` | F routers |
| `RequestProject/Status/Erdos287GoldV12Status.lean` | J firewall + axiom prints |
| `ERDOS287_GOLD_V12_REPORT.md` | this report |

Files modified: `RequestProject/Main.lean` (import lines only).

### Build

`lake build` completes successfully (8101 jobs), all targets, no `sorry` warnings.

### Axioms

Every new theorem prints
`depends on axioms: [propext, Classical.choice, Quot.sound]` — the ordinary Mathlib
axioms.  The prints are executed by `RequestProject/Status/Erdos287GoldV12Status.lean`
and appear in the build log.

Representative table (role column abbreviated; all `COMPILES: yes`):

| THEOREM | FILE | EXTERNAL INTERFACE | ROLE |
| --- | --- | --- | --- |
| `Erdos287.FordData.twoVarWindow_nonempty` | FixedCertificateFordData | no | certificate data arithmetic |
| `Erdos287.FordData.shrink_le` | FixedCertificateFordData | no | shrink bookkeeping |
| `Erdos287.Transference4.sum_a_P_lower4` | FixedCertificateThreeError | no | three-error transference |
| `Erdos287.Transference4.sum_a_P_pos4_fraction` | FixedCertificateThreeError | no | constant-saving positivity |
| `Erdos287.SmoothParity.truncMobius_prime` | FixedCertificateSmoothParity | no | prime normalization |
| `Erdos287.SmoothParity.smoothParity_prime_normalization` | FixedCertificateSmoothParity | yes (packet) | packet consequence |
| `Erdos287.SmoothParity.parent_prime_mass_pos` | FixedCertificateSmoothParity | yes (child bounds) | parent compiler |
| `Erdos287.Counterguard.alternating_partial_binomial` | FixedCertificateOrderCounterguard | no | binomial identity |
| `Erdos287.Counterguard.finite_H8H9_only_census_fails` | FixedCertificateOrderCounterguard | no | census FAIL |
| `Erdos287.Kummer.generic_disjoint_strata` | KummerDegeneracyRouters | no | degeneracy routing |
| `Erdos287.Kummer.generic_not_square` | KummerDegeneracyRouters | no | routing payoff |
| `Status.Erdos287GoldV12.fixedCertificateRoute_sufficient_V12` | Erdos287GoldV12Status | yes (hypotheses) | route firewall |

### Placeholder scan

`rg` over `RequestProject` for `sorry`, `admit`, `axiom`, `opaque`, `native_decide`,
`unsafe`, `implemented_by` finds **no Lean syntax occurrences** — every hit is inside
documentation prose (e.g. "never `native_decide`", "no `sorry`").  No user axiom exists in
the project.

---

## M. FINAL LEDGER

```
LCBETA PLACEMENT:
REPAIRED

LOG-COFACTOR-ASYMPTOTIC287:
KERNEL PASS

FIXED-CERTIFICATE287-PIN:
SOURCE BLOCKED

FIXED-CERTIFICATE-TRANSFERENCE287:
KERNEL PASS

FIXED-CERTIFICATE-SMOOTH-PARITY PACKET:
SOURCE BLOCKED

FINITE-H8/H9-ONLY-CENSUS:
FAIL (counterguard compiles)

HIGH-ORDER COUNTERGUARD:
KERNEL PASS

QUADRATIC-KUMMER FINITE COMPILER:
KERNEL PASS

ROOT-STABILIZER ALGEBRA:
KERNEL PASS

WEIL / INTERVAL COMPLETION:
EXTERNAL INTERFACE

SEVEN-PRIME EXPONENT LEDGER:
KERNEL PASS

KUMMER DEGENERACY ROUTERS:
PARTIAL

SEVENPRIME-KUMMER:
CONDITIONAL CHILD PASS

H8H9-SOURCE-TO-KUMMER45:
SOURCE BLOCKED

287-FIXED-CERTIFICATE-SMOOTH-PARITY45 ANALYTIC ESTIMATE:
OPEN

FIXED-CERTIFICATE LEAKAGE COMPILER:
KERNEL PASS

287-FIXED-CERTIFICATE-LEAKAGE45 ANALYTIC ESTIMATE:
OPEN

GENERATED-(7.23) FIXED-gStar SPECIALIZATION:
MAY STILL BE NEEDED

ERDOS287:
OPEN
```

```
EXACT FIRST OPEN AFTER THIS RUN:
287-FIXED-CERTIFICATE-SMOOTH-PARITY45
(the two fields of Erdos287.SmoothParity.FixedCertificateSmoothParityPacket:
 first the Gate-1B source obligation `cell_identity`, then the analytic bound)

NEXT MATHEMATICAL ACTION:
Obtain the literal Ford factorisation of G_{g*}(m;n) and prove its k = 0, J = ∅ cell
equals the truncated Möbius weight ∑_{d ∣ n, d ≤ n^{1/2−ε}} μ(d) on the smooth sector,
i.e. inhabit the `cell_identity` field of FixedCertificateSmoothParityPacket.
```
