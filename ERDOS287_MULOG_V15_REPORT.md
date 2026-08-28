# Erdős #287 — V15: the `Λ = μ ∗ log` source-minimal chain and the balanced-seven polarization algebra

**Verdict: `ERDOS287_V15_MULOG_POLARIZATION_SAFE_BANK`.**
**`ERDOS287: OPEN`.**

First uninhabited analytic interfaces:

* `AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45` — `OPEN_ANALYTIC`
* `AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45` — `SOURCE_OPEN`

Nothing in V15 proves Erdős #287, any analytic estimate, Bombieri–Vinogradov at any range,
a DGS or Pascadi input, an exponent of distribution, balanced-seven analytic smallness, an
FCL statement, a Gate 1A/1B statement, or a `WindowPairSupply` statement.

## 0. Workspace / regression guard — PASS

All named V14 objects were located before any edit:

| object | file |
| --- | --- |
| `vaughan_identity_exact`, `vaughan_affine_pointwise` | `RequestProject/Erdos287/AffineVaughanIdentity.lean` |
| `AffineVaughanPrimeCell`, `lambdaU_eq_neg_truncMobius` | `RequestProject/Erdos287/AffineVaughanPrimeOuter.lean` |
| `AffinePrimeModulusTwoOuterPacket`, `affine_det_one_line_param`, `affine_line_forward`, `affine_line_complete`, `affine_line_param_unique` | `RequestProject/Erdos287/AffineTwoOuterSource.lean` |
| `singletonTypeII_of_vaughan_twoOuter`, `smoothParity_of_vaughan_twoOuter`, `parentLeakage_of_vaughan_twoOuter` | `RequestProject/Erdos287/AffineTwoOuterCompiler.lean` |

`WORKSPACE_MISMATCH` does not apply. No V14 theorem was deleted, weakened, renamed, or
rewritten; work is append-only apart from seven new import lines in
`RequestProject/Main.lean`. No user axiom was introduced.

## 1. Files added

| file | content |
| --- | --- |
| `RequestProject/Erdos287/AffineMuLogIdentity.lean` | Parts 1–2: `Λ = μ ∗ log`, coefficientwise forms, affine specialisation |
| `RequestProject/Erdos287/AffineMuLogHardSource.lean` | Part 3: three-way `q`/`r` partition and exact recombination |
| `RequestProject/Erdos287/AffineMuLogLine.lean` | Part 4: determinant-one line `q r − 2 m n = ±1` |
| `RequestProject/Erdos287/AffineMuLogExponentLedger.lean` | Part 5: rational exponent ledger only |
| `RequestProject/Erdos287/BalancedSevenFinite.lean` | Parts 6, 7, 9: binomial certificate, repeated-prime router, squarefree encoding interface |
| `RequestProject/Erdos287/BalancedSevenPolarization.lean` | Part 8: labelled polarization coefficient identity |
| `RequestProject/Status/Erdos287V15Status.lean` | Parts 10–11, 13: uninhabited interfaces, status hierarchy, hostile checks, `#print axioms` |
| `ERDOS287_MULOG_V15_REPORT.md` | this report |

Files edited: `RequestProject/Main.lean` (import lines only).

## 2. Theorems proved (all sorry-free, kernel-checked)

### Part 1 — `AFFINE287-MULOG-IDENTITY45 : PROVED_ALGEBRAIC`
* `muLog_identity_abstract` — `μ · lg = Λ` in any commutative ring from `μ ζ = 1`,
  `lg = Λ ζ`.
* `vonMangoldt_eq_mobius_mul_log` — the instance for Mathlib's genuine
  `vonMangoldt`/`moebius`/`log`/`zeta`.
* `vonMangoldt_eq_mobius_mul_log_agrees` — `rfl`-check that this *is* Mathlib's
  `moebius_mul_log_eq_vonMangoldt`.
* `vonMangoldt_eq_sum_antidiagonal`, `vonMangoldt_eq_sum_divisors` — exact coefficientwise
  forms.

### Part 2 — `AFFINE287-MULOG-SOURCE45 : PROVED_ALGEBRAIC`
* `muLog_affine_pointwise`, `muLogAffineSource`, `muLogAffineSource_eq`,
  `muLogAffineSource_arg` (the `Nat`-subtraction firewall, reused from V14 unchanged).

### Part 3 — `AFFINE287-MULOG-HARD-PARTITION45 : PROVED_FINITE/ALGEBRAIC`
* `pairSmallQ`, `pairSmallR`, `pairHard`; `pairClass_exhaustive`, `pairClass_union`;
  `pairClass_disjoint_QR`, `pairClass_disjoint_QH`, `pairClass_disjoint_RH`;
  `pair_sum_split` (abstract weight, any `AddCommMonoid`);
  `mulog_sum_eq_smallQ_add_smallR_add_hard`,
  `mulog_affine_sum_eq_smallQ_add_smallR_add_hard`, `pairHard_affine_det_one`.
* The hard source `muLogHard N U = ∑_{q r = N, q>U, r>U} μ(q) log r` is **not** claimed
  small.

### Part 4 — determinant-one line, `PROVED_ALGEBRAIC`
* `affine_mulog_r_ne_zero`, `affine_mulog_q_ne_zero` (proved, not assumed);
  `affine_mulog_coprime` (`gcd(r,2m)=1`), `affine_mulog_coprime_symm` (`gcd(q,2n)=1`);
  `affine_mulog_line_forward`, `affine_mulog_line_reverse`, `affine_mulog_line_iff`,
  `affine_mulog_line_parameter_unique`, `affine_mulog_line_iff_sign`.

### Part 5 — `AFFINE287-SHORTLINE-MR-ROUTER45 : EXPONENT_CORE_PROVED / ANALYTIC_SUMMATION_EXTERNAL`
* `delta0Of`, `mulog_delta0_pos`, `mulog_shortLine_exponent_eq`,
  `mulog_shortLine_exponent_lt_one`, `mulog_shortLine_exponent_lt_one_rat`,
  `mulog_delta0_unshrunk_value` (`1/6 − ν₀ = 131/300000`).
* No `O`-estimate is stated as a theorem.

### Part 6 — `BALANCED7_CERTIFICATE_BINOMIAL : PROVED_FINITE`
* `balancedSeven_alternating_partial_binomial` (re-export of the banked general identity),
  `balancedSeven_lowSum_eq_neg20`, `balancedSeven_lowSum_eq_counterguard`.
* `BALANCED7_PHYSICAL_SOURCE` is **not** claimed.

### Part 7 — `BALANCED7-REPEATED-PRIME45 : FINITE/EXPONENT CORE PROVED`
* `repeatedPrime_image_card_le_six`, `repeatedLabel_image_card_lt`,
  `repeatedPrime_exponent_lt_one`.

### Part 8 — `BALANCED7-SQUAREFREE-POLARIZATION45 : PROVED_ALGEBRAIC`
* `balancedMonomial`, `balancedSevenMonomial`, `labelledPolynomial`;
  `prod_monomial`, `degreeVector_apply`, `degreeVector_eq_balanced_iff`;
  `coeff_balanced_eq_perm_sum` (arbitrary commutative semiring),
  `coeff_balancedSeven_eq_perm_sum`, `coeff_balancedSeven_eq_perm_sum_complex`,
  `card_perm_seven` (`7! = 5040`).
* Normalisation kept separate: `coeff_balanced_scaled`, `sevenPow_seven` (`7^7 = 823543`),
  `coeff_balancedSeven_scaled_seventh`.

### Part 9 — squarefree multiplicative encoding, finite interface
* `SquarefreeEncoding` (multiplicative, prime values `a p`, zero at exponent `≥ 2`),
  `SquarefreeEncoding.map_prod_primes`, `map_prod_seven_primes`,
  `SquarefreeEncoding.moebius` (inhabitant, so nothing is vacuous),
  `moebius_seven_distinct_primes`.

### Part 10 — analytic interfaces, uninhabited
* `Erdos287.V15Status.PolarizedOmega7SignedEoD` — `OPEN_ANALYTIC`;
* `Erdos287.V15Status.MuLogComparisonLowCondMatch` — `SOURCE_OPEN`.
No inhabitant of either is constructed anywhere in the repository.

## 3. V14 status hierarchy (Part 11)

```
AFFINE287-VAUGHAN-PRIME-SOURCE45        VALID ALTERNATIVE SOURCE / NONMINIMAL CONTROLLING ROUTE
AFFINE287-PRIME-MODULUS-MU-TWOOUTER45   OPEN ALTERNATIVE CHILD, NOT CONTROLLING
AFFINE287-MULOG-IDENTITY45              PROVED_ALGEBRAIC
AFFINE287-MULOG-SOURCE45                PROVED_ALGEBRAIC
AFFINE287-MULOG-HARD-PARTITION45        PROVED_FINITE/ALGEBRAIC
AFFINE287-LINE-DICHOTOMY45              EXPONENT CORE PROVED; ANALYTIC SHORT-LINE ROUTER EXTERNAL
BALANCED7_CERTIFICATE_BINOMIAL          PROVED_FINITE
BALANCED7-SQUAREFREE-POLARIZATION45     PROVED_ALGEBRAIC
AFFINE287-POLARIZED-OMEGA7-SIGNED-EOD45 OPEN_ANALYTIC
AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45  SOURCE_OPEN
ERDOS287                                OPEN
```

V14's Vaughan route is recorded as valid but nonminimal — never as false.

## 4. Hostile tests (Part 13)

The twenty checks are answered individually in the docstring of
`RequestProject/Status/Erdos287V15Status.lean`; all pass, with no downgrades.

## 5. Build / trust audit (Part 14)

* `lake build` succeeds (8118 jobs, no errors).
* A repository-wide scan of all Lean sources for `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, `native_decide`, `@[implemented_by]` finds **zero occurrences in Lean code**;
  every match is documentation prose.
* `#print axioms` is emitted at build time for all 36 principal new theorems by the V15
  status file; every one reports a subset of `[propext, Classical.choice, Quot.sound]`.
