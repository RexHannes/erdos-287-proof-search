# Erdős 287 — V11 Gold reproof / Leanification run

**Terminal status: `ERDOS287 OPEN`.**  Nothing in this run proves Erdős #287, and no
theorem added here claims to.  The run is append-only: no pre-existing definition,
theorem statement or proof was edited, weakened, renamed or deleted (the only edit to an
existing file is nine new `import` lines in `RequestProject/Main.lean`).

**Source firewall note.**  `ERDOS287_STANDALONE_VERIFICATION_DOSSIER_V11.tex/pdf` is
**not present in this repository** (no `.tex`, `.pdf` or any V11 file exists here).  Every
item of the request that is a *literal source-transcription* obligation is therefore
reported `SOURCE_BLOCKED` and nothing was reconstructed from a schematic parent formula.
The items that are mathematically self-contained (the placement repair, the log-cofactor
asymptotic, the transference kernel, the Kummer finite compiler, the root-stabilizer
algebra, the exponent ledger, the leakage compiler) were reproved from scratch against
the Lean bank, which controls throughout.

---

## A. Exact archaeology of the log-cofactor interface

```
OBJECT:           gap-≤2 counterexample structure
LEAN NAME:        Erdos287.Gap2CE
FILE:             RequestProject/Erdos287/Counterexample.lean:23
LITERAL STATEMENT:structure Gap2CE where
                    A : Finset ℕ
                    hne : A.Nonempty
                    hpos : ∀ a ∈ A, 0 < a
                    hsum : ∑ a ∈ A, (1 : ℚ) / a = 1
                    hgap : ∀ a ∈ A, a ≠ A.max' hne → (a + 1 ∈ A ∨ a + 2 ∈ A)
USED BY:          the whole #287 package
STATUS:           banked, unchanged
```

```
OBJECT:           N, M
LEAN NAME:        Erdos287.Gap2CE.N, Erdos287.Gap2CE.M
FILE:             RequestProject/Erdos287/Counterexample.lean:40, 43
LITERAL STATEMENT:def N : ℕ := ce.A.min' ce.hne     def M : ℕ := ce.A.max' ce.hne
USED BY:          all blockers
STATUS:           banked, unchanged
```

```
OBJECT:           the half-range theorem  N ≤ ⌊M/2⌋
LEAN NAME:        Erdos287.Gap2CE.halfRange_min_le
FILE:             RequestProject/Erdos287/V2SophieFinite.lean:178
LITERAL STATEMENT:theorem halfRange_min_le (hM : 2 ≤ ce.M) : ce.N ≤ ce.M / 2
USED BY:          v2 blockers, FiniteRemainder.blocker_window, and (new)
                  Erdos287.Gap2CE.N_le_of_M_le_two_mul
STATUS:           banked, unchanged.  The hypothesis 2 ≤ M is necessary
                  (A = {1} inhabits Gap2CE with N = 1 > 0 = ⌊M/2⌋).
```

```
OBJECT:           WindowPairSupply
LEAN NAME:        Erdos287.WindowPairSupply
FILE:             RequestProject/Erdos287/ClosureInputs.lean:43
LITERAL STATEMENT:def WindowPairSupply (M : ℕ) : Prop :=
                    ∃ x pu au pv av : ℕ, pu.Prime ∧ pv.Prime ∧ 1 ≤ au ∧ 1 ≤ av ∧
                      pu ^ au ∣ x ∧ pv ^ av ∣ (x + 1) ∧
                      M / pu ^ au ≤ 9 ∧ CVal (M / pu ^ au) < pu ∧
                      M / pv ^ av ≤ 9 ∧ CVal (M / pv ^ av) < pv ∧
                      M ≤ 2 * x ∧ x + 1 ≤ M
USED BY:          Erdos287.Gap2CE.no_of_windowPairSupply, Erdos287ClosureInputs
STATUS:           banked, unchanged.  NOTE: this predicate DOES carry the lower
                  placement `M ≤ 2 * x`.
```

```
OBJECT:           LCBeta (the only current variant; there is no other)
LEAN NAME:        Challenges.Delta6.LCBeta
FILE:             RequestProject/Challenges/Delta6Interfaces.lean:113
LITERAL STATEMENT:def LCBeta (M J : ℕ) : Prop :=
                    ∃ x : ℕ, ∃ q₀ q₁ : ℕ, q₀.Prime ∧ q₁.Prime ∧
                      M ≤ 2 * J * q₀ ∧ M ≤ 2 * J * q₁ ∧ M < q₀ ^ 2 ∧ M < q₁ ^ 2 ∧
                      q₀ ∣ x ∧ q₁ ∣ (x + 1) ∧ x + 1 ≤ M
USED BY:          nothing (it is an open-interface record; no theorem consumes it)
STATUS:           banked, unchanged; repaired append-only by Erdos287.PlacedLCBeta
```

```
OBJECT:           the finite log-cofactor blocker
LEAN NAME:        TrustedBank.Erdos287Good.Gap2CE.logCofactor_finite_blocker
FILE:             RequestProject/TrustedBank/Erdos287/GoodPrime.lean:139
LITERAL STATEMENT:theorem logCofactor_finite_blocker {J x q₀ q₁ : ℕ}
                    (hxN : ce.N ≤ x) (hxM : x + 1 ≤ ce.M)
                    (hq0 : q₀.Prime) (hq1 : q₁.Prime)
                    (hlow0 : ce.M ≤ 2 * J * q₀) (hlow1 : ce.M ≤ 2 * J * q₁)
                    (hsq0 : ce.M < q₀ ^ 2) (hsq1 : ce.M < q₁ ^ 2)
                    (hC0 : C (2 * J) < (q₀ : ℤ)) (hC1 : C (2 * J) < (q₁ : ℤ))
                    (hd0 : q₀ ∣ x) (hd1 : q₁ ∣ x + 1) : False
USED BY:          Audit/BankStatus.lean, Status/Delta6Ledger.lean, and (new)
                  Erdos287.Gap2CE.no_of_placedLCBeta
STATUS:           banked, unchanged
```

```
OBJECT:           C(j)
LEAN NAME:        Erdos287.C
FILE:             RequestProject/Erdos287/Defs.lean:60
LITERAL STATEMENT:def C (j : ℕ) : ℤ :=
                    ((((List.range j).map (· + 1)).sublists.filter
                      (fun l => l ≠ [])).map numOf).foldr max 0
USED BY:          window exclusion, GoodPrime, all blockers
STATUS:           banked, unchanged (values C 1 … C 8 certified by `decide`)
```

```
OBJECT:           the banked upper bound corresponding to C(j) ≤ j·j!
LEAN NAME:        Erdos287.C_le_U   (with Erdos287.U j = j * j !)
FILE:             RequestProject/Erdos287/Uniform.lean:66  (U at :46)
LITERAL STATEMENT:theorem C_le_U (j : ℕ) : C j ≤ (U j : ℤ)
USED BY:          primePower_window_exclusion_U, ForcedHole, and (new)
                  Erdos287.logCofactor_asymptotic287
STATUS:           banked, unchanged
```

```
OBJECT:           existing PlacedLCBeta-like / upper-half placement predicate
LEAN NAME:        (i) Erdos287.WindowPairSupply  — carries `M ≤ 2 * x`
                  (ii) TrustedBank.Erdos287Good.Gap2CE.goodPrime_adjacent_blocker_upper_half
FILE:             ClosureInputs.lean:43 ; GoodPrime.lean:115
LITERAL STATEMENT:(ii) theorem goodPrime_adjacent_blocker_upper_half {x q₀ q₁ : ℕ}
                       (hhalf : ce.M < 2 * x) (hxN : ce.N ≤ x) (hxM : x + 1 ≤ ce.M)
                       (h0 : GoodPrime ce.M q₀) (h1 : GoodPrime ce.M q₁)
                       (hd0 : q₀ ∣ x) (hd1 : q₁ ∣ x + 1) : False
USED BY:          (i) the closure compiler; (ii) nothing
STATUS:           banked, unchanged.  (ii) takes `hhalf` but does **not** derive
                  `ce.N ≤ x` from it — `hxN` is a separate hypothesis.
```

```
OBJECT:           any theorem already repairing the missing lower placement
LEAN NAME:        Erdos287.Gap2CE.blocker_window   (the only one)
FILE:             RequestProject/Erdos287/FiniteRemainder.lean:73
LITERAL STATEMENT:… (hUx : U ≤ 2 * x) (hxL : x + 1 ≤ L) (h1 : L ≤ ce.M) (h2 : ce.M ≤ U)
                  : False,  whose proof contains
                    have hN : ce.N ≤ ce.M / 2 := ce.halfRange_min_le hM2
                    have hNx : ce.N ≤ x := by omega
USED BY:          FiniteRangeExtension, ClosureInputs
STATUS:           banked, unchanged.  The placement step exists **inside** this proof
                  but was never exposed as a reusable lemma, and it is not available
                  to the log-cofactor blocker.
```

### A1. Hostile check of the current `LCBeta`

**Verdict: `LCBETA_PLACEMENT_MISSING`.**

Literal check: `LCBeta M J` records `x + 1 ≤ M` and nothing that bounds `x` from below.
It is satisfiable with `x` strictly below `M/2` — kernel-checked witness
`Erdos287.lcBeta_witness_below_half : Challenges.Delta6.LCBeta 30 3`
(`x = 13`, `q₀ = 13`, `q₁ = 7`, `2x = 26 < 30 = M`).  Hence no derivation of `N ≤ x` from
`LCBeta` is possible, and `LCBeta` cannot be fed to `logCofactor_finite_blocker`.

**Second, independent gap found by the audit** (not in the V11 description): `LCBeta`
also omits the numerator threshold `C (2J) < qᵢ`, which the banked finite blocker
likewise requires.  Both gaps are repaired append-only.

**Repair (append-only, historical predicate untouched):**

* `Erdos287.PlacedLCBeta M J` (`RequestProject/Erdos287/PlacedLCBeta.lean`) — the
  `LCBeta` fields plus `C (2*J) < q₀`, `C (2*J) < q₁`, and `M ≤ 2 * x`;
  `Erdos287.UpperHalfLCBeta` is a definitional alias.
* `Erdos287.placedLCBeta_imp_LCBeta` — the repair is strictly stronger.
* `Erdos287.Gap2CE.N_le_of_M_le_two_mul (hM : 2 ≤ ce.M) (h : ce.M ≤ 2 * x) : ce.N ≤ x`
  — proved from the exact banked half-range theorem `halfRange_min_le`.
* `Erdos287.Gap2CE.no_of_placedLCBeta : PlacedLCBeta ce.M J → False` — the append-only
  compiler into `logCofactor_finite_blocker`.  It needs **no** extra hypothesis on `M`:
  `x + 1 ≤ M` together with `M ≤ 2x` already forces `2 ≤ M`.

Compiles in the actual project → **REPAIRED (PASS)**.

---

## B. `LOG-COFACTOR-ASYMPTOTIC287`

File `RequestProject/Erdos287/LogCofactorAsymptotic.lean`; `J(M) = Erdos287.Jlog eta M
= ⌊η·log M / log log M⌋`.

```
theorem logCofactor_asymptotic287 (eta : ℝ) (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∀ q : ℕ, M ≤ 2 * Jlog eta M * q →
      M < q ^ 2 ∧ C (2 * Jlog eta M) < (q : ℤ)
```

The threshold is explicit: `M₀ = ⌈exp T⌉ + 257` with `T = max(17/(1−2η)², 4/η², 6)`.
Primality of `q` is **not needed** and therefore not assumed (the V11 statement for
primes is the special case).

Proof ingredients, all proved in the file, none assumed:

* `log_le_two_sqrt : log x ≤ 2√x`;
* `log_sq_lt_self : (log M)² < M` for `M > 256`, via `log M ≤ 4·M^{1/4}`;
* `J(M) ≤ η log M / log log M` (`Nat.floor_le`) and `2J(M) ≤ log M`
  (uses `2η < 1 ≤ log log M`);
* `1 ≤ J(M)` (uses `log log M ≤ 2√(log M)` and `log M ≥ 4/η²`);
* `M > 4J²` ⟹ `q ≥ M/(2J)` ⟹ `q² > M`;
* `(2J+2)·log(2J) ≤ 2η log M + 2 log log M < log M` — this is the explicit-ε form of
  `log C(2J) ≤ (2η + o(1)) log M`, the strict inequality coming from
  `2 log log M ≤ 4√(log M) < (1−2η) log M`;
* exponentiating, `(2J)^{2J+2} < M`; with the banked `C_le_U` and
  `Nat.factorial_le_pow` this gives `C(2J) ≤ 2J·(2J)! ≤ (2J)^{2J+1} < q`.

Also proved: `placedLCBeta_of_adjacent_large_prime_factors` — above the threshold the two
"prime-factor" side conditions of `PlacedLCBeta` are automatic, so only the arithmetic
supply (an adjacent pair in the upper half with large prime factors) remains.

**Verdict: `LOG_COFACTOR_ASYMPTOTIC287_KERNEL_PASS`.**  No external asymptotic lemma was
needed; nothing is conditional.

---

## C. `FIXED-CERTIFICATE-TRANSFERENCE287`

File `RequestProject/Erdos287/FixedCertificateTransference.lean` (pure finite/order
algebra over an arbitrary index type; no Ford–Maynard import, no analysis).

* `Erdos287.Transference.sum_a_P_identity` — the exact partition identity
  `∑_P a = B + Total − Leak − ∑_N w·H`.
* `Erdos287.Transference.sum_a_P_lower` — with `w = a − b`, `0 ≤ a`, `H = 1` on `P`,
  `H ≤ 0` on `N`, `|Total| ≤ E`, `|Leak| ≤ E`, `∑_N b·H ≥ C·B − E`:
  `∑_{p∈P} a p ≥ (1 + C)·B − 3E`.
* `Erdos287.Transference.sum_a_P_pos` — with `E ≤ δ·B`, `0 < B`, `3δ < 1 + C`:
  `∑_{p∈P} a p ≥ (1 + C − 3δ)·B > 0`.
* `Erdos287.Transference.transference_nonvacuous` — the hypotheses are simultaneously
  satisfiable (non-vacuity guard).

`#print axioms` for all four: `[propext, Classical.choice, Quot.sound]`.

**Verdict: `FIXED_CERTIFICATE_TRANSFERENCE287_KERNEL_PASS`.**

---

## D. Quadratic-Kummer backend

### D1. Finite Cauchy / correlation compiler — `KERNEL PASS`

File `RequestProject/Erdos287/KummerFiniteCompiler.lean`, no number theory:

```
theorem kummer_bilinear_of_correlation_bounds …
    (hsub : ∀ n, exc n ⊆ In) (hcard : ∀ n ∈ In, ((exc n).card : ℝ) ≤ s)
    (hsymm : ∀ n₁ ∈ In, ∀ n₂ ∈ In, (n₂ ∈ exc n₁ ↔ n₁ ∈ exc n₂))
    (hMb0 : 0 ≤ Mb) (hR0 : 0 ≤ R)
    (hExc : ∀ n₁ ∈ In, ∀ n₂ ∈ exc n₁, |∑ m ∈ Im, K m n₁ * K m n₂| ≤ Mb)
    (hNonExc : ∀ n₁ ∈ In, ∀ n₂ ∈ In, n₂ ∉ exc n₁ → |∑ m ∈ Im, K m n₁ * K m n₂| ≤ R) :
    (∑ m ∈ Im, ∑ n ∈ In, alpha m * beta n * K m n) ^ 2
      ≤ (∑ m ∈ Im, alpha m ^ 2) * (∑ n ∈ In, beta n ^ 2) * (s * Mb + R * In.card)
```

*Audit note / repair:* the symmetry hypothesis is stated **relative to `In`**.  The naive
global form `∀ n₁ n₂, n₂ ∈ exc n₁ ↔ n₁ ∈ exc n₂` is false for the intended exceptional
set (`exc n = In.filter (· = ±n)`), because membership in `In` is one-sided; the proof
only ever needs the restricted form.

### D2. Root-stabilizer algebra — `KERNEL PASS`

File `RequestProject/Erdos287/KummerRootStabilizer.lean`, over an **arbitrary field**
(so `ZMod p` for odd `p`, and characteristic 2 as well), **without** a splitting field:
the criterion is proved on coefficients, so the irreducible quadratic case is covered
with no assumption that the roots lie in the base field.

* `quadPoly_separable`, `quadPoly_squarefree` — nonzero discriminant ⟹ squarefree, via
  the characteristic-free Bézout identity `4a·F − (F′)² = 4ac − b²` (`quadPoly_bezout`);
* `exists_const_of_scaling_square` — if `F(n₁X)·F(n₂X) = G²` then
  `F(n₂X) = F(n₁X)·C v` with `v = u²` a nonzero square (uses
  `Squarefree.dvd_pow_iff_dvd` and a degree count);
* `quadratic_scaling_square_criterion` — hence `n₂ = n₁` or `n₂ = −n₁`
  (`n₁, n₂ ≠ 0` are excluded explicitly; the case `c = 0`, where one root is `0`, is
  handled separately and forces `n₂ = n₁`);
* `quadratic_scaling_square_criterion_of_b_ne_zero` — if `b ≠ 0` then `n₂ = n₁`, unless
  the characteristic is 2;
* `scalingSquareStabilizer_subset ⊆ {n₁, −n₁}` and
  `scalingSquareStabilizer_ncard_le_two` — **the stabilizer has at most two elements**;
  `mem_scalingSquareStabilizer_self` shows it is nonempty (bound not vacuous);
* `repeated_root_scaling_square` — in the excluded `disc = 0` sector the product is a
  square for *every* pair of scalings, so the discriminant hypothesis is necessary.

### D3. Weil / interval completion — `WEIL_INPUT_EXTERNAL_INTERFACE_REQUIRED`

A search of Mathlib (the pinned `v4.28.0` tree) and of this project finds **no** Weil
bound for curves and **no** incomplete-character-sum completion estimate.  Nothing was
axiomatized.  File `RequestProject/Erdos287/KummerWeilInterface.lean` instead declares

```
structure QuadraticKummerCorrelationBound (Im : Finset ιM) (In : Finset K)
    (Kern : ιM → K → ℝ) (Mb R : ℝ) : Prop where
  exceptional : ∀ n₁ ∈ In, ∀ n₂ ∈ pmExceptional In n₁, |∑ m ∈ Im, …| ≤ Mb
  completion  : ∀ n₁ ∈ In, ∀ n₂ ∈ In, n₂ ∉ pmExceptional In n₁ → |∑ m ∈ Im, …| ≤ R
  nonneg      : 0 ≤ Mb ∧ 0 ≤ R
```

and proves, from that interface plus D1 (with `s = 2`, justified by D2 through
`pmExceptional_card_le_two`):

```
theorem kummer_bilinear_of_interface … :
    (∑ m ∈ Im, ∑ n ∈ In, alpha m * beta n * Kern m n) ^ 2
      ≤ (∑ m ∈ Im, alpha m ^ 2) * (∑ n ∈ In, beta n ^ 2) * (2 * Mb + R * In.card)
```

No term of the interface structure is constructed anywhere; supplying one is exactly the
external obligation.  `not_square_of_not_pmExceptional` records the D2 ⇒ D3 link
(nonexceptional pairs give a genuinely nonsquare product).

---

## E. Seven-prime `5|2` specialization and exponent ledger — `KERNEL PASS`

File `RequestProject/Erdos287/KummerExponentLedger.lean`.  With `M = Y⁵`, `N = Y²`,
`X = Y⁹`, `p = Y^θ`:

* `exponent_ledger` / `exponent_ledger_max` — for rational `θ ∈ [5/2, 8]`,
  `max(−2, −θ/2, θ/2 − 5) ≤ −1`;
* the two controlling endpoints: `exponent_ledger_endpoint_low` (`θ = 5/2`, value
  `−5/4`, slack) and `exponent_ledger_endpoint_high` (`θ = 8`, value exactly `−1`,
  tight);
* `exponent_ledger_fails_above_eight` — the constraint `p ≤ Y⁸` is necessary;
* `kummer_savings_bound` — for real `Y ≥ 1`,
  `(Y^{−2} + p^{−1/2} + p^{1/2}Y^{−5})^{1/2} ≤ √3 · Y^{−1/2}`;
* `margin_Y_eq_X` — the fixed-power margin `Y^{−1/2} = X^{−1/18}` for `X = Y⁹`
  (`margin_exponent`: `9·(−1/18) = −1/2`).

The `X^{o(1)}` symbols are deliberately not modelled; only the deterministic rational
exponent margin is certified.

---

## F. Degeneracy routers — `SOURCE BLOCKED`

```
ROUTER:                     repeated-root / discriminant-zero sector
EXACT CONDITION:            disc F = b² − 4ac = 0
DIMENSION/VARIABLE LOSS:    (not derivable here: no source)
TARGET THEOREM:             separate treatment of the square-product sector
LEAN STATUS:                the *sector itself* is now delimited:
                            Erdos287.Kummer.repeated_root_scaling_square proves the
                            product is always a square there, so it is genuinely
                            disjoint from the generic packet, and
                            quadPoly_squarefree shows disc ≠ 0 ⟹ generic.
ANALYTIC INPUT STILL NEEDED:everything (no bound proved for this sector)
```

```
ROUTER:                     isolated pure multiplicative-character mode
                            principal / zero mode
                            nonunit / repeated-prime / collision / conductor-loss strata
EXACT CONDITION:            SOURCE BLOCKED
DIMENSION/VARIABLE LOSS:    SOURCE BLOCKED
TARGET THEOREM:             SOURCE BLOCKED
LEAN STATUS:                no H8/H9 object, no affine-audit router, no Kummer packet
                            and no `H8`, `H9`, `Kummer`, `Weil` or Ford (7.23) identifier
                            exists anywhere in this repository (verified by full-text
                            search of all sources).
ANALYTIC INPUT STILL NEEDED:the literal source definitions, absent from the repository
```

Nearest banked relatives, for orientation only (they are *not* the routers): the
repeated-prime sector counterexample `TrustedBank.Gate1B.moebius_prime_sq_eq_zero` /
`moebius_div_prime_fails_at_prime_square`, the non-coprime ρ counterexample
`TrustedBank.Gate1B.rho_not_multiplicative_of_not_coprime`, and the local-root data
`TrustedBank.SingularFactors`.

---

## G. `H8H9-SOURCE-TO-KUMMER45`

The literal physical packet before support enlargement does not exist in this
repository, in any form: there is no `H8`, `H9`, `Kummer45`, `SOURCE-ADAPTER45`,
Ford (7.23) or prefactor/Möbius-sign record to transcribe, and the request explicitly
forbids reconstruction from a schematic parent formula.

**Verdict: `H8H9_SOURCE_TO_KUMMER_SOURCE_BLOCKED`.**

---

## H. Fixed-certificate leakage compiler

File `RequestProject/Erdos287/FixedCertificateLeakageCompiler.lean`.

* **Concrete certificate `g*`: absent.**  No admissible fixed Ford certificate, no
  `H_{g*}`, no literal `P`, `N_ε`, `U` and no published `C_{g*}` exists in this
  repository.  The certificate-specific data is therefore carried by the abstract record
  `FixedCertificateData` (partition `P`/`Ngood`/`U`, weights `a`, `b`, kernel `H`, with
  `0 ≤ a`, `H = 1` on `P`, `H ≤ 0` on `Ngood`).
* **Finite partition identity:** `Transference.sum_a_P_identity` (Part C).
* **Compiler** (analytic inputs only as named antecedents, none hidden in a definition):

```
theorem fixedCertificate_leakage_compiler (d) (Cc E) :
    LeakageBound d E → TotalCorrelationBound d E → ComparisonMargin d Cc E →
    PrimeMassLowerBound d ((1 + Cc) * d.B - 3 * E)
```

* **`N2` repair kept separate:** `fixedCertificate_leakage_compiler_N2` carries an
  independent slack `E₂` (`ComparisonMarginN2`), which appears only additively.
* **Comparison margin / positivity:** `fixedCertificate_prime_mass_pos` gives
  `0 < ∑_{p∈P} a p` from `E ≤ δ·B`, `0 < B`, `3δ < 1 + C_{g*}`.  Whether
  `1 + C_{g*} > 0` holds for a concrete certificate is **source-open**: no concrete
  value of `C_{g*}` exists in this repository, so it is a hypothesis
  (`margin_positive_of_hyps` records that the hypotheses force it).

**Verdict: `FIXED-CERTIFICATE LEAKAGE COMPILER: KERNEL PASS (compiler), certificate
SOURCE BLOCKED`.**  The analytic estimate `287-FIXED-CERTIFICATE-LEAKAGE45` itself is
**OPEN** and is nowhere assumed.

---

## I. Optional route firewall

`FullFMTypeII_1/6`, the generated Ford (7.23) packets, `SOURCE-ADAPTER45` and the global
replacement certificate `C_FM` are **not deleted and not weakened** (they are, in fact,
not present as Lean objects at all; the retired-route registry
`Challenges.Delta6.RetractedRoute` is untouched).  The only logical fact recorded is
`Status.Erdos287GoldV11.fixedCertificateRoute_sufficient`: *if* the fixed-certificate
hypotheses hold, the prime-mass conclusion follows.  No relative-strength claim is made.

---

## J/K. Files added and build / axiom audit

Files added (all new; no historical file rewritten):

| File | Role |
| --- | --- |
| `RequestProject/Erdos287/PlacedLCBeta.lean` | A — placement repair + compiler |
| `RequestProject/Erdos287/LogCofactorAsymptotic.lean` | B — asymptotic |
| `RequestProject/Erdos287/FixedCertificateTransference.lean` | C — transference kernel |
| `RequestProject/Erdos287/KummerFiniteCompiler.lean` | D1 — Cauchy compiler |
| `RequestProject/Erdos287/KummerRootStabilizer.lean` | D2 — root-stabilizer algebra |
| `RequestProject/Erdos287/KummerWeilInterface.lean` | D3 — external interface |
| `RequestProject/Erdos287/KummerExponentLedger.lean` | E — exponent ledger |
| `RequestProject/Erdos287/FixedCertificateLeakageCompiler.lean` | H — leakage compiler |
| `RequestProject/Status/Erdos287GoldV11Status.lean` | I/K — route note + axiom prints |
| `ERDOS287_GOLD_V11_REPORT.md` | this report |

`RequestProject/Main.lean` received nine `import` lines and nothing else.

**Build:** `lake build` completes successfully (8095 jobs), including
`RequestProject.Main`.

**Axioms:** every new theorem reports `[propext, Classical.choice, Quot.sound]`
(`Erdos287.placedLCBeta_imp_LCBeta` reports only `[propext]`); the full list is printed
by `RequestProject/Status/Erdos287GoldV11Status.lean`.  Role and external-interface use
per theorem: all Part A/B/C/D1/D2/E/H theorems are unconditional
(`USES EXTERNAL INTERFACE: no`); the single theorem using an external interface is
`Erdos287.Kummer.kummer_bilinear_of_interface`
(`USES EXTERNAL INTERFACE: QuadraticKummerCorrelationBound`), and the leakage-compiler
theorems consume named analytic *hypotheses* (`LeakageBound`, `TotalCorrelationBound`,
`ComparisonMargin`), which are propositions supplied by the caller, not assumptions of
the file.

**Placeholder scan** of the new files for `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, `native_decide`, `@[implemented_by]`: **none occur**, in any position.  The
strings `axiom`/`sorry` appear only inside documentation prose (e.g. "does not assume it
as an axiom"), never as Lean syntax.

---

## L. Final ledger

```
LCBETA PLACEMENT:
REPAIRED        (verdict LCBETA_PLACEMENT_MISSING; append-only repair
                 Erdos287.PlacedLCBeta + Gap2CE.N_le_of_M_le_two_mul
                 + Gap2CE.no_of_placedLCBeta, all compiling)

LOG-COFACTOR-ASYMPTOTIC287:
KERNEL PASS     (Erdos287.logCofactor_asymptotic287, explicit threshold,
                 no external asymptotic)

FIXED-CERTIFICATE-TRANSFERENCE287:
KERNEL PASS     (Erdos287.Transference.sum_a_P_lower / sum_a_P_pos)

QUADRATIC-KUMMER FINITE COMPILER:
KERNEL PASS     (Erdos287.Kummer.kummer_bilinear_of_correlation_bounds)

ROOT-STABILIZER ALGEBRA:
KERNEL PASS     (Erdos287.Kummer.quadratic_scaling_square_criterion,
                 scalingSquareStabilizer_ncard_le_two; arbitrary field,
                 no splitting field needed)

WEIL / INTERVAL COMPLETION:
EXTERNAL INTERFACE  (WEIL_INPUT_EXTERNAL_INTERFACE_REQUIRED;
                     Erdos287.Kummer.QuadraticKummerCorrelationBound, never inhabited)

SEVEN-PRIME EXPONENT LEDGER:
KERNEL PASS     (Erdos287.KummerLedger.*, margin Y^{-1/2} = X^{-1/18})

KUMMER DEGENERACY ROUTERS:
SOURCE BLOCKED  (only the repeated-root sector could be delimited, and it is:
                 repeated_root_scaling_square / quadPoly_squarefree)

H8H9-SOURCE-TO-KUMMER45:
SOURCE BLOCKED

FIXED-CERTIFICATE LEAKAGE COMPILER:
KERNEL PASS for the compiler; the certificate g* itself is SOURCE BLOCKED

287-FIXED-CERTIFICATE-LEAKAGE45 ANALYTIC ESTIMATE:
OPEN

ERDOS287:
OPEN
```

```
EXACT FIRST OPEN AFTER THIS RUN:
Erdos287.PlacedLCBeta M (Erdos287.Jlog η M) for all sufficiently large M — i.e. for
each large M an adjacent pair x, x+1 with M ≤ 2x, x+1 ≤ M, such that x and x+1 each
have a prime factor q with M ≤ 2·J(M)·q.  (Every other field of PlacedLCBeta is now
automatic above the threshold of logCofactor_asymptotic287.)

NEXT MATHEMATICAL ACTION:
Prove, or supply from the literature with an effective threshold, the adjacent
large-prime-factor supply above: for all large M there exist x with M/2 ≤ x < M such
that both x and x+1 have a prime factor ≥ M/(2·J(M)), J(M) = ⌊η log M / log log M⌋.
```
