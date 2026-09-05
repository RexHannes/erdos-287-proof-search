# ERDŐS #287 — ONE-LEVEL MÖBIUS SAFE BANK REPORT

**Delta:** POST-CAUCHY REPAIR → PRODUCT-MODULUS COMPRESSION → SHARED-GCD GRAM-AS-SQUARE →
ONE-LEVEL MÖBIUS FRONTIER.

**Mode:** APPEND-ONLY EXACT ALGEBRA / FINITE COMBINATORICS / STATUS UPDATE.

---

## 1. HISTORICAL BANK PRESERVED

This delta is **strictly additive**. `git diff` against the pre-delta commit over the whole
protected list is empty:

```
PrimitiveRamanujanAlgebra          PrimitiveReducedDenominator
PrimitiveRamanujanReassembly       PrimitiveNearFreqCount
ShortLiftLocalProfile              SharedG0CauchyConfigurationSocket
LocalProfileHarmonicTwists         CurrentStatusErdos287SharedG0Repair
SharedG0PrimitiveUParam            ARISTOTLE_SUMMARY.md
SharedG0PrimitiveURouter
SharedG0UnitSectorGcd
SharedG0BPairAveraged
```

Nothing above was rebuilt, edited, renamed or re-proved. Ten new files were added; the single
edit to a pre-existing file is the **import block of `RequestProject/Main.lean`** (nine new
`import` lines appended, no other change), which is exactly the "imports if necessary"
allowance.

Preservation is additionally *machine-checked* inside Lean by
`Erdos287.OneLevelMobiusStatus.historical_sharedG0_status_preserved`, which re-derives, from the
imported historical ledgers,

* `SharedG0RepairStatus.ledger erdos287 = open_`,
* `SharedG0RepairStatus.ledger fcl = notReached`,
* `SharedG0RepairStatus.ledger sharedG0CauchyConfiguration45 = analyticRepairOpen`,
* no `closed` row in `SharedG0RepairStatus`, `PrimitiveLocalProfileStatus`, or `Block20Status`.

**All pre-existing analytic sockets remain UNINHABITED.** None was given an instance,
inhabitant, or closing theorem.

---

## 2. STATUS SUPERSESSIONS (§0, §14)

The old row

```
CURRENT FIRST RESIDUAL: SHAREDG0-CAUCHY-CONFIGURATION45
```

is **historical / superseded**. It is *not* closed; it is a research pass that no longer ranks
first. This is banked as a theorem, not prose:
`cauchyConfiguration_superseded_not_closed` proves
`ledger sharedG0CauchyConfiguration = researchPassSuperseded`, that this label `≠ closed`, and
that `residualRank sharedG0CauchyConfiguration = 0`.

New append-only ledger: `RequestProject/Status/CurrentStatusErdos287OneLevelMobius.lean`
(`Erdos287.OneLevelMobiusStatus.ledger`). Rows, exactly as specified in §14:

| Row | Label |
|---|---|
| `SHORTLIFT-EULER` | `nancVerifiedPassUninhabited` |
| `SHAREDG0-BPAIR-AVERAGED` | `formalCorePass` |
| `SHAREDG0-CAUCHY-CONFIGURATION` | `researchPassSuperseded` |
| `LARGESHAREDG0` | `retractedAnalyticOpen` |
| `PRIMITIVE-NEARFREQ` | `openNonclosing` |
| `HARD-DENOMINATOR CORE` | `notPromoted` |
| `LEVELPAIR-PRODUCTMOD-SIGN` | `formalPass` |
| `DET1-D-N-COPRIME` | `formalPass` |
| `LEVELPAIR-N-DIVISORSPLIT` | `formalPass` |
| `FIXEDD-FREQUENCY-RIGIDITY` | `formalPass` |
| `LEVELPAIR-N-RECIPROCAL-NORMALFORM` | `formalPass` |
| `LEVELPAIR-PRIMEASSIGNMENT` | `formalFixedNPass` |
| `SHAREDGCD-GRAM-SQUARE` | `formalPass` |
| `PRIMITIVE-t RAMANUJAN FIREWALL` | `formalPass` |
| `SHAREDGCD-ONELEVEL-ENERGY` | `provisionalResearchSubpolytope` |
| `SHAREDG0-SIGNED-LEVELPAIR-GRAM45` | `strictlyReduced` |
| `SHAREDGCD-ONELEVEL-MOBIUS-GRAM45` | `analyticOpen` |
| `UNIFORM k=0` | `open_` |
| `FCL` | `notReached` |
| `ERDOS287` | `open_` |

Exponents: `nearDensityExponent = 1/2` (Q-level near-density gain) and
`finalAmplitudeExponent = 1/4` (final amplitude gain); `amplitude_exponents` proves both values
and that they differ.

Integrity theorems (all kernel-checked):
`no_closed_rows`, `erdos287_open`, `uniform_k0_open_fcl_not_reached`,
`largeSharedG0_retracted_and_nearFreq_open`, `signed_levelPair_gram_strictly_reduced`,
`energy_subpolytope_provisional_not_closed`,
`oneLevelMobiusGram_is_first_exact_residual` (uniqueness of rank 1 included).

**`no_closed_rows` holds: this delta closes nothing.**

---

## 3. NEW EXACT ALGEBRA

Seven new modules under `RequestProject/CurrentProgramme/`.

### §§1–3, §5 — `LevelPairProductModulus.lean` (`Erdos287.LevelPairProduct`)

`moebius_levelPair_compress`, `moebius_levelPair_eq_moebius_n`, `lcm_levelPair_eq`,
`gcd_D_n_eq_one`, `gcd_D_lambda_dvd_g0_reexport`, `unitary_split_coprime`,
`unitary_split_dvd`, `levelPair_norm_eq`, `levelPair_divisorSplit`,
`levelPair_reindex_fixed_n`, `levelPair_reindex`, `fareyDifference_eq_D_div_g0n`,
`fareyDifference_split_invariant`.

### §4 — `LevelPairFixedDRigidity.lean` (`Erdos287.LevelPairRigidity`)

`t1_congr_mod_r1`, `t2_congr_mod_r2`, `fixedD_solution_of_bezout`, `fixedD_solution_iff`,
`fixedD_u_period_g0`, `primitive_split_g0_r`, `primitive_r_side_independent_of_u`,
`fixedD_primitive_reduces_to_g0_side`.

### §6 — `LevelPairReciprocalNormalForm.lean` (`Erdos287.LevelPairReciprocal`)

`exists_crtBeta`, `gcd_eq_one_of_congr`, `gcd_two_g0_beta_eq_one`, `crtNumerator`,
`crtNumerator_congr`, `crtNumerator_rat`, `reciprocal_phase_normalForm`,
`reciprocal_normalForm_of_inverse`, `global_inverse_restricts`.

### §§7–8 — `LevelPairPrimeAssignment.lean` (`Erdos287.LevelPairPrimeAssignment`)

`unitary_split_injOn`, `unitary_split_image`, `fixed_n_two_state_product`, `localFactorK`,
`coeffK`, `localFactorK_not_multiplicative`.

### §§9–10 — `SharedGcdGramSquare.lean` (`Erdos287.SharedGcdGram`)

`lambdaH`, `sum_lambdaH_divisors`, `divisorSupport`, `levelSlice`, `cofactorSlice`,
`gcd_divisors_eq_filter`, `omega_gcd_eq_indicator_sum`, `gramSharedGcd`, `slice_sum_eq_square`,
`double_sum_indicator`, `gram_expand`, `sharedGcd_gram_square`, `moebius_split_clean_sector`,
`levelSlice_sum_factor`, `norm_sq_moebius_div`, `sharedGcd_oneLevel_gram`, `abs_lambdaH_le`,
`biUnion_divisorsAntidiagonal`, `lambdaH_harmonic_mass_le`, `omega_support_mass_le`.

### §12 — `PrimitiveTRamanujanFirewall.lean` (`Erdos287.PrimitiveTFirewall`)

`int_gcd_prime_eq_one`, `ramanujan_prime_not_dvd`, `ramanujan_prime_dvd`,
`moebius_mul_ramanujan_prime`, `moebius_ramanujan_normalForm_reexport`.

### §§11, 13 — `SharedGcdOneLevelMobiusSocket.lean` (`Erdos287.SharedGcdOneLevel`)

`EnergyLedger` (+ `subpolytopeMargin`, `Valid`), `exists_valid_energyLedger`,
`SharedGcdOneLevelEnergyInput`, `sharedGcdOneLevelEnergy_compiler`,
`sharedGcdOneLevelEnergy_not_automatic`; `OneLevelMobiusConfig` (+ `source`, `Valid`),
`exists_valid_config_with_positive_source`, `SharedGcdOneLevelMobiusGramInput`,
`sharedGcdOneLevelMobiusGram_compiler`, `sharedGcdOneLevelMobiusGram_not_automatic`.

---

## 4. PRODUCT-MODULUS COMPRESSION (§§1–5)

With `g1 = g0·r1`, `g2 = g0·r2`, `gcd(r1,r2) = 1`, `gcd(g0, r1r2) = 1`, everything squarefree,
and `n = r1·r2`:

* `moebius_levelPair_compress` : `μ(g1)·μ(g2) = μ(r1)·μ(r2)` — the shared-`g0` sign cancels
  because `μ(g0)² = 1` on the squarefree support.
* `moebius_levelPair_eq_moebius_n` : `μ(g1)·μ(g2) = μ(n)`.
* `lcm_levelPair_eq` : `lcm(g1,g2) = g0·n`.
* `gcd_D_n_eq_one` (**DET1-D-N-COPRIME45**) with `D = t1·r2 − t2·r1`: proved **directly** from
  the primitivity hypotheses `gcd(t1,g1) = gcd(t2,g2) = 1`, not merely as a corollary of the
  banked `gcd(D,Λ) ∣ g0`. That older implication is still recorded, as
  `gcd_D_lambda_dvd_g0_reexport`.
* `levelPair_norm_eq` : `1/(g1·g2) = 1/(g0²·n)`.
* `unitary_split_coprime` / `unitary_split_dvd` : for squarefree `n` and `r ∣ n`, `r ∣ n`,
  `gcd(r, n/r) = 1`, `r·(n/r) = n` — ordered level pairs correspond exactly to unitary divisor
  splits (`levelPair_divisorSplit`).
* `levelPair_reindex_fixed_n` / `levelPair_reindex` : the exact finite reindexing

  ```
  Σ_{g1,g2} μ(g1)μ(g2)/(g1g2) K(g1,g2)
    =  Σ_{g0} 1/g0² Σ_n μ(n)/n Σ_{r|n} K(g0·r, g0·(n/r)).
  ```

  No asymptotic dyadic range is formalised.
* `fareyDifference_eq_D_div_g0n` : `t1/g1 − t2/g2 = D/(g0·n)`, hence
  `fareyDifference_split_invariant`: the additive/Farey datum depends only on `(g0, n, D)` and
  **not** on the unitary split `r ∣ n`. No analytic property of `Φ_A` is formalised.

**Fixed-`D` rigidity (§4).** `t1_congr_mod_r1` / `t2_congr_mod_r2` give
`t1 ≡ D·r2⁻¹ (mod r1)` and `t2 ≡ −D·r1⁻¹ (mod r2)`. `fixedD_solution_iff` is the *exact
if-and-only-if* general solution `t1 = xD + r1·u`, `t2 = yD + r2·u` under a Bézout pair.
`fixedD_u_period_g0` isolates the surviving degree of freedom as `u mod g0`;
`primitive_r_side_independent_of_u` shows the `r`-side primitivity conditions are
`u`-independent, so `fixedD_primitive_reduces_to_g0_side` reduces the primitive restrictions to
exactly the `g0`-side conditions of the research source.

**CRT reciprocal normal form (§6).** `exists_crtBeta` produces `β_r` with `β_r ≡ b1 (mod r)`,
`β_r ≡ b2 (mod n/r)`; `gcd_two_g0_beta_eq_one` proves `gcd(2·g0·β_r, n) = 1` under the unit
hypotheses; `crtNumerator` / `crtNumerator_congr` / `crtNumerator_rat` give the explicit CRT
numerator `Ξ_r`; `reciprocal_phase_normalForm` and `reciprocal_normalForm_of_inverse` bank the
exact phase identity `e_n(s·D·(2·g0·β_r)⁻¹)`.

**Fixed-`n` prime assignment (§7).** `fixed_n_two_state_product` is the finite combinatorial
equivalence: for squarefree `n`, a unitary split is a two-state choice per prime `p ∣ n`, and

```
Σ_{r|n} (∏_{p|r} L_{p,1})(∏_{p|(n/r)} L_{p,2}) = ∏_{p|n} (L_{p,1} + L_{p,2}).
```

This is banked as a **fixed-`n` factorisation only**. No multiplicativity in `n` is asserted.

---

## 5. SHARED-GCD GRAM-AS-SQUARE (§§9–10)

Highest-priority exact bank; fully proved.

* `lambdaH Om = μ ∗ Om` on the divisor lattice, and `sum_lambdaH_divisors` is the Möbius
  inversion `Ω_H(m) = Σ_{d ∣ m} λ_H(d)`; `omega_gcd_eq_indicator_sum` turns this into
  `Ω_H(gcd(g1,g2)) = Σ_{d ∣ g1, d ∣ g2} λ_H(d)`.
* `sharedGcd_gram_square` — the exact Gram identity

  ```
  Q_H = Σ_d λ_H(d) Σ_a ρ(a) | Σ_{d|g} w_g V_g(a) |².
  ```

  Every double sum over `(g1,g2)` becomes a genuine square of a level slice; no positivity or
  size hypothesis is used, only `0 < g` on the level set.
* On the squarefree clean sector `g = d·m`, `gcd(d,m) = 1`, `moebius_split_clean_sector` gives
  `μ(g) = μ(d)μ(m)`, and since `|μ(d)|² = 1` on the active support (`norm_sq_moebius_div`),
  `sharedGcd_oneLevel_gram` derives the **one-level form**

  ```
  Q_H = Σ_d λ_H(d)/d² Σ_a ρ(a) | Σ_m μ(m)/m V_{dm}(a) |².
  ```

* §10 harmonic mass: `abs_lambdaH_le` is `|λ_H(d)| ≤ Σ_{e|d} |μ(d/e)||Ω_H(e)|`;
  `lambdaH_harmonic_mass_le` is the exact finite convolution inequality

  ```
  Σ_d |λ_H(d)|/d² ≤ (Σ_e |Ω_H(e)|/e²)(Σ_k |μ(k)|/k²)
  ```

  on the truncated repository representation; `omega_support_mass_le` is the support-at-`e ∼ H`
  refinement. The **asymptotic `≤ C/H` statement is left as research metadata**; only the exact
  convolution inequality is banked.

---

## 6. FORMAL vs RESEARCH FIREWALL

### Non-multiplicativity firewall (§8)

The research local factors contain `inverse(n/p) mod p`, so ordinary Euler multiplicativity in
`n` is unavailable. Rather than assert a universal negation, one **explicit finite
counterexample** is proved:

```
coeffK 15 = 4,  coeffK 3 = 1,  coeffK 5 = 1,  coeffK 15 ≠ coeffK 3 * coeffK 5
```

(`localFactorK_not_multiplicative`, re-exported as
`nonmultiplicativity_firewall_is_explicit`). No universal negation and no fake
nonmultiplicativity theorem exists anywhere in the delta.

Research metadata (not a Lean claim): *SINGLE-μ(n) ZERO-FREE EULER ROUTE — NONCLOSING / NO EULER
DICTIONARY.*

### Primitive-`t` Ramanujan firewall (§12)

Exact finite algebra only. For squarefree `m` and `N`:

* `p ∤ N` ⟹ `c_p(N) = −1`, hence `μ(p)c_p(N) = +1`;
* `p ∣ N` ⟹ `c_p(N) = p − 1`, hence `μ(p)c_p(N) = −(p−1)`;

(`ramanujan_prime_not_dvd`, `ramanujan_prime_dvd`, `moebius_mul_ramanujan_prime`), together with
the already-available exact divisor normal form for `μ(m)/m · c_m(N)`
(`moebius_ramanujan_normalForm_reexport`). Algebraically this shows complete primitive-`t`
reassembly can neutralise the remaining Möbius sign at generic primes.

The analytic infinite Euler-product claim `ζ(1+w)/ζ(2+2w)` is **not** formalised.
Research status: *ONELEVEL-RAMANUJAN-ZEROFREE45 — REPRESENTATION LOOP / NONCLOSING.*

---

## 7. PROVISIONAL ANALYTIC SUBPOLYTOPE (§11)

The research bound `|Q_H| ≪ (A+G)(GB+B²)/H · log^{o(1)}X` and the claimed fixed-power closed
subpolytope

```
κ > max(α,θ) + max(β,θ) − 1 + δ
```

are **not** Lean analytic theorems. What is formal is only the bookkeeping: `EnergyLedger`
records `(α, β, θ, κ, δ)`, `subpolytopeMargin = κ − (max α θ + max β θ − 1 + δ)`, and
`EnergyLedger.Valid` requires a strictly positive margin. `exists_valid_energyLedger` shows the
strict subpolytope is non-empty, i.e. the constraint set is satisfiable — nothing more.

`SharedGcdOneLevelEnergyInput C energy` is the corresponding analytic input and is left
**UNINHABITED**: `sharedGcdOneLevelEnergy_not_automatic` exhibits explicit `C, energy` with
`¬ SharedGcdOneLevelEnergyInput C energy`, so the interface is provably not free.
`sharedGcdOneLevelEnergy_compiler` records what the input *would* deliver if supplied.

Status: **DET1-SHAREDGCD-ONELEVEL-ENERGY45 — RESEARCH PROVISIONAL PASS ON STRICT SUBPOLYTOPE;
NANC AUDIT PENDING; FORMAL ANALYTIC INPUT UNINHABITED.** The subpolytope is **NOT** marked
closed in the formal proof layer;
`energy_subpolytope_provisional_not_closed` proves the row `≠ closed`.

---

## 8. CURRENT UNINHABITED ANALYTIC SOCKET (§13)

`SharedGcdOneLevelMobiusGramInput K` is the socket for the exact one-level source

```
Σ_d λ_H(d)/d² Σ_a ρ(a) | Σ_m μ(m)/m Σ*_t G̃_{dm}(t) e_{dm}(t·a) |².
```

`OneLevelMobiusConfig` retains, as data: the shared-gcd projector `Om`, the level set and inner
cofactor set, the friable `a` source with weights `ρ`, the **primitive** `t` sets, the twist
`G̃`, the reciprocal `b` source, the smooth `y`, and the harmonic/Perron parameters `H, X,
perronHeight`. Primitive `t` is **not** completed inside the socket — it is carried, not summed
away. `OneLevelMobiusConfig.source` is the exact quantity above and
`exists_valid_config_with_positive_source` shows the configuration class is inhabited with a
strictly positive source (so the socket is not vacuous for lack of data).

The socket itself is **UNINHABITED**: `sharedGcdOneLevelMobiusGram_not_automatic` exhibits `K`
with `¬ SharedGcdOneLevelMobiusGramInput K`. `sharedGcdOneLevelMobiusGram_compiler` records the
downstream consequence conditional on the input.

Research name: **287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45.**
`oneLevelMobiusGram_is_first_exact_residual` proves it is the *unique* rank-1 residual.

---

## 9. AXIOM AUDIT (§15)

New module: `RequestProject/Status/AxiomAuditErdos287OneLevelMobius.lean`. It runs
`#print axioms` on **every** principal declaration of §§1–14 of this delta — 90 audited
declarations across the seven new `CurrentProgramme` modules and the new status ledger.

Result: **every audited declaration depends only on**

```
propext, Classical.choice, Quot.sound
```

(several depend on strictly fewer; `crtNumerator` depends on none). A filtered scan of the audit
output for any axiom outside the allowed list returns nothing.

Source scan over all ten new files for
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`:
**no occurrences** (the only textual hits are the words "admit" and the audit docstring's own
prohibition list, both inside comments).

---

## 10. BUILD

Targeted builds first, then the full build.

* `lake build RequestProject.Status.CurrentStatusErdos287OneLevelMobius` — success.
* `lake build RequestProject.Status.AxiomAuditErdos287OneLevelMobius` — success.
* `lake build` (full default target, after wiring the nine imports into `RequestProject/Main.lean`) —
  **`Build completed successfully (8262 jobs)`**, **0 errors**.

No new warning is introduced by this delta; the warnings that appear are pre-existing
(`This simp argument is unused`, one `unused variable`) in historical modules, which were
deliberately left untouched — no unrelated historical code was repaired.

### Files added

```
RequestProject/CurrentProgramme/LevelPairProductModulus.lean
RequestProject/CurrentProgramme/LevelPairFixedDRigidity.lean
RequestProject/CurrentProgramme/LevelPairReciprocalNormalForm.lean
RequestProject/CurrentProgramme/LevelPairPrimeAssignment.lean
RequestProject/CurrentProgramme/SharedGcdGramSquare.lean
RequestProject/CurrentProgramme/PrimitiveTRamanujanFirewall.lean
RequestProject/CurrentProgramme/SharedGcdOneLevelMobiusSocket.lean
RequestProject/Status/CurrentStatusErdos287OneLevelMobius.lean
RequestProject/Status/AxiomAuditErdos287OneLevelMobius.lean
ERDOS287_ONELEVEL_MOBIUS_SAFE_BANK_REPORT.md
```

### File modified

```
RequestProject/Main.lean   (import block only: nine new import lines)
```

---

## 11. COMMITS

```
ONE-LEVEL MOBIUS delta: level-pair product-modulus algebra and fixed-D rigidity
ONE-LEVEL MOBIUS delta: CRT reciprocal normal form, prime assignment, non-multiplicativity counterexample
ONE-LEVEL MOBIUS delta: shared-gcd projector Gram-as-square and lambda_H harmonic mass
ONE-LEVEL MOBIUS delta: primitive-t Ramanujan firewall and the two uninhabited one-level analytic sockets
ONE-LEVEL MOBIUS delta: append-only status ledger
ONE-LEVEL MOBIUS delta: axiom audit module and Main.lean wiring
ONE-LEVEL MOBIUS delta: safe bank report
```

## 12. PUSH

All commits pushed to `origin HEAD`.

---

## FINAL

```
ERDOS287: OPEN.

CURRENT FIRST EXACT MAIN-LINE RESIDUAL:

    287-K0-SP2-DET1-
    SHAREDGCD-ONELEVEL-MOBIUS-GRAM45.
```
