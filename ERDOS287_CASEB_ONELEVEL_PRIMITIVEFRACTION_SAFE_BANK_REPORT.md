# ERDŐS #287 — CASE-B ONE-LEVEL PRIMITIVE-FRACTION LARGE SIEVE

## Promotion audit, append-only Δ

Every claim below is backed by a kernel-checked Lean statement in this repository.  Nothing was
promoted on the strength of a prose claim, and no status of the incoming request was assumed:
each of Sections 2–10 was re-derived from scratch.

---

## 0. Files changed

**Added — exact mathematics (`RequestProject/CurrentProgramme/`)**

| file | sections |
| --- | --- |
| `OneLevelPrimitiveFractionSpacing.lean` | §2 |
| `OneLevelCoefficientEnergy.lean` | §4 |
| `OneLevelProjectorS1S2.lean` | §6 |
| `OneLevelWeightedLargeSieve.lean` | §§3, 5 |
| `OneLevelPrimitiveFractionGlobal.lean` | §§7–10 |

**Added — status / audit (`RequestProject/Status/`)**

| file | sections |
| --- | --- |
| `CurrentStatusErdos287PrimitiveFractionCaseB.lean` | §§11–12 ledger |
| `AxiomAuditErdos287PrimitiveFractionCaseB.lean` | axiom audit |

**Modified**: `RequestProject/Main.lean` — seven new `import` lines only.  No pre-existing
module was edited; the historical ledgers are imported and re-checked, not rewritten.

**Build**: succeeds.  **Placeholders**: none — no `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, `native_decide` or `implemented_by` in any module of this delta.  Every principal
declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

---

## 1. Section-by-section verification

### §2 Primitive-fraction spacing — **PASS, unconditional**

* `OneLevelSpacing.primitiveFraction_inj`.  With the standard representatives `0 ≤ t < dm`,
  equality **modulo one** of two reduced fractions `t₁/(dm₁)`, `t₂/(dm₂)` forces `m₁ = m₂` and
  `t₁ = t₂`.  Two remarks from the audit: (i) the integer shift is forced to be `0` by the
  representatives, and this step is where `0 ≤ t < dm` is genuinely used; (ii) only
  `(tᵢ, mᵢ) = 1` is needed — the stronger `(tᵢ, dmᵢ) = 1` of the source is not required.
* `OneLevelSpacing.spacing_lower_bound`.  For **every** integer shift `n`, if the integral
  numerator `t₁m₂ − t₂m₁ − n·d m₁ m₂` is nonzero, then the distance is `≥ 1/(d m₁ m₂)`.
* `OneLevelSpacing.spacing_uniform` / `primitiveFraction_separation`.  For `m₁, m₂ ∈ [M, 2M)`
  and `G = dM`, `1/(d m₁ m₂) ≥ d/(4G²)`, hence the banked separation

  ```
  ‖ t₁/(dm₁) − t₂/(dm₂) ‖  ≥  d/(4G²).
  ```

No coprimality with `d` is used in the metric statements.

### §3 Weighted `d`-restricted large sieve — **PASS as a reduction**

* `OneLevelWeightedLS.rho_nonneg`, `rho_le`: for `ρ(a) = 1_{P⁺(a) ≤ Y}·|V(a/A)|`,
  `0 ≤ ρ(a) ≤ ‖V‖_∞`.  The friability cut is a `{0,1}` factor; **no friability estimate is
  needed**.
* `weighted_sum_le_sup_mul`: `∑_a ρ(a)|S(a)|² ≤ ‖ρ‖_∞ ∑_a |S(a)|²`, so the weighted sieve
  reduces to the unweighted one over the containing interval.
* `largeSieve_separation_factor`: with the §2 spacing `δ = d/(4G²)`, the Montgomery–Vaughan
  factor is exactly `(length) + δ⁻¹ = (length) + 4G²/d`.  **No extra logarithm and no `X^ε`**
  enters this step; the only inflation relative to the source statement is the absolute
  constant `4`.
* `weighted_dRestricted_largeSieve`: the weighted bound `≤ ‖ρ‖_∞ (A + 4G²/d)∑|c|²`.

**Firewall.** The classical separated-frequency large sieve inequality itself is *not*
formalised in this repository.  It is carried as the explicit hypothesis `hLS` of
`weighted_dRestricted_largeSieve` and `fixedD_bound`; nothing here asserts it.

### §4 Coefficient energy — **PASS, implied constant `1`**

`OneLevelEnergy.coefficient_energy_bound`: if `E_g ≤ (gB + B²)L^{C_E}` then, with `G = dM`,

```
∑_{M ≤ m < 2M} E_{dm}/m²  ≤  dB(1 + B/G)·L^{C_E}.
```

The two auxiliary sums are proved here and are exactly the trivial ones,
`∑_{M ≤ m < 2M} 1/m ≤ 1` (`sum_inv_dyadic_le_one`) and `∑_{M ≤ m < 2M} 1/m² ≤ 1/M`
(`sum_inv_sq_dyadic_le`).  **No hidden logarithm.**  The energy hypothesis `E_g ≤ (gB+B²)L^{C_E}`
is an input, not a theorem of this repository.

### §5 Fixed-`d` bound — **PASS, all powers of `d` verified**

`OneLevelWeightedLS.fixedD_factor_identity`: `(A + 4G²/d)·(dK) = (Ad + 4G²)·K` exactly, so

```
G_{H,d} ≤ (A + 4G²/d)·dB(1+B/G)L^{C_E} = (Ad + 4G²)·B(1+B/G)L^{C_E}
```

(`fixedD_bound`, and `fixedD_bound_with_energy` with the §4 energy substituted verbatim).

### §6 Projector `S1`, `S2` — **PASS, conditional on the `Ω_H` pin**

`λ_H = μ * Ω_H` is the repository's own `SharedGcdGram.lambdaH`; Möbius inversion
`∑_{d ∣ m} λ_H(d) = Ω_H(m)` was already banked.

* `lambdaH_S1_pair_le` (exact factorisation, the load-bearing step):

  ```
  ∑_{d ≤ X} |λ_H(d)|/d  ≤  (∑_{e ≤ X}|Ω_H(e)|/e) · (∑_{k ≤ ⌊X/H⌋} |μ(k)|/k).
  ```

  The truncation of the inner Möbius sum at `⌊X/H⌋` is what produces `log(2G/H)` rather than
  `log G`, and it is obtained from the support of `Ω_H` alone.  **No assumption `d ~ H` is used
  anywhere**: `d` runs over all of `[1, X]`.
* `projector_S1_bound` / `projector_S1_bound_real`:
  `S1 ≤ c₁(1 + log⌊X/H⌋) ≤ c₁(1 + log(X/H))`, i.e. with `X = CG` the audited
  `S1 ≪ 1 + log(2G/H) ≪ L`.
* `projector_S2_bound`: `S2 ≤ 2c₁/H`.  The constant `2` comes from
  `∑_{k ≤ X} 1/k² ≤ 2` (`sum_inv_sq_Icc_le_two`, proved here) and the `1/H` from the support of
  `Ω_H` via the banked `omega_support_mass_le`.

**Firewall — Ω_H source normalisation: SOURCE PIN UNRESOLVED.**  The statements

```
supp Ω_H ⊆ {e ~ H},  |Ω_H(e)| ≪ 1,  ∑_e |Ω_H(e)|/e ≪ 1,  ∑_e |Ω_H(e)|/e² ≪ 1/H
```

do **not** occur as theorems anywhere in this repository — `lambdaH` is defined for an arbitrary
`Ω : ℕ → ℝ`.  They are therefore not promoted; they appear only as the hypotheses `hsupp`
(lower support) and `hmass` (`∑|Ω_H(e)|/e ≤ c₁`).  Note that the *upper* support constraint
`e < 2H` was never needed, and `|Ω_H| ≪ 1` was never needed either.

### §7 Global `Q_H` — **PASS, sharp form**

`OneLevelGlobal.global_QH_bound`, with `K = B(1+B/G)L^{C_E}` the §5 constant:

```
|Q_H|  ≤  K · ( A·c₁(1 + log⌊X/H⌋) + 8c₁·G²/H ).
```

`global_QH_envelope` gives the common-log form

```
|Q_H|  ≤  8c₁ · B(1+B/G) · (A + G²/H) · L^{C_E+1}.
```

### §8 Normalised ratio — **PASS, exact identity**

`OneLevelGlobal.normalised_ratio_identity`, with `X = AB`:

```
B(1+B/G)(A·L₁ + (G²/H)L₀) / (A B²)
  =  L₁/B  +  L₁/G  +  L₀G²/(HX)  +  L₀G/(HA).
```

This is an identity, not an inequality: each of the four terms is produced by exactly one of the
four products, so the four branches are independent, as claimed.

### §9 `B` and `G` source pins — **SOURCE PIN UNRESOLVED (both)**

No statement of the form `A ≥ X^{η_A}`, `B ≥ X^{η_B}` or `G > X^{1/2−η₀}` occurs anywhere in
this repository.  They are not manufactured here.

What *is* proved is the closure mechanism, unconditionally:

* `logPow_div_rpow_tendsto_zero` — `(log X)^K / X^η → 0` for every fixed `K ∈ ℕ`, `η > 0`;
* `logPow_div_le_of_polynomial_lower` — consequently, for every fixed `K` and every `ε > 0`,
  eventually in `X`: **if** `B ≥ X^η` then `L^K/B ≤ ε`.

So `L^{C_E+1}/B` beats every prescribed fixed logarithmic power *conditionally* on the pin, and
likewise for `G`.  The rows stay conditional.

### §10 True critical range — **PASS**

With `K_* = 6 + 2η + C_route` a fixed constant (the Lean statements are for an arbitrary fixed
natural `K`):

* `branch_G2_over_HX_closes` — `H ≥ (G²/X)L^{C_E+K}` ⟹ `L^{C_E}G²/(HX) ≤ L^{-K}`;
* `branch_G_over_HA_closes` — `H ≥ (G/A)L^{C_E+K}` ⟹ `L^{C_E}G/(HA) ≤ L^{-K}`;
* `critical_range_union` — above `max(G²/X, G/A)·L^{C_E+K}` both branches close.

Hence the unresolved union is `H ≤ L^{C_E+K_*}·max(G²/X, G/A)`, i.e. exponentially
`κ ≤ max(0, 2θ−1, θ−α) + o(1)`.

---

## 2. STRICT OUTPUT

```
SPACING:
    PASS   (unconditional; Lean: primitiveFraction_inj,
            spacing_lower_bound, spacing_uniform, primitiveFraction_separation)

WEIGHTED LARGE SIEVE:
    PASS   (reduction only; the classical separated-frequency inequality is an
            explicit hypothesis, not a theorem of this repository)
    exact factor = A + 4G²/d,  from δ = d/(4G²);  no log, no X^ε

COEFFICIENT ENERGY:
    PASS
    exact bound = ∑_{M≤m<2M} E_{dm}/m² ≤ dB(1 + B/G)L^{C_E},  constant 1

S1:
    PASS
    exact bound = ∑_{d≤X}|λ_H(d)|/d ≤ c₁(1 + log⌊X/H⌋) ≤ c₁(1 + log(X/H))
                = c₁(1 + log(2G/H)) for X = 2G;   no d ~ H assumption used

S2:
    PASS
    exact bound = ∑_{d≤X}|λ_H(d)|/d² ≤ 2c₁/H

OMEGA_H SOURCE NORMALISATION:
    SOURCE PIN   (not literally available; carried as hypotheses hsupp, hmass;
                  only the lower support and the e⁻¹ mass are ever used)

GLOBAL Q_H:
    PASS
    exact bound = |Q_H| ≤ B(1+B/G)L^{C_E}·( A c₁(1 + log⌊X/H⌋) + 8c₁G²/H )
    envelope    = |Q_H| ≤ 8c₁ B(1+B/G)(A + G²/H) L^{C_E+1}

NORMALISED RATIO:
    PASS (exact identity, X = AB)
    |Q_H|/(AB²) = L₁/B + L₁/G + L₀G²/(HX) + L₀G/(HA)
    all four terms checked independently

B POLYNOMIAL:
    SOURCE PIN

G POLYNOMIAL:
    SOURCE PIN

1/B:
    OPEN   (mechanism proved: L^K/B → 0 whenever B ≥ X^η, η > 0 fixed;
            the pin B ≥ X^{η_B} is not available, so SMALL-B is NOT banked closed)

1/G:
    OPEN   (same mechanism; the pin G > X^{1/2−η₀} is not available,
            so SMALL-G is NOT banked closed)

H-CRITICAL RANGE:
    H ≤ L^{C_E+K_*} · max( G²/X , G/A ),   K_* = 6 + 2η + C_route
    exponentially:  κ ≤ max(0, 2θ−1, θ−α) + o(1)

PROMOTED THEOREMS:
    DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45   : PASS  (exact, unconditional)
    DET1-ONELEVEL-dRESTRICTED-LS45              : PASS  (conditional reduction)
    DET1-ONELEVEL-COEFFENERGY45                 : PASS  (conditional on E_g input)
    DET1-ONELEVEL-PROJECTOR-S1S2-45             : PASS  (conditional on Ω_H pin)
    DET1-ONELEVEL-PRIMITIVEFRACTION-GLOBAL45    : PASS  (conditional on the above)
    SMALL-B OBSTRUCTION                         : NOT BANKED (source pin)
    SMALL-G OBSTRUCTION                         : NOT BANKED (source pin)
    ERDOS287 CLOSED                             : NOT BANKED

ERDOS287:
    OPEN

FIRST EXACT RESIDUAL:
    287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-PRIMITIVEFRACTION-CRITICAL45
    range: H ≤ L^{C_E+K_*} max(G²/X, G/A)
    retains: μ(m); primitive t mod dm; reciprocal-b source; friable a;
             exact signed λ_H(d)/d² projector.
```

---

## 3. Ledger

`Erdos287.PrimitiveFractionCaseBStatus.ledger` records the rows above;
`no_closed_rows`, `erdos287_open`, `source_pins_unresolved`,
`primitiveFractionCritical_is_first_exact_residual` and the five
`*_row_is_a_theorem` statements are kernel-checked, the last five binding each `PASS` row to the
literal statement it claims.  `historical_status_preserved` re-checks that the imported ONE-LEVEL
MÖBIUS and SHARED-`g₀` ledgers are unchanged and still contain no closed row.
