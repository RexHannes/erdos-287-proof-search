# ERDŐS 287 — HYBRID-2 / CRITICAL-RECTANGLE SAFE BANK REPORT

**Append-only delta.**  No previously proved theorem was altered, weakened or removed.  No
source firewall was replaced.  The only change to a pre-existing file is seven new `import`
lines in `RequestProject/Main.lean`.

**Erdős #287 is NOT claimed.**  Nothing here proves Erdős #287, Twin Prime, or any downstream
theorem.

---

## 1. Files added

| File | Content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287Hybrid2Arithmetic.lean` | §3 Möbius `ℓ`-opening, §4 reciprocal cancellation + unit propagation, §5 conductor gcd algebra, §6 `g₀g₀'` divisibility |
| `RequestProject/CurrentProgramme/Erdos287Hybrid2AnalyticCompiler.lean` | §7 fixed-`ℓ` bound (explicit-hypothesis style), §8 exact harmonic `ℓ`-sum compiler |
| `RequestProject/CurrentProgramme/Erdos287Hybrid2CriticalRectangle.lean` | §9 `η₁` compiler, §11 long-edge rectangle algebra, §12 top-shell comparability (partial) |
| `RequestProject/CurrentProgramme/Erdos287Hybrid2ShortEdgeFirewall.lean` | §10 short-edge firewall: exact pigeonhole + explicit predicates + counterexample |
| `RequestProject/CurrentProgramme/Erdos287BDiagonalProductMod.lean` | §14 b-diagonal product-modulus bank |
| `RequestProject/Status/CurrentStatusErdos287Hybrid2Frontier.lean` | §15 frontier ledger |
| `RequestProject/Status/AxiomAuditErdos287Hybrid2.lean` | §16 `#print axioms` for every new declaration |
| `ERDOS287_HYBRID2_CRITICALRECT_SAFE_BANK_REPORT.md` | this report |

## 2. Imports appended

Appended verbatim to the end of the import block of `RequestProject/Main.lean` (nothing removed,
nothing reordered):

```
import RequestProject.CurrentProgramme.Erdos287Hybrid2Arithmetic
import RequestProject.CurrentProgramme.Erdos287Hybrid2AnalyticCompiler
import RequestProject.CurrentProgramme.Erdos287Hybrid2CriticalRectangle
import RequestProject.CurrentProgramme.Erdos287Hybrid2ShortEdgeFirewall
import RequestProject.CurrentProgramme.Erdos287BDiagonalProductMod
import RequestProject.Status.CurrentStatusErdos287Hybrid2Frontier
import RequestProject.Status.AxiomAuditErdos287Hybrid2
```

## 2a. Reuse survey (§1 of the brief)

Existing repository material was searched before anything was written, and reused where a
literal theorem existed:

| Needed | Found in repository / Mathlib | Action |
|---|---|---|
| squarefree Möbius multiplicativity | `Erdos287.LevelPairProduct.moebius_levelPair_compress`, `…_eq_moebius_n`; `ArithmeticFunction.isMultiplicative_moebius` | reused / re-exported (`bdiag_moebius_levelPair`); **not** duplicated |
| modular inverses (literal `q ∣ c·x − 1` convention) | `Erdos287.SharedG0UnitSectorGcd.isCoprime_of_inverse`, `Erdos287.LevelPairReciprocal.global_inverse_restricts` | same convention adopted (`IsInverseMod`) |
| coprimality cancellation | `IsCoprime.dvd_of_dvd_mul_left`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd` (Mathlib) | reused |
| additive large sieve / separated frequencies | `Erdos287.OneLevel*` carry it **as a hypothesis `hLS` only**; no literal separated-frequency large sieve exists in the repository | carried as explicit hypothesis, **not** fabricated |
| finite-interval Cauchy–Schwarz | not present in the shape Hybrid 2 needs | folded into the explicit hypothesis `hArch` |
| harmonic sums | `harmonic_le_one_add_log` (Mathlib), `Erdos287.harmonic_eq_sum_Icc`, `Erdos287.OneLevelProjector.sum_abs_moebius_div_le` | reused (exact bound, no `O(log)`) |
| divisor sums / dyadic cardinalities | `Erdos287.OneLevelProjector.sum_inv_sq_Icc_le` etc. | available, not needed by this delta |
| logarithmic bounds | `Real.log_le_log` (Mathlib) | reused |
| rpow / exponent compilers | `Erdos287.CaseBReproof.rpow_max_eq`, `kappa_le_of_critical_range` | present; the Hybrid-2 exponent consequence was **not** built on them (see §12 below) |
| CRT phase algebra | `Erdos287.NormalForm3221.phase`, `phase_congr`, `Erdos287.LevelPairReciprocal.reciprocal_normalForm_of_inverse` | reused as the base of `bdiag_phase_product_modulus` |

## 3. Unconditional arithmetic theorems

All statements below are kernel-checked with **no** analytic hypothesis and **no** source pin.

### §3  Möbius `ℓ`-opening — `Erdos287Hybrid2Arithmetic.lean`

* `Erdos287.Hybrid2.mobius_opening_of_squarefree` —
  `Squarefree m₁ → m₁ = ℓ·u → Squarefree ℓ ∧ Squarefree u ∧ Coprime ℓ u ∧ μ(m₁) = μ(ℓ)μ(u) ∧ μ(m₁)μ(ℓ) = μ(u)`.
  Stated in the repository's Möbius type `ArithmeticFunction.moebius : ArithmeticFunction ℤ`,
  cast to `ℤ`, matching the existing convention.
* `Erdos287.Hybrid2.mobius_opening_needs_squarefree` — counterguard: the identity
  `μ(m₁)μ(ℓ) = μ(u)` is **false** in the unrestricted generality (`ℓ = 4, u = 1`).  So §3 is not
  banked in a mathematically false ambient generality.

### §4  Reciprocal cancellation and unit propagation

* `Erdos287.Hybrid2.IsInverseMod` (definition) — `Q ∣ c·x − 1`; no inverse is postulated.
* `Erdos287.Hybrid2.isCoprime_of_isInverseMod`
* `Erdos287.Hybrid2.coprime_left_of_mul_coprime`, `…coprime_right_of_mul_coprime`,
  `…coprime_both_of_mul_coprime` — `Coprime (ℓu) Q → Coprime ℓ Q ∧ Coprime u Q` (`ℕ`).
* `Erdos287.Hybrid2.isCoprime_both_of_mul_isCoprime` — the `ℤ` form.
* `Erdos287.Hybrid2.reciprocal_cancel_common_factor` —
  `m₁ = ℓu`, `Δ = ℓv`, `x` inverse of `m₁ mod Q`, `y` inverse of `u mod Q`, `Coprime u Q`
  ⟹ `Q ∣ Δ·a·x − v·a·y`.  Purely modular; no asymptotic notation.
  *Minimality note*: `Coprime ℓ Q` is **not** carried as a hypothesis because it is implied by
  the existence of `x` — this is proved separately as
  `Erdos287.Hybrid2.isCoprime_ell_of_inverse`.

### §5  Exact conductor data

* `Erdos287.Hybrid2.baseConductor_gcd` —
  `Coprime C₁ m₂ → gcd(a₁₂ᵇᵃˢᵉ,C₁) = de₁c₂ → gcd(a₁₂ᵇᵃˢᵉ,m₂) = d₂ → gcd(a₁₂ᵇᵃˢᵉ, C₁m₂) = de₁c₂d₂`.
* `Erdos287.Hybrid2.fullConductor_gcd` — with `a₁₂ = Δ·a₁₂ᵇᵃˢᵉ` and `Coprime Δ a₁₂ᵇᵃˢᵉ`,
  `gcd(a₁₂, C₁m₂) = gcd(Δ,C₁)·gcd(Δ,m₂)·(de₁c₂d₂)`.
* `Erdos287.Hybrid2.fullConductor_needs_coprime` — counterguard showing
  `Coprime Δ a₁₂ᵇᵃˢᵉ` is necessary (`Δ = a = 2, C₁ = 2, m₂ = 1`: `2 ≠ 4`).

**Option chosen for the source gcd identities: B.**  The two literal identities
`gcd(a₁₂ᵇᵃˢᵉ,C₁) = de₁c₂` and `gcd(a₁₂ᵇᵃˢᵉ,m₂) = d₂` are *not* formalised from their elementary
congruences (those congruences are not present in this repository); they are exposed as explicit
hypotheses `h1`, `h2` of the compiler.  **No source identity is encoded as an axiom.**

### §6  `g₀g₀' ∣ e·(b₂−b₁)`

* `Erdos287.Hybrid2.pairwise_factors_dvd` — `a·c₁·d₁·c₂·d₂ ∣ D_b` under the ten pairwise
  coprimalities and the five divisibilities.
* `Erdos287.Hybrid2.lcm_dvd_e` — `lcm(a₁,a₂) ∣ e`.
* `Erdos287.Hybrid2.mul_eq_gcd_mul_lcm` — `a₁a₂ = gcd·lcm`.
* `Erdos287.Hybrid2.g0_mul_g0prime_dvd_e_mul_difference` —
  `(a₁c₂d₂)·(a₂c₁d₁) ∣ e·D_b`, with `a = gcd(a₁,a₂)`.
* `Erdos287.Hybrid2.g0_mul_g0prime_does_not_divide_difference` — the stronger claim
  `g₀g₀' ∣ (b₂−b₁)` is **FALSE** and is explicitly refuted
  (`a₁ = a₂ = 2, e = D_b = 2, c₁ = d₁ = c₂ = d₂ = 1`: `4 ∣ 4` but `4 ∤ 2`).
  It was **not** formalised.

### §8  Harmonic `ℓ`-sum (unconditional, exact)

* `Erdos287.Hybrid2.sum_inv_Icc_le_one_add_log` — `∑_{k=1}^{n} 1/k ≤ 1 + log n`.
* `Erdos287.Hybrid2.ell_sum_harmonic` —
  `(∀ ℓ ∈ Icc 1 n, B_ℓ ≤ C/ℓ) → ∑_{ℓ ∈ Icc 1 n} B_ℓ ≤ C(1 + log n)`.
* `Erdos287.Hybrid2.ell_sum_harmonic_two_min` — the `n = min(D,M₁)` form with the source's
  `1 + log(2·min(D,M₁))`.  Floor/`Nat` coercions are explicit.
  **No asymptotic `O(log)` theorem is used.**

### §9, §11, §12  Real algebra (unconditional)

* `Erdos287.Hybrid2.eta1` (definition), `eta1_nonneg`
* `Erdos287.Hybrid2.eta_sq_expand` —
  `η₁² = C_arch²L_ℓ²(1/D + 1/M₁ + 1/Q + Q/(DM₁))`.
* `Erdos287.Hybrid2.rectangle_side1`, `rectangle_side2`, `rectangle_product`,
  `rectangle_intersection` — see §6 of this report.
* `Erdos287.Hybrid2.topShell_e_lower_bound` — see §12 of this report.

### §10  Short-edge firewall (unconditional)

* `Erdos287.Hybrid2.noncontraction_shortEdge_or_rectangle`, `hybrid2_survivor_union`,
  `rectangle_alone_does_not_capture_all_survivors`, `shortD_is_not_automatic`.

### §14  b-diagonal exact algebra (unconditional)

* `Erdos287.BDiagonal.isCoprime_of_dvd_mul_sub_one`
* `Erdos287.BDiagonal.bdiag_crt_inverse_congr` — `x₁m₂ + x₂m₁ ≡ z (mod m₁m₂)`.
* `Erdos287.BDiagonal.bdiag_phase_product_modulus` — the CRT phase combination
  `e_{m₁}(X(2ebm₂)⁻¹)·e_{m₂}(X(2ebm₁)⁻¹) = e_{m₁m₂}(X(2eb)⁻¹)` in
  `Erdos287.NormalForm3221.phase`.
* `Erdos287.BDiagonal.bdiag_moebius_mul` — `μ(m₁)μ(m₂) = μ(n)`, `n = m₁m₂`, `Coprime m₁ m₂`.
* `Erdos287.BDiagonal.bdiag_moebius_levelPair` — re-export of the banked shared-`g₀` version.
* `Erdos287.BDiagonal.bdiag_squarefree_split` — squarefree support version.
* `Erdos287.BDiagonal.reducedConductor` (definition), `bdiag_reduced_conductor`,
  `bdiag_reduced_unit` — `d_c = (N,e)`, `q_c = 2eb/d_c`, `d_c·q_c = 2eb`,
  `Coprime (N/d_c) (e/d_c)`, and unit propagation to the reduced modulus.

## 4. Analytic CONDITIONAL theorems and EVERY explicit hypothesis

Nothing in this section is unconditional.  Every hypothesis is a **theorem hypothesis**, never
an axiom, and none of them appears in any `#print axioms` output.

### `Erdos287.Hybrid2.fixedEll_bound`  (§7)

Positivity: `0 < ℓ`, `0 < D`, `0 < Q`, `0 < M₁`, `0 ≤ C_arch`.

| Name | Statement |
|---|---|
| `hArch` | `Bell ≤ Carch * Real.sqrt Sell` — Archimedean reciprocal factor admits a separated packet expansion with total coefficient mass `≤ Carch` (Cauchy–Schwarz already applied) |
| `hPacket` | `Pell ≤ L1^2 / (ell * M1)` — packet `L²` mass `∑_u |c_ℓ(u)|²` |
| `hLS` | `Sell ≤ (D/ell + Q) * (1 + M1/(ell*Q)) * Pell` — separated reciprocal frequencies with spacing `1/Q` |

Conclusion (fixed-`ℓ` estimate, verbatim):
`Bell ≤ Carch * sqrt( (D/ℓ + Q)(1 + M₁/(ℓQ)) · L₁²/(ℓM₁) )`.

*No equivalent literal theorem exists in the repository, so `hLS` is passed, not instantiated.*

### `Erdos287.Hybrid2.hybrid2_bound`  (§9)

Positivity: `0 < D`, `0 < M₁`, `0 < Q`, `0 ≤ Carch`, `0 ≤ Lell`.

| Name | Statement |
|---|---|
| `hArch` | `Btot ^ 2 ≤ Carch ^ 2 * Etot` |
| `hPacket` | `Etot ≤ Lell ^ 2 * Wsep` |
| `hLS` | `Wsep ≤ 1/D + 1/M1 + 1/Q + Q/(D*M1)` |

Conclusion: `Btot ≤ eta1 Carch Lell D M1 Q`.  The theorem is **not** labelled unconditional.

### `Erdos287.BDiagonal.bdiag_delta_contraction_conditional`  (§14)

The claimed b-diagonal `Δ`-large-sieve contraction is **not** banked as unconditional.  Its
analytic inputs are exposed exactly as above, under the names `hArchB`, `hPacketB`, `hLSB`.

## 5. Short-edge firewall status

`Erdos287.Hybrid2.noncontraction_shortEdge_or_rectangle` (unconditional, explicit constants):

> `0 < D`, `0 < M`, `0 < Q`, and `1 ≤ C²L²(1/D + 1/M + 1/Q + Q/(DM))`
> ⟹ `D ≤ 4C²L² ∨ M ≤ 4C²L² ∨ Q ≤ 4C²L² ∨ DM ≤ 4C²L²Q`.

`C_short = 4`, `C_rect = 4` (four terms, pigeonhole).  This is the exact finite-sum inequality;
the informal "either a short edge or the rectangle" is **not** relied on anywhere.

Predicates: `ShortD`, `ShortM`, `ShortQ`, `LongEdgeRectangle`, and the survivor predicate
`Hybrid2Survivor`.  Union theorem: `Erdos287.Hybrid2.hybrid2_survivor_union`.

**Ledger nodes and their status** (`Erdos287.Hybrid2FrontierStatus.hybrid2Ledger`):

| Node | Label |
|---|---|
| `Hybrid2ShortD` | `conditionalOpen` — **FORMALISED OPEN** |
| `Hybrid2ShortM` | `conditionalOpen` — **FORMALISED OPEN** |
| `Hybrid2ShortQ` | `conditionalOpen` — **FORMALISED OPEN** |
| `Hybrid2LongEdgeTwoSidedRectangle` | `conditionalOpen` |
| `BDiagonalDeltaProductModRectangle` | `conditionalOpen` |

No separate closure proof for any short edge was supplied by the audit, and none is invented
here, so all three short-edge nodes are marked **OPEN**.

`Erdos287.Hybrid2.rectangle_alone_does_not_capture_all_survivors` (and its status wrapper
`Erdos287.Hybrid2FrontierStatus.hybrid2_longEdge_pass_does_not_capture_survivors`) proves that
`LongEdgeRectangle PASS` does **not** imply that all Hybrid-2 survivors lie in the rectangle:
`C = L = 1`, `D = 1`, `M = 100`, `Q = 1` is a survivor with `DM = 100 > 4 = 4C²L²Q`.

## 6. Long-edge rectangle theorem

* `Erdos287.Hybrid2.rectangle_side1` — from `D·M₁ ≤ L²Q₁°`, `M₁ = G/(e r₁)`, `Q₁° = BG/g₀`
  (all positive): `r₁ ≥ g₀D/(eBL²)`.
* `Erdos287.Hybrid2.rectangle_side2` — the symmetric side with `g₀'`, `M₂`, `r₂`, `Q₂°`.
* `Erdos287.Hybrid2.rectangle_product` — `r₁r₂ ≥ g₀g₀'D²/(e²B²L₁²L₂²)`.
* `Erdos287.Hybrid2.rectangle_intersection` — under `r₁r₂ < R_aff`:
  `D < eBL₁L₂·sqrt(R_aff/(g₀g₀'))`.

All positivity hypotheses are explicit; the derivation is division-safe (no `x/0` shortcut).

**Status: FORMALISED PASS** (as an algebraic compiler).  The ledger node
`Hybrid2LongEdgeTwoSidedRectangle` remains `conditionalOpen`, because its analytic input is
conditional and the short edges are open.

## 7. `g₀g₀'` divisibility theorem

`Erdos287.Hybrid2.g0_mul_g0prime_dvd_e_mul_difference` : **FORMALISED PASS**.

The stronger `g₀g₀' ∣ (b₂−b₁)` was **not** formalised; it is explicitly refuted by
`Erdos287.Hybrid2.g0_mul_g0prime_does_not_divide_difference`.

## 8. b-diagonal algebra bank

**FORMALISED PARTIAL.**

* Exact algebraic collapse: `bdiag_crt_inverse_congr`, `bdiag_phase_product_modulus` — PASS.
* `n = m₁m₂` and `μ(m₁)μ(m₂) = μ(n)`: `bdiag_moebius_mul`, `bdiag_squarefree_split`,
  `bdiag_moebius_levelPair` — PASS.
* gcd reduction `d_c = (N,e)`, `q_c = 2eb/d_c`, reduced modular conductor and its unit
  condition: `bdiag_reduced_conductor`, `bdiag_reduced_unit` — PASS.
* `Δ`-large-sieve contraction — **NOT unconditional**; exposed with explicit hypotheses
  (`bdiag_delta_contraction_conditional`).  Ledger node `BDiagonalDeltaProductModRectangle`
  is `conditionalOpen`.

## 9. §12 top-shell exponent compiler

* `Erdos287.Hybrid2.topShell_e_lower_bound` — **FORMALISED** (comparability constants explicit):
  from `c₀·G²/(Ae) ≤ D` and `AB ≤ c₂X`, `e ≥ c₀G²B/(c₂XD)`.
* The exponent-level consequence
  `κ ≥ θ − 1/2 − ρ_aff/4 + (γ₀+γ₀')/4 − o(1)`: **NOT YET FORMALISED**.  It needs a source-exact
  dictionary between `κ, θ, ρ_aff, γ₀, γ₀'` and the scales, which is not present in this
  repository; no such dictionary was manufactured.  The arithmetic / analytic compiler bank is
  not blocked on it.

## 10. Source pins unchanged

```
Omega_H normalisation:  SOURCE PIN   (unchanged)
B polynomial margin:    SOURCE PIN   (unchanged)
G polynomial margin:    SOURCE PIN   (unchanged)
Erdős #287:             OPEN         (unchanged)
```

Machine-checked preservation of the earlier ledgers:
`Erdos287.Hybrid2FrontierStatus.caseB_ledger_still_preserved`,
`Erdos287.Hybrid2FrontierStatus.primitiveFraction_ledger_still_preserved`.

## 11. Frontier ledger (§15)

`RequestProject/Status/CurrentStatusErdos287Hybrid2Frontier.lean`.

FORMAL SOURCE FIRST RESIDUAL: `SharedGcdOmegaHNormalizationSourcePin` (label `sourcePin`,
stage 0, unique — `omegaNormalization_is_formal_first_residual`).

CONDITIONAL-ON-NORMALIZED-OMEGA analytic descendants, all `conditionalOpen`:
`Hybrid2ShortD`, `Hybrid2ShortM`, `Hybrid2ShortQ`, `Hybrid2LongEdgeTwoSidedRectangle`,
`BDiagonalDeltaProductModRectangle`.

Ledger theorems: `caseB_strictly_before_hybrid2_frontier`,
`primitiveFractionCritical_not_frontier`, `omegaNormalization_is_formal_first_residual`,
`hybrid2_analytic_descendants_all_open`,
`hybrid2_longEdge_passedThrough_only_if_appropriate`, `erdos287_open`,
`only_arithmetic_rows_are_unconditional`, `hybrid2_survivor_union`,
`hybrid2_longEdge_pass_does_not_capture_survivors`, `caseB_ledger_still_preserved`,
`primitiveFraction_ledger_still_preserved`.

No node is asserted closed merely because its structural reduction has been formalised.

## 12. `#print axioms` output (§16)

Verbatim from the full build of `RequestProject/Status/AxiomAuditErdos287Hybrid2.lean`:

```
'Erdos287.Hybrid2.mobius_opening_of_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.mobius_opening_needs_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.coprime_left_of_mul_coprime' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.coprime_right_of_mul_coprime' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.coprime_both_of_mul_coprime' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.isCoprime_both_of_mul_isCoprime' depends on axioms: [propext]
'Erdos287.Hybrid2.isCoprime_of_isInverseMod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.reciprocal_cancel_common_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.isCoprime_ell_of_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.baseConductor_gcd' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.fullConductor_gcd' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.fullConductor_needs_coprime' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.pairwise_factors_dvd' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.lcm_dvd_e' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.mul_eq_gcd_mul_lcm' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.g0_mul_g0prime_dvd_e_mul_difference' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.g0_mul_g0prime_does_not_divide_difference' depends on axioms: [propext, Quot.sound]
'Erdos287.Hybrid2.fixedEll_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.sum_inv_Icc_le_one_add_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.ell_sum_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.ell_sum_harmonic_two_min' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.eta1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.eta_sq_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.eta1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.hybrid2_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.rectangle_side1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.rectangle_side2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.rectangle_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.rectangle_intersection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.topShell_e_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.Hybrid2Survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.ShortD' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.ShortM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.ShortQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.LongEdgeRectangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.noncontraction_shortEdge_or_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.hybrid2_survivor_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.rectangle_alone_does_not_capture_all_survivors' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2.shortD_is_not_automatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.isCoprime_of_dvd_mul_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.bdiag_crt_inverse_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.bdiag_phase_product_modulus' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.bdiag_moebius_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.bdiag_moebius_levelPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.bdiag_squarefree_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.reducedConductor' does not depend on any axioms
'Erdos287.BDiagonal.bdiag_reduced_conductor' depends on axioms: [propext, Quot.sound]
'Erdos287.BDiagonal.bdiag_reduced_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.bdiag_delta_contraction_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.BDiagonal.bdiag_survivor_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2FrontierStatus.stage' does not depend on any axioms
'Erdos287.Hybrid2FrontierStatus.hybrid2Ledger' does not depend on any axioms
'Erdos287.Hybrid2FrontierStatus.caseB_strictly_before_hybrid2_frontier' does not depend on any axioms
'Erdos287.Hybrid2FrontierStatus.primitiveFractionCritical_not_frontier' does not depend on any axioms
'Erdos287.Hybrid2FrontierStatus.omegaNormalization_is_formal_first_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2FrontierStatus.hybrid2_analytic_descendants_all_open' does not depend on any axioms
'Erdos287.Hybrid2FrontierStatus.hybrid2_longEdge_passedThrough_only_if_appropriate' does not depend on any axioms
'Erdos287.Hybrid2FrontierStatus.erdos287_open' does not depend on any axioms
'Erdos287.Hybrid2FrontierStatus.only_arithmetic_rows_are_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2FrontierStatus.hybrid2_survivor_union' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2FrontierStatus.hybrid2_longEdge_pass_does_not_capture_survivors' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2FrontierStatus.caseB_ledger_still_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos287.Hybrid2FrontierStatus.primitiveFraction_ledger_still_preserved' does not depend on any axioms```

Every dependency lies in `{propext, Classical.choice, Quot.sound}`; several rows depend on no
axioms at all.  **No new custom axiom was introduced.**  The explicit theorem hypotheses
(`hArch`, `hPacket`, `hLS`, `hArchB`, `hPacketB`, `hLSB`, `h1`, `h2`) are hypotheses, not
axioms, and do not appear above.

## 13. Static unsafe-token audit (§17)

Search over the seven new files for `sorry`, `axiom`, `unsafe`, `native_decide`, `opaque`,
`implemented_by`:

```
sorry          : 0 occurrences in code (1 prose mention in the audit docstring)
admit          : 0 occurrences in code (2 prose uses of the English word "admits")
axiom          : 0 declarations (only `#print axioms` commands and prose)
unsafe         : 0 occurrences in code (1 prose mention)
native_decide  : 0 occurrences in code (1 prose mention)
opaque         : 0 occurrences in code (1 prose mention)
implemented_by : 0 occurrences in code (1 prose mention)
```

There is no unsafe escape hatch.  All decidable facts are discharged with `decide +kernel`.

## 14. Full-build result (§18)

```
lake build            (default target `RequestProject`)
Build completed successfully (8279 jobs).
exit status 0, 0 errors
```

The full default target — every previously banked module included — rebuilds cleanly.

---

```
ERDOS287:
    OPEN.

FORMAL FIRST RESIDUAL:
    OMEGA_H NORMALISATION SOURCE PIN.

CONDITIONAL ANALYTIC FRONTIER:
    Hybrid2ShortD  ∪  Hybrid2ShortM  ∪  Hybrid2ShortQ
      ∪  Hybrid2LongEdgeTwoSidedRectangle
      ∪  BDiagonalDeltaProductModRectangle.
```

No claim is made that Erdős #287, Twin Prime, or any downstream theorem is proved.
