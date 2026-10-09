# Erdős #287 — Research Bank V22 report: explicit completed positive upper sieve

**Erdős #287 remains OPEN.** V22 constructs the new completed upper-sieve weight as an actual
mathematical object and kernel-proves its finite properties. The Rosser scalar asymptotic and the
prime-harmonic rounding estimate remain EXTERNAL PROVIDER interfaces.

Namespace `Erdos287.ResearchBankV22`. Aggregator `RequestProject/Erdos287/ResearchBankV22.lean`.

## Files

| File | Content |
|---|---|
| `PositiveSieveParameters.lean` | `vartheta = 273/500`, `rho = 1/10⁶`, `vartheta0 = 545999/10⁶`, `b_z = 501/1000`, `s0 = vartheta0/b_z`, `nu S = rho/S`, `R S = ⌊vartheta0/nu⌋`; `QuantifierOrder` (S → τ → x) |
| `ExceptionalPrimeSet.lean` | `excSet` (primes `≤ 2K+2`, primes of the base, slopes, nonzero slope differences), `P_E` — an AUXILIARY presieve, never moved into `W0` |
| `SmallPrimeUpperSieve.lean` | `SmallPrimeRosserProvider` (finite contract), `rosserBeta`, `rosserSmallProvider` (constructed, no axiom) |
| `RoundedRoughSieve.lean` | atom-set weights: `dsum`, `SupportedIn`, `OneBounded`, `Adm`, `ellW`, `roundedCond`, **`ellRd`** (`ℓ_rd`) |
| `FirstForbiddenPrefix.lean` | first-failed-prefix classification and positivity |
| `CompletedPositiveWeight.lean` | `conv`, `muE`, `completedWeight`, **`LambdaNewPlus`** `= μ_E ⋆ β_sm^+ ⋆ ℓ_rd` |
| `CellColouring.lean` | exact 3-colouring model, `G_i`, `piConst`, **exact colouring identity** |
| `IndependentFactorization.lean` | small primes into the first bin, bilinear source shape, literal-convolution firewall |
| `PackingRanges.lean` | `sigma`, `eta`, the four repaired margins |
| `RosserCostProvider.lean` | normalized cost `costU`, cost factorization, `RosserScalarProvider`, `PrimeHarmonicTupleProvider`, `completed_cost_bound` |
| `Ledger.lean` | `v22Ledger = v21Ledger ++ v22New` |
| `AxiomAudit.lean` | `#print axioms` for all 106 V22 theorems |

## Principal theorems

### LEAN BANK
- `FirstForbiddenPrefix.dsum_ellW_classification`, `dsum_ellW_ge`, `dsum_ellRd_ge`,
  `dsum_ellRd_nonneg` — `divisorSum(ℓ_rd, n) ≥ 1(no relevant rough prime divides n) ≥ 0`, proved by
  classification by the first failed prefix (`firstFail_odd`: it has odd index), nonnegative omitted
  correction, and Möbius tail `0` or `1` (`mobius_tail_zero_or_one`). Not imported as a provider.
- `CompletedPositiveWeight.dsum_completed_eq` — `S_Λ(n) = 1(gcd(n,P_E)=1) · S_β(n) · S_ℓ(n)` for
  disjoint universes; `LambdaNewPlus_nonneg`, `LambdaNewPlus_ge_survivor` (`S_Λ ≥ 0`,
  `S_Λ ≥ 1(n survives the whole auxiliary sieve)`); `natDivSum_LambdaNewPlus` (integer form);
  `completed_support_budget` (`P_E · x^rho · x^vartheta0 = P_E · x^vartheta`, `P_E` kept explicit).
- `SmallPrimeUpperSieve.rosserSmallProvider` — the small-prime Rosser weight (`β = 2` rule at level
  `x^rho`) satisfies the finite contract (`dsum ≥ 1(no small prime)`, `dsum ≥ 0`, level support):
  constructed, so the completed weight is LEAN BANK without a small-prime provider.
- `CellColouring.exact_colouring_identity` — `1(squarefree cell pattern) = π^{-1} E_ω[G₀⋆G₁⋆G₂]`
  with `π = ∏_j k_j!/(k_{j1}!k_{j2}!k_{j3}!) · 3^{-k_j}`; the expectation is a finite average of
  total mass one (`colouring_mass_one`); `piProb_inv_le`: `π^{-1} ≤ 3^R`. `G_zero_or_one`,
  `colourClass_disjoint`: the colour supports are disjoint, so the convolution never double counts a
  prime nor creates `p²`.
- `IndependentFactorization.beta_G0_oneBounded` (`|β_sm^+ ⋆ G₁| ≤ 1`, from disjoint smooth/rough
  support and one-boundedness), `coloured_weight_source_contract` (`Λ_ω = g ⋆ h`, `g, h`
  one-bounded, rough-supported second factor — proved from the collapse lemma, not from integer
  support), `colouring_factorization_identity`.
- `PackingRanges.repaired_margins` — `216791/209000000 > 0`, `13/2750 > 0`,
  `18038791/209000000 > 0`, `38938791/209000000 > 0`; `rho_genuine_power` — `x^rho → ∞`: rho is a
  genuine polynomial exponent, NOT `x^{o(1)}`; `completed_weight_independent_of_HB_length`.
  Caveat: the formulas producing the margins from (`rho`, `sigma`, `eta`) were not supplied; the
  margins are certified as given (positivity and exact relations `margin_relations`).
  Cell inflation is paid by the rounded endpoints inside `ℓ_rd`; the same weight does not depend on
  the Heath-Brown length `N`, only its valid representation (the allocation) may.
- `RosserCostProvider.costU_eq_normCost`, `costU_mono` (V21 monotonicity for the actual weights),
  `costU_conv` (costs multiply over disjoint universes), `thinLayer_length_le_R`, `CnuR_nonneg`
  (explicit constant `C_{nu,R} = vartheta0/3 · Σ_{k≤R} ⌈k/2⌉ nu^{-k} (b_z-nu)^{k-1}`).

### EXTERNAL PROVIDER (interfaces; never constructed)
- `RosserScalarProvider` — `DimensionOneDensity` (`h(p) = 1/p + O_K(1/p²)`, two-sided Mertens),
  `F(s) = 2e^γ/s` on `[1,3]`, `F(S) → 1`, small-prime cost `≤ F(S) + ε` and unrounded rough cost
  `≤ F(s0) + ε` eventually (`1 < s0 < 3`).
- `PrimeHarmonicTupleProvider` — rounding error `≤ C_{nu,R} τ + ε` eventually.

### LEAN CONDITIONAL
- `RosserCostProvider.completed_cost_bound` — in the order `S → τ → x`:
  `C_{β_sm^+ ⋆ ℓ_rd}(h) ≤ F(s0) + 1/10000 + ε` eventually, for every `ε > 0` (the `o(1)` is the
  explicit `ε`/eventual quantifier).

## Firewall
- **REPAIRED / RETIRED** — literal cell-indicator convolution:
  `literal_cell_convolution_multiplicity_two` (FINITE REGRESSION) `(1_C ⋆ 1_C)(143) = 2` for the
  cell `C = {11, 13}`; replaced by the exact colouring identity (`colour_convolution_le_one`).

## Trust
See the common trust section in `ERDOS287_RESEARCH_BANK_V24_REPORT.md`. V22: 106 theorems, all
depending only on `propext`, `Classical.choice`, `Quot.sound` (or a subset).
