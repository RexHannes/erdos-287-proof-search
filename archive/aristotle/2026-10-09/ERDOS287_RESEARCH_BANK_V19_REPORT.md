# Erdős #287 — Research Bank V19 report: final-composition repair

**Erdős #287 remains OPEN.** `ActualCenteredSourceCompositionProvider` is **OPEN — DEFINED, NEVER
CONSTRUCTED**.

Namespace `Erdos287.ResearchBankV19`. Aggregator `RequestProject/Erdos287/ResearchBankV19.lean`.
This version follows the latest final-composition audit as supplied in the request: every claim
that the audit repaired or withdrew appears only as a counterexample / REPAIRED / RETIRED row.

Semantic classes used (exactly): **LEAN BANK**, **LEAN CONDITIONAL**, **EXTERNAL PROVIDER**,
**FINITE REGRESSION**, **OPEN**, **REPAIRED / RETIRED**.

## Files

| File | Content |
|---|---|
| `ZeroFrequencyCompatibility.lean` | compatibility, `kappa`, CRT existence/uniqueness, exact count |
| `CoherentRoots.lean` | coherent root packets, zero-mode equivalence (same assignment) |
| `RootClassGram.lean` | root-class Gram identity |
| `PrimePowerCRT.lean` | `gcd(D₁,s₁) = 1`, CRT phase reduction, conductor divisibility |
| `NonunitReduction.lean` | nonunit coefficient congruence |
| `OverlapConductor.lean` | overlap / prime-power conductor |
| `PeriodicReciprocalCompletion.lean` | periodic completion identity, `CompleteKloostermanProvider` |
| `E1PeriodicProvider.lean` | `E1PeriodicProvider` (namespace `E1Periodic`), conductor ≠ period |
| `E2OuterMultiplier.lean` | Cauchy-stage outer / own-variable multiplier absorption |
| `OuterCostLedger.lean` | square-root halving, unweighted conductor sums, margins |
| `HBBranchTaxonomy.lean` | structural HB taxonomy |
| `ActualBranchData.lean` | `ActualBranchData` record (namespace `BranchData`) |
| `ActualCenteredCompositionProvider.lean` | the sole remaining provider; `LocalTransportBounds` |
| `NegativeControls.lean` | bundle `v19_negative_controls` |
| `Ledger.lean`, `AxiomAudit.lean` | ledger; `#print axioms` for all 66 V19 theorems |

(All under `RequestProject/Erdos287/ResearchBankV19/`.)

## Classified results

### LEAN BANK
- **Zero-frequency compatibility**: `compat_necessary` (`a₁n₂ ≡ a₂n₁ (mod g)` for any common
  solution), `kappa`, `crt_exists`, `crt_unique`, `zero_frequency_count` — under the unit
  hypotheses the number of `m ∈ [0, L)` solving both congruences is exactly `κ`.
- **Coherent roots**: `coherent_zero_mode` — for ONE coherent assignment used by BOTH copies,
  `a(q₁)n₂ ≡ a(q₂)n₁ (mod g) ↔ n₁ ≡ n₂ (mod g)`.
- **Root-class Gram**: `all_characters`, `principal_term`, `root_class_gram` —
  `Σ_{j,k} z_j z̄_k (1_{r_j=r_k} − 1/φ(g)) = (1/φ(g)) Σ_{χ≠χ₀} |Σ_j z_j χ(r_j)|²`.
- **Prime powers / nonunit CRT**: `coprime_D1_s1`, `lcm_eq`, `crt_phase_reduction`
  (`e_[D,s](hΔ) = e_{D₁}(h c s̄₁)` for all positive `D, s`), `period_of_dvd`, `leastPeriod_dvd`,
  `conductor_dvd` (primitive conductor divides `D₁/gcd(D₁,c)`), `overlap_conductor_dvd`,
  `prime_power_overlap`; `NonunitReduction.no_solution_of_not_dvd`, `reduce_iff`,
  `reduced_coprime`, `reduced_unit_solution`.
- **Periodic completion identity**: `completion`, `completion_bound`, `Fper_apply`.
- `E1Periodic.coeff_periodic`.
- **E2 scope**: `cauchy_outer_absorb`, `cauchy_outer_unimodular`, `h_multiplier_absorb`.
- **Outer-cost ledger**: `sqrt_saving` (saving `x^{−σ}` ↦ `x^{−σ/2}`),
  `unweighted_divisor_sum_ge`, `exponent_after_unweighted_sum` (conservative exponent
  `ε/2 − δ(2+p)`), `E1_margin` (`17/40000 > 0`), `E2_margin` (`13/30000 > 0`) — LOCAL savings only.
- **HB taxonomy**: `three_large_impossible`, `three_large_impossible_mul`, `large_count_le_two`,
  `typeII_partial_sum`, `taxonomy_complete`.
- `ActualBranchData` record and predicates `CoherentPacket`, `E1Valid`, `E2InScope` (definitions).
- `ActualCenteredCompositionProvider.provider_falsifiable` — the provider is a genuine
  proposition.

### LEAN CONDITIONAL
- `PeriodicReciprocalCompletion.periodic_completion_bound` — from `CompleteKloostermanProvider`.
- `E1Periodic.e1_bound` — from `E1PeriodicProvider` (whose contract names the actual period `V`).

### EXTERNAL PROVIDER
- `CompleteKloostermanProvider` — complete-sum (Weil/Ramanujan) bound; not in Mathlib, never an
  axiom.
- `E1PeriodicProvider` — source-level E1 contract incl. the actual period `V`.

### FINITE REGRESSION
- `PrimePowerCRT.prime_power_fixture` (`D = 8`, `s = 12`), `OverlapConductor.overlap_fixture`
  (`D = 27`, `s = 9`), `E1Periodic.conductor_not_period`.

### OPEN
- **`ActualCenteredSourceCompositionProvider`** — fields exactly: `zeroMode` (coherent packet or
  root-class Gram), `e1` (valid period `V`), `e2` (outer/own-variable scope), `localControl` and
  `outerControl` (global control in the same normalization, eventually for every `η > 0`),
  `principalRecombination` (signed principal terms recombine legally). **Never constructed.**
- That actual branches satisfy any of these predicates.

### REPAIRED / RETIRED
- "`Ω(0) = 1` ⟹ zero-frequency main term unchanged": `omega_zero_does_not_fix_main_term`
  (counterexample `q₁ = q₂ = 3`, `n₁ = n₂ = 1`, `a₁ = 1`, `a₂ = 2`: phase 1, count 0).
- Independent-copy root assignments: `independent_copies_fail` (`q₁ = 3`, `q₂ = 6`, `a ≡ 1`,
  `a' ≡ 2`).
- Identifying conductor `E` with period `V`: `conductor_not_period`.
- Arbitrary joint `q/h` dependence covered: `joint_dependence_not_covered`,
  `inner_dependent_outer_fails`.
- "σ survives the square root": `sigma_not_preserved`.
- "Fixed `J` makes `Σ_{D≤Y} τ_J(D)` polylogarithmic": `not_polylog`,
  `unweighted_divisor_sum_not_polylog`.

## Caveats
- The `(ε, δ, p)` triples `(1/1000, 1/40000, 1)` (E1) and `(1/1000, 1/40000, 2/3)` (E2) were not
  supplied; they are a reconstruction reproducing exactly the supplied margins `17/40000` and
  `13/30000`.
- The CRT factorization of the complete sum into a Kloosterman sum times `ω̂` is not formalized;
  the provider bounds the complete sum directly.

## Trust
- 66 theorems; `#print axioms`: 55 × `[propext, Classical.choice, Quot.sound]`,
  5 × `[propext, Quot.sound]`, 1 × `[propext]`, 5 × no axioms. No other axiom.
- No forbidden token.
