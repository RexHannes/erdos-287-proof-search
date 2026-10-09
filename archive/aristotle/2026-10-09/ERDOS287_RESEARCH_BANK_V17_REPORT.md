# Erdős #287 — Research Bank V17 report: Route-C-thin consumer / uniform thinning

**Erdős #287 remains OPEN.** V17 claims no explicit threshold, no finite splice, no #287.

Namespace `Erdos287.ResearchBankV17`. Aggregator `RequestProject/Erdos287/ResearchBankV17.lean`.

Semantic classes used (exactly): **LEAN BANK**, **LEAN CONDITIONAL**, **EXTERNAL PROVIDER**,
**FINITE REGRESSION**, **OPEN**, **REPAIRED / RETIRED**.

## Files

| File | Content |
|---|---|
| `ResearchBankV17/ThinParameters.lean` | `δ = 1/40000`, `L = 41252000`, `K = 2^L`, `P = 12K`, `a = 28593810` |
| `ResearchBankV17/CorrectedLogP.lean` | `log P = (L+2) log 2 + log 3`; regression `L log 2 + log 3 = log(3K)` |
| `ResearchBankV17/ThinFunctionalCertificate.lean` | corrected functional certificate (namespace `ThinFunctional`), separate from arithmetic moments |
| `ResearchBankV17/UniformThinning.lean` | parameter family `L_δ`, `FunctionalThinningProvider`, quantifier order δ → tuple → x |
| `ResearchBankV17/ThinSupportLedger.lean` | support comparisons with 4/7, 7/12, 3/5; provider firewall |
| `ResearchBankV17/ThinConsumer.lean` | thin consumer (conditional) |
| `ResearchBankV17/ThinEffectivityFirewall.lean` | eventual ⟹ no explicit bound; effectivity firewall unchanged |
| `ResearchBankV17/Ledger.lean` | `v17Ledger` (V16 ledger as verbatim prefix) |
| `ResearchBankV17/AxiomAudit.lean` | `#print axioms` for all 35 V17 theorems |

## Classified results

### LEAN BANK
- `CorrectedLogP.log_twelve_pow` — for every `L`: `log(12·2^L) = (L+2) log 2 + log 3`;
  `logP_eq` for the fixed thin `P`.
- `CorrectedLogP.a_sub_logP_bounds` — `99 < a − log P < 101` (Mathlib's certified `log 2` bounds).
- `ThinParameters.L_mul_delta` (`Lδ = 10313/10`), `L_ge_threshold` (`Lδ log 2 ≥ 704`).
- `UniformThinning.Ldelta_spec`, `b_ge`, `a_gt_b` — for every `0 < δ ≤ 1/40000`,
  `L_δ = ⌈704/(δ log 2)⌉` satisfies `704 ≤ L_δ δ log 2`, `δ b ≥ 704`, `a = b + 120 > b`.
- `ThinFunctional.thin_margin_pos`, `toRouteC`, `certificate_does_not_give_moments` — the
  certificate implies the rational score margin; S0/S1 are **not** inferred from it.
- `ThinSupportLedger.thresholds_ordered`, `support_comparisons`, `thetaD_comparisons`
  (support arithmetic only).
- `Ledger.v17_preserves_v16_ledger`, `v17_erdos287_open`.

### LEAN CONDITIONAL
- `UniformThinning.uniform_thinning_conditional` — from `FunctionalThinningProvider`: for each
  fixed δ the fixed tuple has margins `≥ m₀ > 0`, and actual margins converging to them are
  eventually positive, with a threshold depending on δ. Quantifier order: **choose δ → construct
  fixed tuple → let x → ∞**.
- `ThinConsumer.thin_eventually_no_counterexample` — thin certificate + exact check + S0/S1
  contracts + (never constructed) `RouteCBaselineProvider` ⟹ eventual no-counterexample.
- `ThinConsumer.thin_margin_is_certified_input_dependent`.

### EXTERNAL PROVIDER
- `ThinFunctionalCertificate` (corrected strict bounds of the hostile repair, as certified data).
- `FunctionalThinningProvider` — the smallest isolation of the transcendental/integration layer.
- `ThinSupportLedger.PrimeDistributionProvider` — shape of an analytic prime-distribution input.

### FINITE REGRESSION
- Thin parameter record. `ThinConsumer.bad_bounds_fail_check`.
- `UniformThinning.no_uniform_x0` — countermodel `1 − 1/(δx)`: eventual positivity for each δ
  does not give one `x₀` uniform in δ.
- `ThinSupportLedger.thetaD_certificate` (instance `θ_d = 273/500`).

### OPEN
- `RouteCBaselineProvider` / thin pair baseline; explicit threshold; finite splice; #287.

### REPAIRED / RETIRED
- The old verifier formula `log P = L log 2 + log 3`: `CorrectedLogP.old_formula_is_log_3K`
  shows it equals `log(3K)`, `old_formula_ne_logP` shows it is not `log P` (gap exactly `2 log 2`,
  `logP_sub_old`). Only the corrected identity is banked.

## Firewalls
- `ThinSupportLedger.level_below_threshold_does_not_construct_provider`: level `< 3/5` does NOT
  construct a prime-distribution provider.
- `ThinEffectivityFirewall.eventual_gives_no_bound`, `v17_effectivity_firewall`.

## Caveats
- `L` is introduced with `irreducible_def` so that the kernel never tries to evaluate
  `2^41252000`; all statements about `K` are symbolic.
- The audited thin support exponent was not supplied; it is a parameter `θ` with certificate
  `θ < 4/7`, instantiated at `θ_d = 273/500`.
- The audited numerical bounds `μ_lo`, `W_hi`, `err` were not supplied; they are parameters.

## Trust
- 35 theorems; `#print axioms`: 32 × `[propext, Classical.choice, Quot.sound]`,
  1 × `[propext, Quot.sound]`, 2 × no axioms. No other axiom.
- No forbidden token (`sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `unsafe`,
  `implemented_by`, `opaque`, `skipKernelTC`, `Lean.trustCompiler`).
