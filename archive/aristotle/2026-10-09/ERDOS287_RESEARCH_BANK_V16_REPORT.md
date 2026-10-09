# Erdős #287 — Research Bank V16 report: generic Route-C consumer

**Erdős #287 remains OPEN.** Nothing in V16 claims #287, an explicit threshold, or a finite splice.

Namespace `Erdos287.ResearchBankV16`. Aggregator `RequestProject/Erdos287/ResearchBankV16.lean`.
Append-only: V2–V15 and `ARISTOTLE_SUMMARY.md` were not modified (see the V20 report for the
git audit).

Semantic classes used (exactly): **LEAN BANK**, **LEAN CONDITIONAL**, **EXTERNAL PROVIDER**,
**FINITE REGRESSION**, **OPEN**, **REPAIRED / RETIRED**.

## Files

| File | Content |
|---|---|
| `ResearchBankV16/MacroGraph26.lean` | `G(26,7)`, α = 7, proper 4-colouring, 8 occupied ⟹ edge |
| `ResearchBankV16/BalancedBlowup26.lean` | symbolic balanced blow-up over `Fin K` (never enumerated) |
| `ResearchBankV16/Score26.lean` | score `f(v) = v − C(v,2)/99`, bound 350, nonnegative-weight extraction |
| `ResearchBankV16/RouteCParameters.lean` | fixed Route-C instance, `RouteCFunctionalCertificate`, margin check |
| `ResearchBankV16/ContactLocalizationC.lean` | `c_C = 46/125`, `c_C > 1/e`, `c_C R_C < 1`, harmonic two-hole at `c_C` |
| `ResearchBankV16/RouteCConsumer.lean` | Route-C deterministic consumer (tuple, window, score identity, contradiction) |
| `ResearchBankV16/RelaxedPairBudget.lean` | relaxed baseline `A_C W_F + 90 + err + o(1)` with explicit ε/eventual quantifiers |
| `ResearchBankV16/ConditionalRouteCImplication.lean` | `RouteCBaselineProvider`, conditional eventual no-counterexample |
| `ResearchBankV16/ScopeFirewalls.lean` | Route-B constants not imported, certificate ≠ moments, effectivity unchanged |
| `ResearchBankV16/Ledger.lean` | `SemClass` (the six classes), `RowV16`, `v16Ledger` (V15 ledger embedded verbatim) |
| `ResearchBankV16/AxiomAudit.lean` | `#print axioms` for all 86 V16 theorems |

## Classified results

### LEAN BANK
- `MacroGraph26.indep_card_le_seven`, `alpha_eq_seven` — α(G(26,7)) = 7 by the general argument
  (translate so the set contains 0, offsets lie in `[−6,6]`, pairwise offsets differ by ≤ 6 ⟹ one
  7-point arc). No subset enumeration.
- `MacroGraph26.col4_proper` — the colouring `{0..6},{7..13},{14..20},{21..25}` is proper.
- `MacroGraph26.occupied_eight_forces_edge`, `BalancedBlowup26.blowup_occupied_eight_forces_edge`
  — ≥ 8 occupied macro-groups ⟹ an occupied (blow-up) edge. `groupSize_K` uses `K ≡ 12 (mod 26)`
  (`RouteCParameters.K_mod_26`), proved symbolically; `K = 2^82650` is never evaluated.
- `Score26.fifty_sub_f` — `50 − f(v) = (v−99)(v−100)/198` in ℚ; `f_le_fifty`,
  `score_le_350_of_seven`, `eight_occupied_of_score_gt`.
- `Score26.exists_gt_of_weighted_pos` — positive weighted mean ⟹ a point with score > 350,
  **with nonnegative weights as an explicit hypothesis**.
- `RouteCParameters.A_C_eq_two_div_theta_add_xi` — `A_C = 1000273/273000 = 2/θ_d + ξ`.
- `ContactLocalizationC.cC_gt_inv_e` (`46/125 > 1/e`, via Mathlib's certified bound on `e`),
  `RC_lt`, `cC_mul_RC_lt_one`, `cC_mul_RC_buffer_lt_one`, `contact_coeff_ratio_C`,
  `two_hole_contradiction_cC` (re-proved natively at `c_C`; `cC_lt_c_routeB` shows the V14
  statement at `37/100` cannot be reused).
- `RouteCConsumer.window_good`, `score_identity`, `pair_contradiction`,
  `no_counterexample_of_good_t` — the deterministic consumer.
- `RelaxedPairBudget.relaxed_score_positive`, `eta_choice`, `eventual_score_positive`,
  `baseline_form` — rational/real implication; `A_* W_F < 187` (Route B) is not used.
- `Ledger.v16_preserves_v15_ledger`, `v16_erdos287_open`, `v16_provider_open`.

### LEAN CONDITIONAL
- `RouteCParameters.routeC_margin_of_certificate`, `routeC_margin_pos` — from a
  `RouteCFunctionalCertificate` + the exact rational `RouteCMarginCheck`.
- `ConditionalRouteCImplication.routeC_eventually_no_counterexample` — S0/S1 contracts (V14/V15)
  + `RouteCBaselineProvider` + functional certificate + margin check ⟹ `∃ M₀, ∀ M ≥ M₀`, no
  counterexample with maximum `M`. Asymptotic only.

### EXTERNAL PROVIDER
- `RouteCFunctionalCertificate` (bounds `μ_F > μ_lo`, `W_F < W_hi`): the high-dimensional
  functional integrals are **not** formalized; they enter only as certified input.

### FINITE REGRESSION
- Parameter record `K = 2^82650`, `P = 12K`, `a = 57384`, `δ = 1/80`, `θ_d = 273/500`,
  `ξ = 1/1000`, `A_C = 1000273/273000`.
- `ContactLocalizationC.routeB_c_fails_with_RC`, `routeB_buffer_fails`,
  `ScopeFirewalls.routeB_constants_not_imported` — Route-B `c = 37/100` and buffer `1001/1000`
  fail the Route-C inequality. `Score26.signed_weights_fail` — signed weights break extraction.

### OPEN
- `RouteCBaselineProvider` — defined, never constructed (`baseline_provider_falsifiable`,
  `ScopeFirewalls.baseline_provider_not_vacuous` show it is a genuine proposition).
- Explicit analytic threshold; finite splice; Erdős #287.

### REPAIRED / RETIRED
- Silent import of the Route-B constants (`c = 37/100`, `A_* W_F < 187`, buffer `1001/1000`) into
  Route C: retired; Route C uses only its own constants.

## Caveats (reconstructions)
- The audited numerical value of `R_C` was not supplied. `R_C = ((19+2ξ)/(7−2ξ))·ρ_C²` with
  `ρ_C = 10001/10000` is reconstructed from the 26-group geometry (adjacent groups satisfy
  `7 ≤ s − r ≤ 19`, `adj_oriented_range`). All constants are visible definitions.
- The audited values of `μ_lo`, `W_hi`, `err` were not supplied; they are parameters and
  `RouteCMarginCheck` is a decidable rational inequality to be discharged by `norm_num` once
  supplied.

## Trust
- 86 theorems; `#print axioms`: 77 × `[propext, Classical.choice, Quot.sound]`,
  3 × `[propext, Quot.sound]`, 4 × `[propext]`, 2 × no axioms. No other axiom.
- No `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `unsafe`, `implemented_by`,
  `opaque`, `skipKernelTC`, `Lean.trustCompiler` in V16.
- Files use ordinary (non-`module`) Lean headers, matching the existing V2–V15 banks they import.
