# Erdős #287 — Research Bank V11 report (effective-constant handoff)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN.**

No numerical M_an is available in the current bank.

Unknown external constants are not numerical activation data.

The current finite architecture is OPEN.

The effective finite splice is BLOCKED.

Erdős #287 remains OPEN.

---

## 1. Files (append-only)

All files are new. No file from V2–V10, and no other pre-existing file, was modified.
`ARISTOTLE_SUMMARY.md` was not edited.

* `RequestProject/Erdos287/ResearchBankV11.lean` (aggregator)
* `RequestProject/Erdos287/ResearchBankV11/`
  `EffectiveConstants`, `PowerToLog`, `ExceptionalFactor`, `AnalyticActivation`,
  `FiniteArchitectureFrontier`, `EffectiveSplice`, `Ledger`, `AxiomAudit` (`.lean`)

The layout matches the suggested one. The only difference is that `AnalyticActivation.lean` also
holds the status predicates `EffectiveActivation` and `AsymptoticCompositionHolds`, and fixture 7.
Namespaces: `Erdos287.ResearchBankV11.<File>`. As in V10, files do not start with `module`,
because a `module` file cannot import the (non-module) V9/V10 files.

## 2. Build

| target | command | result |
|---|---|---|
| V11 (narrow) | `lake build RequestProject.Erdos287.ResearchBankV11` | success, **8186 jobs**, 0 errors, 0 warnings in V10/V11 files |
| full | `lake build` | success, **8681 jobs**, exit 0; 26 warning lines, all in pre-existing files, 0 in V10/V11 |

## 3. Axiom audit (§X)

`ResearchBankV11/AxiomAudit.lean` runs `#print axioms` on **all 45 V11 theorems**. Across them, the
union of reported axioms is `{propext, Classical.choice, Quot.sound}`; several rely on no axioms at
all. There is no `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler` and no custom axiom.
If V10 is included (215 theorems in total), the union is the same.

We scanned the new files for `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `bv_decide`,
`opaque`, `implemented_by` and `debug.skipKernelTC`. They appear only in comments/docstrings and in
the `#print axioms` commands. Only ordinary kernel `decide` is used, on the fixed finite ledger
lists and the killed-architecture list.

## 4. Principal theorems and semantic audit (§W)

### §Q Constants — `EffectiveConstants`, `PowerToLog`

* **`NumericalExternalConstants`**: a structure with fields `K_Kloosterman, K_GBV, K_BV, K_SW,
  K_divisor, K_smoothing, K_log`, the savings `η_*`, the log exponent `A₀`, the log-loss `C`, and
  positivity proofs. **No instance is provided anywhere.** `currentConstants : Option … := none`
  and `currentConstants_eq_none`.
* **`symbolicError c X = K_log·X·(log X)^(−A₀) + Σ_{i=1}^{6} K_i·X^{1−η_i}·(log X)^C`**. Only the
  definition is given.
* **`power_to_log`**
  Lean: `0<K → 0<η → 0<A → 0≤C → C+A+1 ≤ n → 0<X → 1 ≤ log X → K·n!/η^n ≤ log X →
  K * X^(1-η) * (log X)^C ≤ X * (log X)^(-A)`.
  Informal: the generic power-to-log conversion, with an explicit threshold on `log X`. The proof
  uses `X^η = e^{η log X} ≥ (η log X)^n / n!`. Equiv.: yes. It is a conservative sufficient
  condition and not an optimal threshold. External: none.
  `power_to_log_of_threshold` restates it with the single threshold `max 1 (K n!/η^n)`.

### §R `M_an` — `AnalyticActivation`

* `analyticActivation c A : Option ℕ := some ⌈exp(T)⌉₊`, where
  `T = max(1, max_i K_i n!/η_i^n)` and `n = ⌈C+A+1⌉₊`. The function is defined only for a supplied
  numerical bundle `c`; no numeral is hard-coded.
* **`analyticActivation_sufficient`**
  Lean: `0<A → A ≤ c.A₀ → analyticActivation c A = some M → (M:ℝ) ≤ X →
  c.symbolicError X ≤ (c.K_log + 6) * X * (log X)^(-A)`.
  Informal: once numerical constants are supplied, the computed threshold really does activate
  the log-power saving. Equiv.: yes, for the symbolic error function above. External: the constants
  themselves.
* **`current_M_an_eq_none`**: `current_M_an A = none` for every `A`, by `rfl`.
  `current_M_an A := currentConstants.bind (analyticActivation · A)`.
* **`effective_composition`**: from an `EffectiveProviderBundle` (external) *and* an
  `ExceptionalModulusInput` (§S), it gives `|Total X| ≤ (K_log+6)·X·(log X)^(−A)` for
  `X ≥ max(M, 2)`. The effective composition therefore depends visibly on the exceptional-modulus
  input.
* **`effectiveActivation_needs_constants`**: `EffectiveActivation → ∃ c, currentConstants = some c`.
  **`effectiveActivation_false`**: `¬ EffectiveActivation`.
* **`asymptotic_does_not_imply_effective`**:
  `¬ (AsymptoticCompositionHolds → EffectiveActivation)`. The asymptotic composition is inhabited
  (in the zero-error model), but effective activation is false in the current bank.
* **Fixture 7, `fixture_asymptotic_vs_effective`**: all five asymptotic providers (Zheng, smooth
  Type I, restored Type II, ordinary BV, SW seed) are inhabited, yet `currentConstants = none` and
  `∀ A, current_M_an A = none`.
* Does NOT prove: any numerical value of any constant, or any activation threshold for the actual
  #287 error terms.

### §S Exceptional modulus — `ExceptionalFactor`

* `ExceptionalSafeFullModulus q pExc Sep := (∀ p, pExc = some p → ¬ p ∣ q) ∨ Sep`. This says the
  exceptional prime is excluded from the **full** AP modulus `q`, or else a separate
  exceptional-character estimate `Sep` is supplied.
* `ExceptionalModulusInput` (external `Prop` structure): every full modulus in the family is safe.
* **`W_shortcut_invalid`**: if `p ∣ W`, then `¬ ExceptionalSafeFullModulus (W*r) (some p) False`.
  Putting the exceptional prime into `W` keeps it in the full modulus, so it does not solve the
  problem. **`W_shortcut_claim_false`** refutes the universal shortcut claim.
* `no_exceptional_safe`: with no exceptional prime, every modulus is safe.

### §T Finite architecture — `FiniteArchitectureFrontier`

* `ArchitectureTag` and `killedArchitectures` (prescribed CRT, small-graph/narrow-simplex, and the
  V9 scoped kills).
* **`FiniteArchitectureProvider arch c M_geom ai aj t : Prop`** has fields `notKilled`,
  `realization`, `primeSupply`, `rigidity`, `localization` and `activation (1/e < c)`. These are
  stated through the V9 `F`, `C` and `UsefulEdgeData` API. **No instance is constructed.**
* **`eventual_exclusion_of_architecture`**: the contract implies V9's
  `EventualNoCounterexampleFrom M_geom`, using the frozen V9 edge-supply theorem. So the contract
  is sufficient; it is not an empty placeholder.
* **`killed_architecture_no_provider`**: a killed tag cannot inhabit the contract.
  **`kills_are_scoped`**: some tag is not killed, so the kills are scoped and not universal.
  **`graph_existence_frozen`**: the V9 graph gates are re-exported verbatim.
* `currentArchitecture : Option ArchitectureRecord := none` and `currentArchitecture_eq_none`.

### §U Effective splice — `EffectiveSplice`

* **`EffectiveSpliceInput A`** contains: an `M_an` equal to `current_M_an A`, a recorded
  architecture (so `M_geom`), `M_int`, `M_rig`, `M_prime`, a verified finite endpoint `U`
  (V9 `FiniteVerifiedThrough U`), and `max(M_an, M_geom, M_int, M_rig, M_prime) ≤ U+1`.
* **`effectiveSplice_sound`**: a complete input bundle gives `Erdos287Closed` via the frozen V9
  splice, so the bundle is a genuine sufficient contract. It is never instantiated.
* **`splice_blocked_of_M_an_none`**, **`splice_blocked_of_no_architecture`**, and
  **`current_effective_splice_blocked`**: `IsEmpty (EffectiveSpliceInput A)` for every `A`.
* **`erdos287ClosedInBank_false`**, **`asymptotic_does_not_imply_closed`** and
  **`asymptotic_does_not_imply_finitePrimeSupply`**.
* **Fixture 8, `fixture_analytic_vs_finite`**: the asymptotic composition and all providers are
  inhabited, `currentArchitecture = none`, and `¬ Erdos287ClosedInBank`.
* Semantic caveat: `Erdos287ClosedInBank` means that *the current bank* contains a splice input.
  The non-implications are statements about the bank's contents. They are **not** a proof that
  #287 is false or unprovable. The real statement `Erdos287Closed` is never derived.

### Ledger — `Ledger`

* **`v11_preserves_v10_ledger`**: `v11Ledger.take v10Ledger.length = v10Ledger` and every V10 row
  is in V11. **`v11_preserves_v9_ledger`**: every V9 row is preserved with the same name, status
  and evidence.
* **`v11_no_reclassification`**: no new row renames an old row with a different status.
  **`v11_no_closed`**: no `CLOSED` row exists.
* **`v11_frontier`**: explicit numerical `M_an` is `NONE`; the viable finite architecture is
  `OPEN`; the effective finite splice is `BLOCKED`; the asymptotic composition is
  `REPAIRED/CONDITIONAL`; Erdős #287 is `OPEN`, and every #287 row is `OPEN`.
* **`no_ledger_path_closes_erdos287_v11`**: the closure-DAG fixpoint from the PROVED / EXACT PASS /
  FROZEN BANK rows never contains `Erdős #287`, `explicit numerical M_an` or
  `effective finite splice`.

Final status (as checked by `v11_frontier` and the V10 ledger):

| item | status |
|---|---|
| asymptotic composition | CONDITIONAL / formally composed from visible providers |
| M_an | NONE |
| finite architecture | OPEN |
| finite splice | BLOCKED |
| Erdős #287 | OPEN |

## 5. Regression fixtures

* 7. `AnalyticActivation.fixture_asymptotic_vs_effective`
* 8. `EffectiveSplice.fixture_analytic_vs_finite`
* also `ExceptionalFactor.W_shortcut_claim_false` and
  `FiniteArchitectureFrontier.killed_architecture_no_provider`.

## 6. Kernel re-check (§Y)

Lean 4.28 ships its checker as `leanchecker` (the successor to the external `lean4checker`).
It was run through `lake env` after the full build.

| command | module | exit | warnings |
|---|---|---|---|
| `lake env leanchecker RequestProject.Erdos287.ResearchBankV10` | V10 aggregator (+ imports) | 0 | none |
| `lake env leanchecker RequestProject.Erdos287.ResearchBankV11` | V11 aggregator (+ imports) | 0 | none |
| `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV11` | V11 aggregator; it transitively imports V10, so V10 is re-checked from scratch too | 0 | none (≈23–30 min wall time) |

## 7. What V11 does not prove

* No numerical value for any external constant, and hence no `M_an`.
* No finite architecture, prime supply, localization or rigidity at any scale.
* No analytic estimate. The providers stay external `Prop` structures, and no theorem constructs
  them from nothing. They are inhabited only in the zero-error test models used by the fixtures.
* **Erdős #287 remains OPEN.**
