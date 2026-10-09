# Erdős #287 — Research Bank V20 report: conditional asymptotic closure / final firewall

**Erdős #287 remains OPEN.** V20 proves only a CONDITIONAL asymptotic reduction. It gives no
explicit `M₀`, no finite splice, and no global #287 theorem.

Namespace `Erdos287.ResearchBankV20`. Aggregator `RequestProject/Erdos287/ResearchBankV20.lean`.

Semantic classes used (exactly): **LEAN BANK**, **LEAN CONDITIONAL**, **EXTERNAL PROVIDER**,
**FINITE REGRESSION**, **OPEN**, **REPAIRED / RETIRED**.

## Files

| File | Content |
|---|---|
| `ResearchBankV20/ThinPairBaseline.lean` | `ThinPairBaselineBound` (= V16 `RouteCBaselineProvider` contract), `PairDecompositionProvider` |
| `ResearchBankV20/ConditionalThinPairTheorem.lean` | `thinPairBaseline_of_providers_CONDITIONAL` |
| `ResearchBankV20/ConditionalAsymptotic287.lean` | `conditional_asymptotic_287_of_baseline`, `conditional_asymptotic_287_CONDITIONAL` |
| `ResearchBankV20/NoEffectivization.lean` | no explicit `M₀` from an eventual statement; splice needs `M₀` |
| `ResearchBankV20/ScopeFirewalls.lean` | the eight required non-implications |
| `ResearchBankV20/Status.lean` | `v20Ledger`, `v20_final_status` |
| `ResearchBankV20/AxiomAudit.lean` | `#print axioms` for all 23 V20 theorems |

## Principal theorems

### LEAN CONDITIONAL
- `ConditionalThinPairTheorem.thinPairBaseline_of_providers_CONDITIONAL`:

      PairDecompositionProvider τ W N branches          (frozen standard analytic provider)
      + LocalTransportBounds branches                   (V18/V19 local transport output)
      + ActualCenteredSourceCompositionProvider branches N (A_C·W_F + 90 + err)   (OPEN)
      ⟹ ThinPairBaselineBound τ W N W_F err.

  Proof: `Pair/N = Σ principal + (Σ err)/N`; `principalRecombination` bounds the principal sum;
  `|Σ err| ≤ Σ localBound ≤ ηN` eventually (`localControl`). **Not a proved pair theorem.**
- `ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline` — V14/V15 S0/S1 contracts +
  V16/V17 thin consumer (certificate + margin check; the V14 compiler/harmonic infrastructure is
  inside the V16 consumer) + `ThinPairBaselineBound` ⟹ `∃ M₀, ∀ M ≥ M₀, NoCounterexampleAt M`.
- `ConditionalAsymptotic287.conditional_asymptotic_287_CONDITIONAL` — the same from all explicit
  providers, including the never-constructed composition provider.

### LEAN BANK
- `ConditionalThinPairTheorem.err_sum_le`; `ThinPairBaseline.thinPairBaselineBound_iff`,
  `decomposition_provider_falsifiable`.
- `NoEffectivization.conditional_asymptotic_gives_no_explicit_M0`, `splice_needs_explicit_M0`
  (positive direction: explicit `M_an ≤ U + 1` + finite exclusion to `U` closes; negative
  direction: without a threshold the splice fails), `v20_effectivity_status`.
- `ScopeFirewalls` (all countermodels machine-checked), bundled in `v20_scope_firewalls`:
  1. `omega_zero_not_compatibility` — `Ω(0) = 1` does NOT imply zero-mode compatibility;
  2. `residue_restriction_breaks_balance` — one-bounded residue restriction does NOT preserve a
     Siegel–Walfisz-type balance (toy mod-2 model: `1` is balanced, its restriction to even `n`
     is not; `const_one_balanced`);
  3. `support_below_threshold_no_provider` — support exponent `< 3/5` does NOT construct the prime
     provider;
  4. `local_transport_not_branch_match` — local transport bounds hold for a branch list on which
     the composition provider fails;
  5. `local_margins_not_global_control` — positive E1/E2 margins coexist with uncontrolled outer
     conductor/root sums;
  6. `finite_verifier_not_analytic` — an error vanishing on all of `x ≤ 100` still violates the
     analytic prime-distribution provider;
  7. `conditional_asymptotic_no_explicit_M0` — the conditional asymptotic theorem does NOT give
     an explicit `M₀`;
  8. `explicit_M0_required_for_splice` — an explicit `M₀` is required before the finite splice
     can close global #287.
- `Status.v20_preserves_v19_ledger`, `v20_final_status`, `v20_erdos287_open`,
  `v20_composition_provider_not_proved`.

### EXTERNAL PROVIDER
- `PairDecompositionProvider` (Heath-Brown identity + dispersion bookkeeping, as an exact branch
  decomposition of the weighted pair count). Frozen V15 providers (BV, S0/S1 main terms, divisor
  moments) as before.

### OPEN
- `ActualCenteredSourceCompositionProvider` — defined in V19, never constructed.
- `ThinPairBaselineBound` itself (only conditional). Explicit `M₀`. Finite splice. Erdős #287.

### REPAIRED / RETIRED
- None new in V20 (V19 retirements are carried in the ledger).

## Final status (machine-checked in `Status.v20_final_status`)

| Item | Class |
|---|---|
| V14/V15 infrastructure | LEAN BANK |
| Route-C graph / score / contact infrastructure | LEAN BANK |
| Route-C conditional implication | LEAN CONDITIONAL |
| Route-C-thin corrected functional consumer | LEAN CONDITIONAL (certified-input dependent) |
| Reciprocal colour algebra (finite algebra) | LEAN BANK |
| Zero-frequency compatibility | LEAN BANK |
| Prime-power / nonunit CRT reduction | LEAN BANK |
| Periodic E1 reduction | LEAN CONDITIONAL (complete-sum provider) |
| E2 outer-multiplier scope theorem | LEAN BANK |
| Outer exponent ledger | LEAN BANK |
| PairDecompositionProvider | EXTERNAL PROVIDER |
| ActualCenteredSourceCompositionProvider | OPEN — DEFINED, NEVER CONSTRUCTED |
| Thin pair theorem | LEAN CONDITIONAL (on that provider) |
| Asymptotic Erdős #287 | LEAN CONDITIONAL only |
| Explicit M₀ | OPEN |
| Finite splice | OPEN |
| Global Erdős #287 | OPEN |

## Validation / trust (V16–V20)

### Build commands
```
lake build RequestProject.Erdos287.ResearchBankV16 RequestProject.Erdos287.ResearchBankV17 \
  RequestProject.Erdos287.ResearchBankV18 RequestProject.Erdos287.ResearchBankV19 \
  RequestProject.Erdos287.ResearchBankV20          # narrow targets incl. all AxiomAudit modules
lake build                                          # full: "Build completed successfully (8798 jobs)."
lake env lean RequestProject/Erdos287/ResearchBankV{16..20}/AxiomAudit.lean   # axiom output
```
Both builds succeed; the V16–V20 files build with no errors and no warnings.

### `#print axioms` summary (every theorem of V16–V20)

| Bank | Theorems | `[propext, Classical.choice, Quot.sound]` | `[propext, Quot.sound]` | `[propext]` | none |
|---|---|---|---|---|---|
| V16 | 86 | 77 | 3 | 4 | 2 |
| V17 | 35 | 32 | 1 | 0 | 2 |
| V18 | 55 | 49 | 2 | 1 | 3 |
| V19 | 66 | 55 | 5 | 1 | 5 |
| V20 | 23 | 17 | 2 | 0 | 4 |
| **Total** | **265** | 230 | 13 | 6 | 16 |

No other axiom appears (in particular no `sorryAx`, no `Lean.ofReduceBool`, no
`Lean.trustCompiler`, no custom axiom).

### Forbidden tokens
`rg "sorry|admit|^axiom|native_decide|bv_decide|unsafe|implemented_by|skipKernelTC|trustCompiler|opaque"`
over all V16–V20 files: no occurrence in code (the only hit is the English word "admits" inside
a docstring of `ResearchBankV18/PostCenteringTransfer.lean`).

### External checker
Installed binary: `leanchecker` (from the Lean toolchain; `lean4checker` is **not** installed and
was not used). Commands run:
```
lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV16
lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV17
lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV18
lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV19
lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV20
```
Results (run in parallel, fresh re-check of every declaration in the transitive import closure,
including Mathlib and V2–V15):

| Module | leanchecker exit | wall time |
|---|---|---|
| `RequestProject.Erdos287.ResearchBankV16` | 0 | 2421 s |
| `RequestProject.Erdos287.ResearchBankV17` | 0 | 2429 s |
| `RequestProject.Erdos287.ResearchBankV18` | 0 | 2392 s |
| `RequestProject.Erdos287.ResearchBankV19` | 0 | 2458 s |
| `RequestProject.Erdos287.ResearchBankV20` | 0 | 2453 s |

No output, no errors.

### Comparator
`lake comparator` → `error: unknown command 'comparator'`; no `comparator` binary on `PATH`.
**Comparator: not installed.** No challenge file was run and nothing was emulated.

### Module system
The new files use ordinary (non-`module`) Lean headers, matching the V2–V15 banks they import;
mixing module and non-module files in this import graph was avoided.

## Git / append-only audit
- Base commit: `f0dc239` ("Initial commit").
- `git diff --name-status f0dc239 HEAD`: 62 lines, all `A` (added); 0 `M`, 0 `D`, 0 `R`.
- Modified files: **none**. Deleted files: **none**. V2–V15 sources and `ARISTOTLE_SUMMARY.md`
  are untouched. No historical theorem was weakened or strengthened; no withdrawn claim is
  reintroduced as a bank theorem (withdrawn claims appear only as counterexamples /
  REPAIRED / RETIRED rows).

### Added files
```
A	ERDOS287_RESEARCH_BANK_V16_REPORT.md
A	ERDOS287_RESEARCH_BANK_V17_REPORT.md
A	ERDOS287_RESEARCH_BANK_V18_REPORT.md
A	ERDOS287_RESEARCH_BANK_V19_REPORT.md
A	ERDOS287_RESEARCH_BANK_V20_REPORT.md
A	RequestProject/Erdos287/ResearchBankV16.lean
A	RequestProject/Erdos287/ResearchBankV16/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV16/BalancedBlowup26.lean
A	RequestProject/Erdos287/ResearchBankV16/ConditionalRouteCImplication.lean
A	RequestProject/Erdos287/ResearchBankV16/ContactLocalizationC.lean
A	RequestProject/Erdos287/ResearchBankV16/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV16/MacroGraph26.lean
A	RequestProject/Erdos287/ResearchBankV16/RelaxedPairBudget.lean
A	RequestProject/Erdos287/ResearchBankV16/RouteCConsumer.lean
A	RequestProject/Erdos287/ResearchBankV16/RouteCParameters.lean
A	RequestProject/Erdos287/ResearchBankV16/ScopeFirewalls.lean
A	RequestProject/Erdos287/ResearchBankV16/Score26.lean
A	RequestProject/Erdos287/ResearchBankV17.lean
A	RequestProject/Erdos287/ResearchBankV17/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV17/CorrectedLogP.lean
A	RequestProject/Erdos287/ResearchBankV17/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV17/ThinConsumer.lean
A	RequestProject/Erdos287/ResearchBankV17/ThinEffectivityFirewall.lean
A	RequestProject/Erdos287/ResearchBankV17/ThinFunctionalCertificate.lean
A	RequestProject/Erdos287/ResearchBankV17/ThinParameters.lean
A	RequestProject/Erdos287/ResearchBankV17/ThinSupportLedger.lean
A	RequestProject/Erdos287/ResearchBankV17/UniformThinning.lean
A	RequestProject/Erdos287/ResearchBankV18.lean
A	RequestProject/Erdos287/ResearchBankV18/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV18/CharacterExpansion.lean
A	RequestProject/Erdos287/ResearchBankV18/ColourConductor.lean
A	RequestProject/Erdos287/ResearchBankV18/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV18/NegativeControls.lean
A	RequestProject/Erdos287/ResearchBankV18/PostCenteringTransfer.lean
A	RequestProject/Erdos287/ResearchBankV18/ProviderInterfaces.lean
A	RequestProject/Erdos287/ResearchBankV18/ReciprocalMonomial.lean
A	RequestProject/Erdos287/ResearchBankV18/ScalarVariation.lean
A	RequestProject/Erdos287/ResearchBankV19.lean
A	RequestProject/Erdos287/ResearchBankV19/ActualBranchData.lean
A	RequestProject/Erdos287/ResearchBankV19/ActualCenteredCompositionProvider.lean
A	RequestProject/Erdos287/ResearchBankV19/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV19/CoherentRoots.lean
A	RequestProject/Erdos287/ResearchBankV19/E1PeriodicProvider.lean
A	RequestProject/Erdos287/ResearchBankV19/E2OuterMultiplier.lean
A	RequestProject/Erdos287/ResearchBankV19/HBBranchTaxonomy.lean
A	RequestProject/Erdos287/ResearchBankV19/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV19/NegativeControls.lean
A	RequestProject/Erdos287/ResearchBankV19/NonunitReduction.lean
A	RequestProject/Erdos287/ResearchBankV19/OuterCostLedger.lean
A	RequestProject/Erdos287/ResearchBankV19/OverlapConductor.lean
A	RequestProject/Erdos287/ResearchBankV19/PeriodicReciprocalCompletion.lean
A	RequestProject/Erdos287/ResearchBankV19/PrimePowerCRT.lean
A	RequestProject/Erdos287/ResearchBankV19/RootClassGram.lean
A	RequestProject/Erdos287/ResearchBankV19/ZeroFrequencyCompatibility.lean
A	RequestProject/Erdos287/ResearchBankV20.lean
A	RequestProject/Erdos287/ResearchBankV20/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV20/ConditionalAsymptotic287.lean
A	RequestProject/Erdos287/ResearchBankV20/ConditionalThinPairTheorem.lean
A	RequestProject/Erdos287/ResearchBankV20/NoEffectivization.lean
A	RequestProject/Erdos287/ResearchBankV20/ScopeFirewalls.lean
A	RequestProject/Erdos287/ResearchBankV20/Status.lean
A	RequestProject/Erdos287/ResearchBankV20/ThinPairBaseline.lean
```

### Theorem counts
V16: 86 · V17: 35 · V18: 55 · V19: 66 · V20: 23 (total 265).
