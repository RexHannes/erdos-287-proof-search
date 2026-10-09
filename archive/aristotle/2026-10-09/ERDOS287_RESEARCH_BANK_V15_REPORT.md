# Erdős #287 — Research Bank V15: fixed-source moment interface

INTERNAL #287 RESEARCH PROGRAMME ONLY. **Erdős #287 remains OPEN. Nothing here claims it.**

Mode: append-only; namespace `Erdos287.ResearchBankV15.*`. See also
`ERDOS287_RESEARCH_BANK_V14_REPORT.md`.

## Files

```
RequestProject/Erdos287/ResearchBankV15.lean                  (aggregator)
RequestProject/Erdos287/ResearchBankV15/FixedAffineSource.lean
RequestProject/Erdos287/ResearchBankV15/DerivativeKernel.lean
RequestProject/Erdos287/ResearchBankV15/MobiusCoefficients.lean
RequestProject/Erdos287/ResearchBankV15/CompleteLCMModulus.lean
RequestProject/Erdos287/ResearchBankV15/CRTResidues.lean
RequestProject/Erdos287/ResearchBankV15/CollisionLocalFactors.lean
RequestProject/Erdos287/ResearchBankV15/DivisorMultiplicity.lean      (B8)
RequestProject/Erdos287/ResearchBankV15/Normalization.lean
RequestProject/Erdos287/ResearchBankV15/BombieriVinogradovProvider.lean
RequestProject/Erdos287/ResearchBankV15/ZerothMomentContract.lean
RequestProject/Erdos287/ResearchBankV15/FirstMomentContract.lean
RequestProject/Erdos287/ResearchBankV15/PairProvider.lean
RequestProject/Erdos287/ResearchBankV15/OneLemmaReduction.lean
RequestProject/Erdos287/ResearchBankV15/ScopeFirewalls.lean
RequestProject/Erdos287/ResearchBankV15/Ledger.lean
RequestProject/Erdos287/ResearchBankV15/AxiomAudit.lean
```

## Content

| § | declarations | status |
|---|---|---|
| B1 | `FixedAffineSource.tuple` (= V14 `compilerTuple`, one fixed constant), `L i t = a_i t + 1`, `fixed_admissible` | proved. No quantification over compiler outputs. |
| B2 | `DerivativeKernel.KernelPair`, `DerivativeRelation` (`(-1)^K ∂_1…∂_K G = F` via one-variable `deriv` slices), `DerivativeKernelProvider`, `fixture_relation`, `fixture_G_ne_F`, `identify_G_with_F_fails` | relation recorded; multivariate analysis is the explicit provider; `G ≠ F` regression. |
| B3 | `MobiusCoefficients.lam` = `(∏ μ(d_i)) G(log d_i / log X)` if `(∏ d_i, W0) = 1`, `lam_smul`, `shared_primes_allowed` | no pairwise coprimality imposed. |
| B4 | `CompleteLCMModulus.completeModulus` (`lcm(d_1..d_K, e_1..e_K)`), `shared_primes_once`, `fixture_lcm_vs_product`, `firstMomentModulus` (`a_i W0 q`), `firstMoment_modulus_ne_q` | proved. |
| B5 | `CRTResidues.Solves`, `solves_periodic`, `solves_unique_mod`, `solves_of_compatible`, `crtResidue`, `crtResidue_spec`, `residue_moves_with_tuple` | finite CRT consistency proved; residue depends on the tuple. |
| B6 | `CollisionLocalFactors.nu`, `localFactor` (`(1 − ν_p/p)/(1 − 1/p)^K`), `nu_le_card`, `nu_good`, `localFactor_good`, `collision_only_at_differences` | local algebra proved; the global moment is **not** inferred from the origin value (it is the `S0MainTermProvider`). |
| B7 | `BombieriVinogradovProvider.OrdinaryBVProvider` | explicit structure (maximal over reduced residue choices); not an axiom, never constructed. |
| B8 | `DivisorMultiplicity.pairMultiplicity`, `sum_group_by_modulus`, `sum_pairMultiplicity`, `abs_sum_le_multiplicity`, `multiplicity_fixture` (9 pairs for `q = 6`) | finite grouping proved; no pointwise polylog claim; analytic divisor moment is `DivisorMomentProvider`. |
| B9 | `Normalization.NX = C_X · S_W0(a) · I`, `weight` (physical, `≥ 0`), `normalization_scale_invariant`, `omitting_I_breaks_invariance` | proved (regression with `c = 2`). |
| B10 | `ZerothMomentContract.weighted_expansion`, `S0_expansion`, `hit_periodic` (period `W0 · q`), `periodic_count_abs`, `count_error`, `S0_error_bound`, `S0MainTermProvider`, `DivisorMomentProvider`, **`s0_contract`**; `FirstMomentContract.S1_expansion`, `L_modEq` (modulus `a_i W0 q`), `mainS1`, `S1_split`, `BVTransfer` (a function of `OrdinaryBVProvider`), `S1MainTermProvider`, **`s1_contract (bv : OrdinaryBVProvider) …`** | ε/eventual form: `∀ η > 0, ∃ M₀, ∀ M ≥ M₀, 0 < N_X ∧ |S0/N_X − 1| ≤ η` and `μ_F − η ≤ S1/N_X`. Conditional on the named providers only; square expansion, periodic counting and error bound are exact finite algebra. |
| B11 | `PairProvider.ActualWeightedColouredPairProvider src WF`, `toV14`, `ofV14`, `pair_expansion` | defined on the same tuple / weight / window / `N_X`; **never constructed**. |
| B12 | `OneLemmaReduction.StandardProviders`, **`one_lemma_reduction`**, `open_content_concentrated`, `contracts_of_providers` | `OrdinaryBVProvider + StandardProviders + ActualWeightedColouredPairProvider ⇒ ∃ M₀, ∀ M ≥ M₀, NoCounterexampleAt M`. |
| C | `ScopeFirewalls.pascadiNotes`, `provider_fails_degenerate`, `exponent_fact_does_not_construct_provider`, `residue_is_root_dependent`, `v15_effectivity_firewall` | `0.624 < 5/8` is true but does **not** imply the provider (degenerate data with `N_X ≡ 0`, `W_F = −1000` refutes the universal provider). |
| D | `Ledger.v15Ledger`, `v15_preserves_v14_ledger`, `v15_final_status`, `v15_erdos287_open`, `v15_pair_provider_open`, `v15_no_open_item_promoted` | final ledger below. |

"One-lemma reduction" means exactly one remaining **new** asymptotic provider in this
architecture. It does not mean the provider is known or follows from Pascadi.

## Final ledger

```
ResearchBankV12:                          BANK
ResearchBankV13:                          BANK
Balanced functional score:                BANK
11-cell compiler existence:               LEAN BANK / theorem application (edge-only theorem proved in V14)
Compiler useful-height bound:             OPEN (not needed for asymptotic existence)
Contact annulus:                          LEAN BANK
Useful consecutive identity:              LEAN BANK, orientation fixed
Row rigidity:                             LEAN BANK
Conditional source-to-#287 implication:   LEAN BANK
Fixed-source S0/S1 reduction:             LEAN BANK conditional on named standard analytic providers
Actual weighted coloured pair theorem:    OPEN ANALYTIC PROVIDER
Explicit analytic threshold:              OPEN
Finite splice:                            OPEN
#287:                                     OPEN
```

## Validation (V14 + V15)

* Narrow builds: `lake build RequestProject.Erdos287.ResearchBankV14` — success;
  `lake build RequestProject.Erdos287.ResearchBankV15` — success.
* Full `lake build` — `Build completed successfully (8741 jobs)`, 0 errors.
* `#print axioms`: V14 119 theorems, V15 83 theorems; the union of reported axioms is
  `{propext, Classical.choice, Quot.sound}`. No `sorryAx`, no custom axiom, no
  `Lean.ofReduceBool`, no `Lean.trustCompiler`.
* Forbidden-token scan over all V14/V15 files (`sorry`, `admit`, `axiom`, `native_decide`,
  `unsafe`, `implemented_by`, `extern`, `opaque`, `trustCompiler`, `ofReduceBool`): no code
  occurrences (only English words in doc comments and the `#print axioms` commands).
* External checker: the installed binary is **`leanchecker`** (`/root/.elan/bin/leanchecker`,
  run as `lake env leanchecker --fresh <module>`); **lean4checker is not installed and was not
  run**. Results: see the section below.

## External checker results

Binary: `leanchecker` (`/root/.elan/bin/leanchecker`, Lean toolchain v4.28.0). lean4checker was
**not** run (not installed).

```
lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV14   → exit 0, no output (2312 s)
lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV15   → exit 0, no output (2469 s)
```

`--fresh` replays the complete import closure (including Mathlib and the V14 modules imported by
V15) in the kernel.
