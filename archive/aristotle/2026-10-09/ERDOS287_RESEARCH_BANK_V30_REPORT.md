# Erdős #287 — Research Bank V30 report (final pre-effectivity composition)

INTERNAL #287 RESEARCH PROGRAMME ONLY. **Erdős #287 is OPEN. Explicit M₀ is OPEN. Finite splice is OPEN.**

Mode: append-only. V2–V28, every historical report and `ARISTOTLE_SUMMARY.md` are unchanged.

## Files added

- `RequestProject/Erdos287/ResearchBankV30.lean` (aggregator)
- The files in `RequestProject/Erdos287/ResearchBankV30/`:
  - `FullPairComposition.lean`
  - `SameSourceChain.lean`
  - `SameWeightChain.lean`
  - `SameNormalizationChain.lean`
  - `QuantifierOrder.lean`
  - `FinalPreEffectivity.lean`
  - `TrustedChallenge.lean`
  - `Status.lean`
  - `AxiomAudit.lean`

Namespace: `Erdos287.ResearchBankV30.<File>`.

## Classification (task §23)

**SUCCESS D: SEMANTIC MISMATCH.** It is recorded in `Status.final_classification`, which is checked by `decide`.

- **First mismatch: the same-source chain.** The zero-frequency functional `D0` is not defined from the physical source `(τC, W)`. The same holds for `D1`, `D2`, `Db` and `DEnz`.
  - The bank proves the tensor/cell, fixed-state, HB, dyadic, colour and clean-state splits as identities about explicit finite sums. No declaration applies them to `Pair τC W`.
  - `same_source_not_established` proves the consequence: the zero functionals with the empty DI class satisfy every branch field, the DI field and the nonzero realization. The branch fields therefore do not force any link to the source.
- **Same-weight chain: established** (`same_auxiliary_weight_end_to_end`).
- **Same-normalization chain: established** (`same_normalization_end_to_end`).
- **Not SUCCESS A.** Internal content remains in `InternalGlueOwner`, which has two fields: `tensor`, the actual-measure majorization, and `nonzero`, the clean realization. The latter includes DIClass membership, kernel realization and `NonzeroPruningContract`. The structural hypotheses `SieveGeometry`, `RoundedCellData`, `Li ≥ 0` and `φ(W) > 0` also remain. They are stated on sieve universes and parameters that the bank never interprets.
- **Earliest missing derivation (task §4 STOP).** For every clean state `s` of the nonzero branch, `DIClass s.DD.KD` is missing. No physical clean-state generator exists and `DIClass` is undefined.
- **SUCCESS C was avoided, not triggered.** No external provider was strengthened. The degenerate route `old_FinalAnalyticProviders_of_degenerate` needs a remainder-free tensor provider, which is stronger than any tensor-approximation theorem. It is recorded as a mismatch witness and is not used by the final theorem.

## Main theorems

- **`FullPairComposition.full_pair_composition`** (§14). One proof, with explicit declaration references:
  - V24 `lamFam_source_decomposition` gives the completed positive sieve and the source decomposition of the SAME weight.
  - The glue owner's `tensor.decomp` gives the principal + remainder split.
  - V28 `derived_source_class_provider` and V24 `distribution_error_small` handle the zero, one-large, two-large and boundary branches.
  - V28 `nonzero_branch_small` (built on V27 `clean_nonzero_derived`) handles the clean nonzero branch.
  - V23 `principal_budget_le_A_C` gives the same-weight principal bound.
  - V23 `hat_approximation_eventually_small` gives the tensor approximation.
  - The conclusion: for every `η > 0` there are `S, τ, M₀` such that for all `M ≥ M₀`, `‖B_x‖² ≤ A_C W_F + η` and `P_actual/N ≤ A_C W_F + 27/5 + η`.
- **`SameSourceChain.same_source_end_to_end`**: one `(τC, W)` feeds S0, S1 and the majorized `Pair`. **`same_source_not_established`**: the mismatch witness.
- **`SameWeightChain.same_auxiliary_weight_end_to_end`**: `LambdaNewPlus` sits in the physical majorant slot, in both remainder slots, in the principal bound and in the source decomposition, for the same `S, τ, M`.
- **`SameNormalizationChain.same_normalization_end_to_end`**: one `R.N` serves S0, S1, the principal prefactor, the pair baseline (with the exact conversion `27/5 = 90 + errFinal`), the actual pair bound, and the consumer check `ThinMarginCheck μ_lo W_hi errFinal`. Also proved: `baseline_of_full_pair`.
- **`QuantifierOrder.quantifier_order_respected`**, with `rho_fixed` and `mass_independent_of_M`. `S` and `τ` are existentials outside `∀ M`, and they appear in the conclusion through the weight `LamFam S τ M`. `ρ` is a constant. The representation mass depends only on `(S, τ)`.
- **`FinalPreEffectivity.pre_effectivity_287_FINAL_BANK`**:

  ```
  MinimalExternalAnalyticProviders … → FunctionalKernelCertificate muF (LF/I) →
  InternalGlueOwner … errFinal … → SieveGeometry … → RoundedCellData … →
  (∀ M, 0 ≤ Li M) → 0 < phiW → ∃ M₀, ∀ M ≥ M₀, NoCounterexampleAt M
  ```

  The V28 hypothesis `0 ≤ LF/I` is no longer needed: it is derived from the certificate. The type shows the dependence on the internal glue owner, so this is **not** a SUCCESS A bank.
- **`TrustedChallenge.trusted_challenge : TrustedStatement`**. `TrustedStatement` is the closed proposition. `noCounterexampleAt_unfold` shows that `NoCounterexampleAt M` unfolds literally to the #287 statement at endpoint `M`.
- **`Status.final_classification`** and **`Status.not_successA`**.

## Trust

- **Build**: `lake build RequestProject.Erdos287.ResearchBankV30` succeeds (8315 jobs). There are no warnings in V30 files. It includes `AxiomAudit` and imports all of V29.
- **Full project**: `lake build` (the default target) succeeds with 8907 jobs.
- **Append-only check**: `git diff --name-status bf0b461 HEAD` lists only added files (`A`). No V2–V28 file, historical report or `ARISTOTLE_SUMMARY.md` was modified.
- **Axioms**: `#print axioms` was run on the 14 V30 theorems. 12 depend on exactly `[propext, Classical.choice, Quot.sound]`. `Status.final_classification` and `Status.not_successA` depend on no axioms. V29 has 37 audited declarations, all `[propext, Classical.choice, Quot.sound]`.
- **Forbidden tokens**: the scan of V29/V30 code finds no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, `unsafe`, `implemented_by`, `opaque`, `skipKernelTC` or `trustCompiler`. The only hits are doc-comment words.
- **External checker**: `leanchecker` is installed; `lean4checker` is not. The result of `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV30` is recorded below.
- **Comparator**: not installed. `comparator` is not on `PATH`, and `lake comparator` fails with "unknown command 'comparator'". It was NOT run, and nothing was emulated in its place.

### External checker result

`lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV30` exited with **0** (real 56m45s). No declaration was rejected. This run re-checks every declaration in the environment of V30, which includes all of V29 and the frozen V2–V28 dependencies it imports.
