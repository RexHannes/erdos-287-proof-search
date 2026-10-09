# Erdős #287 — Research Bank V29 report (provider audit and elimination)

INTERNAL #287 RESEARCH PROGRAMME ONLY. **Erdős #287 is OPEN. Explicit M₀ is OPEN. Finite splice is OPEN.**

Mode: append-only. V2–V28, every historical report and `ARISTOTLE_SUMMARY.md` are unchanged.

## Files added

- `RequestProject/Erdos287/ResearchBankV29.lean` (aggregator)
- The files in `RequestProject/Erdos287/ResearchBankV29/`:
  - `PhysicalCleanState.lean`
  - `DIClassRealization.lean`
  - `KernelRealization.lean`
  - `NonzeroPruning.lean`
  - `ZeroBranchComposition.lean`
  - `TypeIIBranchComposition.lean`
  - `OneLargeComposition.lean`
  - `TwoLargeComposition.lean`
  - `SourceNormalization.lean`
  - `FunctionalCertificate.lean`
  - `ProviderElimination.lean`
  - `Ledger.lean`
  - `AxiomAudit.lean`
- `PROVIDER_CLASSIFICATION.md` (task §2)
- `FINAL_EXTERNAL_PROVIDER_MAP.md` (task §20; it covers V29's minimal bundle)

Namespace: `Erdos287.ResearchBankV29.<File>`.

## Headline findings

1. **§4 STOP: no physical clean state exists, and `DIClass` is undefined.**
   - `CleanState x` (V27) is an abstract structure. `KloostermanData` has no fields for `q₀, D, r₁, r₂, n₁, n₂`, so the §4 gcd conditions cannot even be expressed on it.
   - `DIClass` is a free predicate parameter everywhere. The V28 typing admits both a vacuous reading and a false reading (`DIClass_underdetermined`).
   - The §4 arithmetic conditions alone give a FALSE provider (`arithOnlyClass_provider_false`). DIClass therefore must not be weakened to them.
   - **Earliest remaining composition hole:** the membership `DIClass s.DD.KD` inside `CleanAdmissible` for the clean states of the nonzero branch. It is named `ActualCleanStateMemDIClass`.
2. **§5: no physical smooth cutoff exists.** `psiHat` and `b` in V27 are abstract, and the kernel `Kl` is an arbitrary function. The kernel is load-bearing: `kernel_is_load_bearing` gives two forms with identical numeric data and opposite DI verdicts. `realize_clean_kernel` cannot be built without inventing the DI kernel, which §24 forbids.
3. **§6: `NonzeroPruningContract` is NOT retired.**
   - There is no physical `R_nonzero`.
   - The exact seven-sector shape is formalized (`NonzeroSectorDecomposition`). The composition lemma `nonzero_pruning_from_sector_decomposition` derives the contract from any exact sector decomposition with summed bounds.
   - The decomposition itself has no source.
   - The contract and the whole V28 realization hold vacuously at value 0 with the empty family (`nonzero_realization_zero`). The contract is not vacuous in general (`pruning_contract_nontrivial`).
4. **§7: branch fields.** `D0, D1, D2, Db, DEnz` are uninterpreted.
   - The V25/V26 identities hold for explicit sums but are never applied to these functionals. The branch fields are kept as external-shape class bounds, and the identification with the physical branch sums is recorded as missing.
   - Composition lemmas are proved: `branchClassBound_of_uniform`, `oneLarge_sum_split`, `twoLarge_sum_split`, `four_branch_sum_small`, `typeII_coverage`, `typeII_branch_small_of_realization`, and `zero_frequency_eventually_le` (a reuse of V25).
   - Vacuity: `branchClassBound_zero`.
5. **§8–§9 hold.**
   - `all_components_same_normalization`: S0, S1, the principal prefactor, the tensor decomposition and the consumer's baseline all use ONE `RouteCNormalization.N`.
   - `principal_weight_eq_error_weight`: `LambdaNewPlus` is literally the weight in the principal slot and in both remainder slots.
6. **§10: no certificate data is in the repository.**
   - `FunctionalKernelCertificate` is a FINITE CERTIFIED INPUT with provenance `certificateProvenance`. It is equivalent to the V28 thin certificate (`certificate_iff_thin`).
   - `−1079/1900` has no derivation in the repository. Only `= −1/2 − 129/1900` and its sign comparisons are checked. The missing derivation is the analytic real-correction estimate that produces the `129/1900` excess.
7. **§11: score formula MISMATCH.**
   - The consumer consumes `RouteCMarginCheck`, i.e. `μ_lo − (A_C W_hi + 27/5)/99 − 350 > 0`, whose value is `12093752057/12285000000` (`consumedMargin_value`).
   - The task's formula subtracts an additional `1/20` (`score_formula_relation`, `taskScore_ne_consumed`). It equals `11479502057/12285000000 > 0` (`taskScore_value`) and implies the consumer check (`task_score_implies_consumer`). It is not the consumed quantity.
8. **§12: the provider split.**
   - `MinimalExternalAnalyticProviders` holds only external analytic fields: rosser, tuple, euler, hat, di, zeroFreq, oneLarge, twoLarge, boundary, s1.
   - `FunctionalKernelCertificate` is the finite certified input.
   - `InternalGlueOwner` holds the NOT-eliminated internal fields `tensor` and `nonzero`.
   - `old_FinalAnalyticProviders_of_minimal` rebuilds the old V28 bundle FROM minimal + certificate + glue.
   - `old_FinalAnalyticProviders_of_degenerate` shows that the old bundle can also be built with all branch functionals zero and `DIClass = ∅`. That route needs a remainder-free tensor provider, which is stronger than any external theorem (SUCCESS C). It is recorded and not used.

## Theorems proved (by file)

- **PhysicalCleanState**: `DIArithmeticConditions_satisfiable`, `DIArithmeticConditions_nontrivial`, `degenerateArith_conditions`, `arithOnlyClass_provider_false`.
- **DIClassRealization**: `di_provider_empty_class`, `di_provider_full_class_false`, `DIClass_underdetermined`, `cleanAdmissible_empty_class`. It also defines `ActualCleanStateMemDIClass`, a named hole that is not assumed anywhere.
- **KernelRealization**: `zeroKernelForm_DI`, `kernel_is_load_bearing`.
- **NonzeroPruning**: `nonzero_pruning_from_sector_decomposition`, `pruning_contract_empty`, `pruning_contract_nontrivial`, `nonzero_realization_zero`.
- **ZeroBranchComposition**: `branchClassBound_zero`, `branchClassBound_of_uniform`, `zero_frequency_eventually_le`.
- **TypeIIBranchComposition**: `typeII_coverage`, `typeII_branch_small_of_realization`.
- **OneLargeComposition**: `oneLarge_sum_split`.
- **TwoLargeComposition**: `twoLarge_sum_split`, `four_branch_sum_small`.
- **SourceNormalization**: `all_components_same_normalization`, `lamFam_eq_lambdaNewPlus`, `principal_weight_eq_error_weight`.
- **FunctionalCertificate**: `mu_F_lower`, `W_F_upper`, `certificate_iff_thin`, `exponent_supplied_facts`, `consumer_check_iff`, `consumedMargin_value`, `score_formula_relation`, `taskScore_value`, `task_score_implies_consumer`, `taskScore_ne_consumed`.
- **ProviderElimination**: the definitions `old_FinalAnalyticProviders_of_minimal` and `old_FinalAnalyticProviders_of_degenerate`. They are definitions because the V28 bundle carries data.
- **Ledger**: `internal_not_external`, `remaining_internal`, `cert_isolated`.

## Trust

- `lake build RequestProject.Erdos287.ResearchBankV29` succeeds (8307 jobs), with no warnings in V29 files.
- `#print axioms`: all 37 audited declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- Forbidden-token scan of V29 (sorry, admit, axiom declarations, native_decide, bv_decide, unsafe, implemented_by, opaque, skipKernelTC, trustCompiler) finds nothing in code. The only hits are the doc-comment words "axiom audit" and "admits".
- The external checker is covered by the V30 run (V30 imports V29): see the V30 report.
