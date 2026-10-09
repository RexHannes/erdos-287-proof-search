# ERDŐS #287 — FRONTIER AUDIT / CONTINUATION SYNC REPORT

**INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.**
**NO PUBLIC ERDŐS CLAIM. ERDŐS #287 REMAINS OPEN AND IS NOT CLAIMED.**

Checkpoint: `2026-09-10`, version `FRONTIER_AUDIT_v1`.
Mode: continuation of the existing repository / append-only / audit of the current
`k = 1` frontier / evidence-typed / axiom-audited.

---

## 1. Repository state on entry

* Single pre-existing commit (`Initial commit`), working tree clean, 467 Lean modules.
* The bounded-conductor sync (`CompensatedMeasure`, `HyperbolaInterfaces`,
  `CompensatedSummationByParts`, `AdjacentInterfaceFirewall`, `ResidueCollapse`,
  `InternalProductFibre`, `SmallEllCRT`, `HalfOpenProgressionCompiler`,
  `SmallEllMeanCovariance`, `CompensationLoop`, `BoundedConductorFrontier`,
  `RankThreeOperator`, `RankThreeProjection`, `ConductorComplementLedger`,
  `AnnihilatorFamily`, `DensityCompensationRestoration`,
  `CurrentStatusEffectivityBoundedConductor`) was **already present, already imported by
  `RequestProject/Main.lean`, and already building**.  Its report
  (`ERDOS287_BOUNDED_CONDUCTOR_FORMAL_SYNC_REPORT.md`) was present as well.
* A full `lake build` on entry **passed**: `Build completed successfully (8493 jobs)`.
* No module was rebuilt, rewritten, renamed or deleted in this run.  **Nothing from the
  earlier interrupted run was discarded.**

What was *not* finished by the interrupted run: the declaration registration / audit stage
and the continuation of the frontier itself.  Both are completed here.

## 2. Files added in this run

All under `RequestProject/Erdos287/`:

| # | File | Content |
| --- | --- | --- |
| 1 | `FixedConductorCharacterRepair.lean` | §61 — refutation of the unnormalised character interface; normalised repair |
| 2 | `BoundedConductorTargetAudit.lean` | §62 — long-window period law; `meanSum ≠ 0`; refutation of the `k = 1` target; density-centred replacement target |
| 3 | `CentredFrontierTriviality.lean` | §64 — uniform atom bound; period-block algebra; the centred target is satisfiable |
| 4 | `CurrentStatusEffectivityFrontierAudit.lean` | §63 — status aggregator, evidence table, finite-bank status, `#print axioms` |

File modified: `RequestProject/Main.lean` — **one added import line** for the new aggregator.
`ARISTOTLE_SUMMARY.md` was not modified.

## 3. Principal new theorems

### §61 `FixedConductorCharacterRepair.lean`

| Declaration | Evidence |
| --- | --- |
| `returnedKernel_one_point_window` | KERNEL_PROVED — on the one-point window `[2503,2504)` only the conductor `ℓ = 2503` survives |
| `returnedKernel_outer_periodic`, `returnedKernel_one_point_ne_zero` | KERNEL_PROVED |
| `fixedConductorCharacterBound_unsatisfiable` | **KERNEL_PROVED REFUTATION** — `FixedConductorCharacterBound b` is false for **every** `b` |
| `character_bound_bridge_is_vacuous` | KERNEL_PROVED — the banked bridge `character_bound_implies_k1_owner_bound` has an unsatisfiable hypothesis |
| `FixedConductorCharacterMeanBound`, `characterMeanBound_iff_boundedConductorTarget` | KERNEL_PROVED — the *normalised* character interface is exactly equivalent to the pointwise `k = 1` target |

### §62 `BoundedConductorTargetAudit.lean`

| Declaration | Evidence |
| --- | --- |
| `sum_Ico_period_multiple`, `sum_Ico_eq_sum_range` | KERNEL_PROVED (generic periodic-window algebra) |
| `meanTerm`, `meanSum`, `meanK_eq_meanTerm`, `periodSum_eq_mul_meanTerm` | KERNEL_PROVED |
| `Kell_long_window`, `returnedKernel_long_window` | **KERNEL_PROVED** — over `n` full periods the returned kernel equals `P·n·meanSum` |
| `meanSum_ne_zero` | **KERNEL_PROVED** — the aggregate complete-period mean is nonzero; proved by a `4999`-adic valuation argument (`padicNorm_meanTerm_4999`, `padicNorm_meanTerm_le_one`, `not_dvd_meanDen`) |
| `boundedConductorK1Target_unsatisfiable` | **KERNEL_PROVED REFUTATION** — the `k = 1` frontier target is false for every `b` |
| `characterMeanBound_unsatisfiable` | KERNEL_PROVED |
| `perSum`, `perMean`, `meanSumAt`, `meanSumAt_one`, `CentredBoundedConductorK1Target` | definitions / KERNEL_PROVED |
| `returnedKernel_of_empty_window`, `centred_target_needs_ordered_windows` | KERNEL_PROVED — the ordered-window restriction is necessary |
| `centred_kernel_vanishes_on_full_periods`, `frontier_repair_summary` | KERNEL_PROVED |

### §64 `CentredFrontierTriviality.lean`

| Declaration | Evidence |
| --- | --- |
| `Kbound`, `abs_Kell_le` | KERNEL_PROVED — a bound on `K_ℓ` uniform in `s` and `z` |
| `periodBlock_base_independent`, `sum_blocks`, `abs_sum_Ico_le`, `sum_Ico_split` | KERNEL_PROVED |
| `windowSum_centred_bound` | KERNEL_PROVED — per conductor, window sum minus density term is at most one incomplete period |
| `centred_target_satisfiable`, `centred_target_exists_budget` | **KERNEL_PROVED** — the centred target holds for the explicit budget `centredBudget` |
| `qualitative_boundedness_has_no_analytic_content` | KERNEL_PROVED firewall |

### §63 `CurrentStatusEffectivityFrontierAudit.lean`

Evidence table (`frontierAuditEvidence`), `frontierAudit_refutations_are_backed`,
`frontierAudit_open_frontier`, `early4490_and_bank_preserved`,
`centred_target_qualitatively_settled`, finite-bank status
(`finite_bank_status_recorded`, `finite_ceiling_kernel_proved`,
`finite_ceiling_below_ten_pow_sixty`), plus the `#print axioms` block.

## 4. What the audit means

The `k = 1` frontier as formalised does **not** state a nontrivial analytic problem:

1. Unnormalised character interface — false for every budget (arbitrary finite outer sets
   of `z` with unit weights add up an unbounded number of copies of one nonzero value).
2. Normalised character interface — exactly equivalent to the pointwise target; no gain.
3. Pointwise target over all half-open windows — false for every budget, because the
   returned kernel carries a **nonzero density**: over `n` full periods it equals
   `P·n·meanSum` with `meanSum ≠ 0`.
4. Density-centred target on ordered windows — holds for *some* budget, for the structural
   reason that a finite sum of periodic kernels with uniformly bounded atoms deviates from
   its density only by one incomplete period.

Consequently the live analytic content has to be re-stated **quantitatively** (an
admissible ledger budget) and at the level of the physical `X → ∞` source, not for the
finite periodic kernel alone.  This is consistent with, and reinforces, the banked firewall
`DX_term_not_removable`.  **No owner is closed by this run.**

## 5. Build and axiom audit

* Full `lake build` after the additions: **PASS** — `Build completed successfully (8497 jobs)`.
* Dedicated builds of all four new modules: **PASS**, no warnings.
* `#print axioms` on every principal new theorem: only `propext`, `Classical.choice`,
  `Quot.sound` (`frontierAudit_open_frontier` depends on none).
* Scan of the new modules for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `@[implemented_by]`, `opaque`: **no matches**.

## 6. Finite side

* Kernel-verified in this repository: **no counterexample with maximum `M ≤ 67108856338751594`**
  (`Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling`), built on the 34-window
  bank reaching `4·10^9` plus 24 Pratt-certified windows.
* `M ≤ 10^60`: **NOT PRESENT** in this repository (`finite_ceiling_below_ten_pow_sixty`
  records that the available ceiling is far below `10^60`).  It was not reconstructed.
* `U2 = 3739298103962937078961175187719640178760086558841160733818922`: the certified-factor
  data and the harmonic-blocker witness are **not supplied** anywhere in the repository, so
  the extension is recorded as **PENDING** and nothing was invented.

## 7. Current minimal open cut set

1. `centredK1TargetQuantitative` — a ledger-admissible *quantitative* budget for the centred
   bounded-conductor `k = 1` kernel (the qualitative version is now settled and empty of
   content); equivalently, a physical-window restatement of the `k = 1` owner.
2. `Ω(k) = 2`, 3. `Ω(k) = 1`, 4. EARLY_4490 residual leaf, 5. proper gamma over the full slab,
6. `S_live`, 7. `R_012`, 8. signed floor, 9. final splice.
Maynard: NOT ENTERED. Erdős #287: OPEN.

## 8. Continuation state

Begin from item 1 of the cut set: restate the `k = 1` owner as a quantitative bound for the
*physical* hyperbola windows (`HyperbolaInterfaces.physIndex`) with the true source weights
and an explicit ledger budget, then re-derive the bridge to the owner ledger.  The banked
exact machinery (CRT compiler, `≤ 65` atoms, half-open progression compiler, local mean,
Gram structure, compensation-loop firewall, returned finite-conductor kernel) is unchanged
and directly reusable; the refuted statements must not be re-used as hypotheses.

**NO PUBLIC ERDŐS CLAIM. ERDŐS #287: OPEN.**
