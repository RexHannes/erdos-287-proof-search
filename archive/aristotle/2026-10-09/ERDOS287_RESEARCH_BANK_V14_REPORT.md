# Erdős #287 — Research Bank V14: fixed-tuple compiler / contact / conditional implication

INTERNAL #287 RESEARCH PROGRAMME ONLY. **Erdős #287 remains OPEN. Nothing here claims it.**

Mode: append-only. Compared with the pre-V14 commit (`7b0e706`), every V14/V15 file is newly
added (32 files added, 0 modified). ResearchBankV2–V13 and `ARISTOTLE_SUMMARY.md` are unchanged.
No existing aggregator needed an import line: the library glob `RequestProject.+` already picks up
the new modules in the full `lake build`.

Namespace: `Erdos287.ResearchBankV14.*`.

## Files

```
RequestProject/Erdos287/ResearchBankV14.lean                      (aggregator)
RequestProject/Erdos287/ResearchBankV14/BalancedKernelParameters.lean
RequestProject/Erdos287/ResearchBankV14/MacroGraph11.lean
RequestProject/Erdos287/ResearchBankV14/BalancedBlowup.lean
RequestProject/Erdos287/ResearchBankV14/EdgeOnlyCompilerInterface.lean
RequestProject/Erdos287/ResearchBankV14/CompilerApplication.lean
RequestProject/Erdos287/ResearchBankV14/ContactAnnulus.lean
RequestProject/Erdos287/ResearchBankV14/UsefulPairIdentity.lean
RequestProject/Erdos287/ResearchBankV14/ScoreCombinatorics.lean
RequestProject/Erdos287/ResearchBankV14/RowRigidity.lean
RequestProject/Erdos287/ResearchBankV14/HarmonicTail.lean
RequestProject/Erdos287/ResearchBankV14/ConditionalAsymptoticImplication.lean
RequestProject/Erdos287/ResearchBankV14/EffectivityFirewall.lean
RequestProject/Erdos287/ResearchBankV14/Ledger.lean
RequestProject/Erdos287/ResearchBankV14/AxiomAudit.lean
```

## Principal theorems (all kernel-checked, no `sorry`)

| § | theorem | content |
|---|---|---|
| A1 | `BalancedKernelParameters.K_eq`, `margin_at_bounds`, `margin_gt`, `remaining_margin_gt`, `budget_split` | `K = 2^4170`, `P = 12K`, `a = 2982`, `δ = 1/80`; with `μ_F > 350774/10000`, `W_F < 559454/10000`, `A0 = 2000599/599000`: `μ_F − (A0 W_F + 2/5)/11 − 18 > 163216957/2995000000`, and after the budget `1/20` the remaining margin is `> 13466957/2995000000 > 0`. The functional bounds are fields of the structure `CertifiedFunctionalBounds` (a firewall: they are not identified with arithmetic moments). |
| A2 | `MacroGraph11.alpha_eq_three`, `properColouring`, `col4_classes`, `no_proper_three_colouring`, `occupied_four_forces_edge` | `α(G(11,2)) = 3`; proper 4-colouring `{0,1,2},{3,4,5},{6,7,8},{9,10}`; four occupied cells force a macro-edge. |
| A3 | `BalancedBlowup.cells_balanced`, `cellSize_sum`, `no_edge_in_cell`, `blowupColouring` | Balanced partition of `Fin K` into 11 cells (symbolic, `i ↦ i mod 11`), blow-up graph with no edges inside cells, lifted proper 4-colouring. No enumeration of `2^4170` vertices. |
| A4 | `EdgeOnlyCompilerInterface.prescribedShape_gcdClique`, `edgeOnly_compiler`; `CompilerApplication.compiler_exists`, `compilerTuple` | General edge-only CRT theorem: any finite graph, any rational boxes, arbitrarily large scale `T`, arbitrarily large common translation `A` with `gcd(A+b_u, A+b_v) = |b_u − b_v|` on every edge (in fact every pair). Instantiated on the 11-cell blow-up. **Honest note:** before V14 the repository had no proved edge-only box theorem (V9 provided the general CRT lemma `crt_exists_ge`, re-used here, and an uninhabited interface `PrescribedShapeGCDClique`); the edge-only theorem was therefore proved in V14 from the V9 CRT. It needs neither the colouring nor disjointness of the boxes. |
| A5 | `ContactAnnulus.Rstar_eq`, `Rstar_chain`, `c_gt_inv_e`, `c_mul_Rstar_lt_one`, `c_mul_Rstar_buffer_lt_one`, `edge_difference_range`, `contact_coeff_ratio`, `one_window` | `ε = 1/100`; `149/50 < b_v − b_u < 401/50` for oriented edges; `A ≥ 1000 max b` gives ratio `≤ 1001/1000`; `R* = (401/149)(1001/1000)^2 = 401802401/149000000 < 100/37 < 685/252 < e` (Mathlib's `Real.exp_one_gt_d9`); `c = 37/100 > 1/e`, `c R* < 1`; all contacts in one window `[cM, M]`. |
| A6 | `UsefulPairIdentity.useful_identity_oriented`, `useful_identity_pm_one`, `signless_identity_false`, `fixture_value` | Oriented `a_u < a_v`: `(a_v/d) L_u − (a_u/d) L_v = 1`; unoriented: only `±1`; regression fixture refutes the signless identity. |
| A7 | `ScoreCombinatorics.six_sub_cellScore`, `score_le_18_of_three`, `exists_gt_of_weighted_pos`, `signed_weights_fail` | `6 − (v − C(v,2)/11) = (v−11)(v−12)/22 ≥ 0`; ≤ 3 occupied cells ⇒ `S ≤ 18`; positive nonneg-weighted average ⇒ some `S(t) > 18`; the signed-weight version fails (counterexample). |
| A8 | `RowRigidity.clearing_contradiction`, `row_rigidity`, `multiples_omitted` | With `D_H = lcm(1..H)`, `N_H = Σ D_H/j`: `⌊M/p⌋ ≤ H`, `p > max(H, N_H)` ⇒ no `p`-multiple in a reciprocal-sum-one set. |
| A9 | `HarmonicTail.selected_set_above`, `harmonic_tail_lt_log`, `log_100_37_lt_one`, `two_hole_contradiction_c` | Two consecutive omissions `z, z+1` ⇒ set in `[z+2, M]`; `Σ_{n=z+2}^M 1/n < log(M/z) ≤ log(100/37) < 1`: contradiction. |
| A10 | `ConditionalAsymptoticImplication.eventually_no_counterexample` | `S0Contract + S1Contract + ActualWeightedColouredPairProvider + certified bounds (+ fixed tuple, score margin, row rigidity, harmonic tail)` ⇒ `∃ M₀, ∀ M ≥ M₀, NoCounterexampleAt M` — **every sufficiently large `M`**. The provider is a `structure` that is never constructed. |
| A11 | `EffectivityFirewall.effectivity_firewall`, `compiler_outputs_unbounded` | Compiler useful-height bound `= none`; explicit analytic threshold `= none`; finite splice closed `= false`; the audited `10^500` payload remains `notSupplied` (no theorem about it). |
| D | `Ledger.v14_preserves_v13_ledger`, `v14_status_ledger`, `v14_erdos287_open`, `v14_no_open_item_promoted` | Append-only ledger; #287 OPEN. |

## Trust

* `AxiomAudit.lean`: `#print axioms` for all 119 V14 theorems. Output: only `propext`,
  `Classical.choice`, `Quot.sound` (or subsets). No `sorryAx`, no custom axiom,
  no `Lean.ofReduceBool`/`Lean.trustCompiler`.
* No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern` in any
  V14 file (the only textual hits of the scan are English words in doc comments and the
  `#print axioms` lines).
* Build and checker results: see `ERDOS287_RESEARCH_BANK_V15_REPORT.md` (shared validation section).
