# Erdős #287 — Research Bank V7 report

**INTERNAL #287 RESEARCH PROGRAMME ONLY. Erdős #287 is `OPEN`; no proof and no counterexample is
claimed. No universal global closure is claimed.**

## 1. Scope and append-only discipline

New layer `RequestProject/Erdos287/ResearchBankV7/` with aggregator
`RequestProject/Erdos287/ResearchBankV7.lean`.

Nothing in `AnchoredV2*`, `AnchoredV3*`, `AnchoredV4*`, `ResearchBankV5*`, `ResearchBankV6*` was
edited, renamed, moved, weakened, reinterpreted or overwritten. V7 only imports, re-exports and
audits those layers (`git status` shows the V7 files and this report as the only additions).

## 2. Files added

| file | content |
| --- | --- |
| `ResearchBankV7/Epochs.lean` | four research epochs (V6 upper-gap/carry, STABLE-ENTRY, exact-HIT/arithmetic-spine, current ENTRY-FIRST), epoch-stamped owner records, meta-firewalls |
| `ResearchBankV7/Absorption.lean` | exact finite charging theorem for bounded adaptive absorption; budgets at `γ = 1/8`; branching-bit budget |
| `ResearchBankV7/PolylogCompletion.lean` | finite second moment, disjoint buffer packing (proved); Croot / PNT / LLL external interfaces; the fixed-polylog complete-row law and its conditional theorem |
| `ResearchBankV7/StableEntry.lean` | absorption setup, forward direction (kernel), leaf-realization interface, the conditional feasibility equivalence, firewalls |
| `ResearchBankV7/IntervalLifting.lean` | exact mixed-modulus interval lifting with actual Boolean subsets, overlap inequality, recursion for successive lifts with support and mass bookkeeping |
| `ResearchBankV7/Spine.lean` | arithmetic-spine extraction from a **supplied** certificate |
| `ResearchBankV7/ErasureHit.lean` | ERASURE-HIT (erasure, arbitrary fixed part, complement/two-sided, rational form) |
| `ResearchBankV7/GuardedBranchHit.lean` | guarded branch-to-HIT with the actual reference-word mass `S(x₀)`; firewalls and the seed-mass counterfixture |
| `ResearchBankV7/FouvryPin.lean` | Fouvry/Luca–Young, Selberg, Brun–Titchmarsh, prime-counting interfaces; pin-capture inequality; sublinear-support consequence; branch-budget localization |
| `ResearchBankV7/FiniteSourceKills.lean` | finite `p = 2q ± 1` source kills (59, 83, 107, 61, 73), counterfixture, supply firewall |
| `ResearchBankV7/Numerics.lean` | corrected metadata: `J = L₄₄₇` has **194 decimal digits and 644 bits** |
| `ResearchBankV7/V6Audit.lean` | semantic spot audit of the five load-bearing V6 theorems; re-export unchanged |
| `ResearchBankV7/Owners.lean` | superseded V6 owners; the current sole owner; the closure DAG with proved edges only |
| `ResearchBankV7/Ledger.lean` | epoch-aware verdict ledger (frozen V6 block + new rows) with machine-checked discipline |
| `ResearchBankV7/AxiomAudit.lean` | `#print axioms` for every principal V7 theorem |

## 3. Evidence classification of the new results

**KERNEL-BANKED (sorry-free, standard axioms only)**

* charging: `guarded_charging`, `unguarded_charging`, `guarded_W_bound`, `guarded_U_bound`,
  `unguarded_W_bound`, `unguarded_U_bound`, `branching_bits_le`;
* interval lifting: `interval_lift`, `lift_interval_nonempty`, `chain_reaches`,
  `chainSupport_card_le`, `chain_mass_eq`;
* spine: `SpineCert.spine_subset`, `spine_reaches`, `spine_reaches_all`, `spine_card_le`,
  `spine_mass_eq`;
* erasure: `erasure_hit`, `erasure_hit_with_fixed_part`, `erasure_hit_complement`,
  `erasure_hit_rational`;
* guarded branch: `GuardedBranch.deficit_eq`, `guarded_branch_to_hit`, `guards_preserved`;
* STABLE-ENTRY forward: `stableEntry_forward`;
* polylog finite components: `finite_second_moment`, `buffer_packing`;
* Fouvry finite consequences: `sublinear_support_cannot_capture_positive_proportion`,
  `branch_budget_pin_localization`;
* numerics: `J_digits`, `J_bits`, `J_is_not_194_bits`, `lcmRange_eq_lcmUpto`;
* V6 spot audit and all meta-firewalls.

**CONDITIONAL-BANKED (implication proved; premise uninhabited here)**

* `polylog_completion_conditional` (Croot + PNT + LLL adapter);
* `stableEntry_reverse`, `stableEntry_equivalence`, `stableEntry_equivalence_conditional`;
* `pin_capture_conditional`, `short_cofactor_pin_bound`.

**COUNTERFIXTURE**: `seed_mass_is_not_reference_mass`, `kill_pattern_not_universal`,
`lift_failure_is_not_unsat`, `overlap_failure_is_not_unsat` (terminology firewalls).

**FINITE-SOURCE-KILL**: `sourceKill_2q_add_one`, `sourceKill_2q_sub_one` and the five explicit
instances — finite diagnostics only.

**SUPERSEDED (never false)**: `UpperGapCarryCompression`, `ExactMassIntersection`.

**OWNER-OPEN**: `GenuineEntryReferenceWord`, `EntryFirstTerminalLeafExistenceOrKill`,
`SafePrimeSupply`, and Erdős #287 itself.

## 4. Current closure DAG

```text
FULL-FROZEN / seed constraints
  → bounded absorption                      (kernel)
  → STABLE-ENTRY terminal-leaf criterion    (forward kernel / reverse conditional)
  → genuine ENTRY reference word            (UNINHABITED — no theorem bypasses it)
  → guarded spine / ERASURE-HIT             (kernel)
  → exact S = 1
```

`Owners.no_bypass_of_entry_node`, `Owners.dag_does_not_close` and
`Epochs.no_closure_propagation_through_ledger_edges` are machine-checked.

## 5. Audit

* `lake build RequestProject.Erdos287.ResearchBankV7` — succeeds.
* `lake build` (full project) — succeeds.
* `#print axioms` on every principal V7 theorem: only `propext`, `Classical.choice`, `Quot.sound`
  (several bookkeeping theorems depend on no axioms).
* Token scan of the V7 layer: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`,
  `@[implemented_by]`. The only computational steps are ordinary kernel `decide` on explicit
  finite data (the `J = L₄₄₇` size certificates, audit fixtures, decidable ledger checks), kept in
  their own declarations, separate from the general theorems.

## 6. Final verdict

```text
V6                                            frozen historical bank
bounded absorption                            banked
polylog completion                            correctly dependency-classified (conditional)
STABLE-ENTRY                                  banked as reduction/equivalence, not existence
exact interval lifting                        banked
arithmetic spine                              banked as certificate theorem
ERASURE-HIT                                   banked
guarded branch-to-HIT                         banked as sufficient conditional theorem
Fouvry localization                           banked, external analytic dependencies explicit
finite source kills                           banked as finite diagnostics only
genuine ENTRY seed / surviving terminal leaf  OPEN
Erdős #287                                    OPEN
```
