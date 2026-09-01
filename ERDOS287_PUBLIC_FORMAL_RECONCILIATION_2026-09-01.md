# ERDŐS #287 — PUBLIC-TREE FORMAL RECONCILIATION (2026-09-01)

Append-only reconciliation of the current public formal tree. No mathematical theorem
statement was altered, no file was deleted, and Erdős #287 is **not** claimed to be solved.

## CURRENT COMMIT

Base of the audit: `3ebb841` ("Initial commit", the public `main` state at the start of this
pass).
Reconciliation commit adding this layer: `49ae6c0` (files listed below).

## LAKE BUILD

* Baseline (pre-pass, unmodified tree): `lake build` — **Build completed successfully
  (8317 jobs)**, `0` errors, `32` warnings (all cosmetic linter warnings: unused variables
  and unused `simp` arguments in pre-existing files; no deprecation and no failure).
* After this pass: `lake build` — **Build completed successfully (8320 jobs)**, `0` errors.
  The three added jobs are the three files added below.

## PLACEHOLDER SCAN (repository-wide)

`sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `implemented_by`:

* **no occurrence as Lean code** anywhere in `RequestProject/`;
* the words occur only inside docstrings/prose and in `.md` files (e.g. "no `sorry`,
  `axiom`, `unsafe`, or `native_decide`", "the unsafe heuristic …", "admit several coprime
  factorisations").

## AXIOM AUDIT

`#print axioms` is executed by the audit modules during the build. In the full build log,
`2276` axiom reports were emitted; parsing every reported axiom set gives exactly the union

```
{ propext, Classical.choice, Quot.sound }
```

with `0` occurrences of `sorryAx` and no user-declared axiom. The end-to-end chain was
re-printed in this pass (`RequestProject/Status/AxiomAuditPublicTreeReconciliation20260901.lean`),
covering in particular

`no_Erdos287Counterexample_of_closure`, `erdos287_seq_of_closure`,
`Gap2CE.no_of_windowPairSupply`, `windowPairSupply_of_sophieWitness`,
`no_Erdos287Counterexample_of_max_le_4e9`, `no_Erdos287Counterexample_of_prime_max`,
`erdos287_seq_of_no_counterexample`,

plus all twelve declarations of the new bridge layer and all twenty-five of the new
reconciliation layer.

## AUTHORITATIVE STATUS FILE

Preserved unchanged and treated as governing:

* `RequestProject/Status/SemanticFirewallsErdos287.lean`
* `RequestProject/Status/CurrentAuthoritativeStatusErdos287.lean`
* `RequestProject/Status/Erdos287EndToEndStatus.lean`
* `RequestProject/Erdos287/ClosureInputs.lean`

The new layer `RequestProject/Status/PublicTreeReconciliation20260901.lean` is *later* in the
chronological ordering and therefore governs labels only; it contradicts no earlier
mathematical content and rewrites no historical status file.

## EXACT PUBLIC THEOREM

```lean
theorem Erdos287.no_Erdos287Counterexample_of_closure
    (I : Erdos287ClosureInputs) : Erdos287Statement
```

with `Erdos287Statement := ∀ A : Finset ℕ, ¬ Erdos287Counterexample A`, reconfirmed in this
pass as `PublicTree20260901.reconfirm_endToEnd`, and — via the new statement equivalence —
in the published ordered form as `PublicTree20260901.reconfirm_endToEnd_seq`.

## UNINHABITED INPUTS

No inhabitant of `Erdos287ClosureInputs` exists anywhere in the tree. Beyond the metadata
ledger, this pass adds *mathematical* guards showing the input is not vacuously inhabitable
and has real arithmetic content:

* `not_windowPairSupply_zero`, `not_windowPairSupply_one`, `not_windowPairSupply_two`
  — the supply statement is false for `M ≤ 2`;
* `closureInputs_threshold_ge_three` — hence every inhabitant has threshold `M0 ≥ 3`;
* `windowPairSupply_forces_large_primePowers` — a window pair at `M` produces two
  consecutive positions `x`, `x+1` with `M ≤ 2x ≤ 2M`, each divisible by a prime power
  `> M/10`;
* `closureInputs_supply_visible` — the `supply` field is exposed verbatim, never hidden;
* `no_banked_interface_constructs_closureInputs` — metadata ledger over the eight banked
  local analytic / source interfaces (grouped product energy, Ξ-gcd tail, affine product
  energy, Ω weighted divisor moment, simultaneous-critical packet, dense `q_C`
  admissibility, C0 physical normalisation, transverse carrier); each is recorded as **not**
  constructing a closure-inputs inhabitant. This row is explicitly labelled metadata: it is
  a bookkeeping fact about the repository, not a mathematical impossibility theorem.

## WINDOWPAIR SUPPLY

**OPEN.** Classified `open_` with kind `windowPairSupplyKind`
(`supply_is_input_not_output`). It is an input to the compiler, never an output of it.

## END-TO-END ERDŐS287

**OPEN.** The implication `Erdos287ClosureInputs → Erdos287Statement` is kernel-proved; the
statement node remains `open_`. This is enforced in Lean by
`implication_does_not_close_target`. No theorem named `erdos287` is declared anywhere in the
repository (checked by search), and none may be added while `supply` is unproved.

## STATEMENT-EQUIVALENCE AUDIT

**PASS.** Details in `ERDOS287_STATEMENT_EQUIVALENCE_2026-09-01.md`. The missing purely
logical bridge was supplied: `erdos287Statement_iff_seqStatement` proves that the set form
and the published ordered-sequence form are equivalent (previously only the forward
direction existed), together with `gap_le_two_iff_orderEmb_gap` (adjacent-gap dictionary) and
`sum_recip_rat_iff_real` (`ℚ` vs `ℝ` reciprocal-sum condition). The problem statement is not
weakened anywhere.

## SEMANTIC FIREWALL AUDIT

**PASS.** Coverage of the required items in the current tree:

| Item | Guard | Status |
|---|---|---|
| `q`-role ambiguity | `SemanticFirewalls.qRoles_pairwise_distinct`, `qRole_card`, `AuthoritativeStatus.qRoleName_distinct` | machine-checked |
| `x` vs `X` | `SemanticFirewalls.smallX_bound_does_not_transfer`, `AuthoritativeStatus.smallX_ne_bigX`, `modulus_is_not_scale` | machine-checked |
| pointwise / packet / aggregate / global | `pointwise_not_aggregate`, `aggregate_not_pointwise`, **new** `PublicTree20260901.packetwise_not_aggregate` | machine-checked |
| C0 finite / analytic / physical | `AuthoritativeStatus.c0_levels_have_distinct_status` | machine-checked |
| Ω plain L², weighted divisor, shared-gcd, Perron | `AuthoritativeStatus.omega_norms_are_four_separate_pins` (labels) + **new** `PublicTree20260901.plain_l2_ne_weighted_l2` (quantitative countermodel) | machine-checked |
| local 287 Type-II vs Möbius-level vs classical | `AuthoritativeStatus.typeII_names_have_distinct_status` | machine-checked |
| branch vs global coverage | `SemanticFirewalls.branch_coverage_not_global`, `AuthoritativeStatus.coverage_scopes_distinct` | machine-checked |
| `WindowPairSupply` as compiler input | `AuthoritativeStatus.windowPairSupply_is_not_proved` + **new** `supply_is_input_not_output`, `closureInputs_threshold_ge_three`, `windowPairSupply_forces_large_primePowers` | machine-checked |
| `Gap2CE` vs exact `Erdos287Counterexample` | `SemanticFirewalls.gap2CE_firewall` with countermodel `{1}` | machine-checked |
| interface ≠ theorem | **new** `interface_status_not_theorem`, `analytic_nodes_not_kernelProved` | machine-checked |

Items previously carried by prose alone and now backed by a kernel-checked guard: the
Ω-weighting distinction, the packet-vs-aggregate distinction, the "an implication does not
close its target" rule, and the non-vacuity of the closure input.

## CURRENT FORMAL FRONTIER (node classification)

Classification lives in Lean (`PublicTree20260901.nodeStatus`, `nodeKind`), so it cannot
drift from prose:

| Node | Kind | Status |
|---|---|---|
| `Erdos287Statement` | public statement | open |
| `Erdos287SeqStatement` | public statement | open |
| statement equivalence | finite theorem | kernel-proved |
| end-to-end compiler | end-to-end compiler | kernel-proved |
| `WindowPairSupply` | supply input | open |
| finite range `3 ≤ M ≤ 4·10⁹` | finite theorem | kernel-proved |
| window-certificate engine | finite theorem | kernel-proved |
| top-layer congruence package | finite theorem | kernel-proved |
| prime blockers | finite theorem | kernel-proved |
| Sophie interface | finite theorem | kernel-proved |
| banked local analytic interfaces | local analytic interface | conditional source interface |
| source-normalisation interfaces | source normalisation | conditional source interface |
| naive full-CRT signless-pair DFT | local analytic interface | retracted |
| old local scalar route | local analytic interface | superseded |

Exactly seven nodes are kernel-proved (`kernelProved_node_count`); no node of analytic kind
is kernel-proved (`analytic_nodes_not_kernelProved`). Nothing about a final b-diagonal
closure, an Ω proof-local reconstruction, a total Perron ledger or a local analytic kernel
closure is promoted here: no literal theorem of that kind exists in the public tree, so no
such node is listed as anything but conditional/open.

## DEPENDENCY DAG (terminal node `Erdos287Statement`)

Edges `a → b` mean "closing `a` requires `b`" (`PublicTree20260901.dependsOn`), proved
acyclic by the explicit rank function (`dependsOn_rank_decreasing`, `dependsOn_irrefl`), with
`erdos287Statement_terminal` recording that no node other than its own equivalent ordered
restatement depends on the statement.

```
Erdos287SeqStatement  ──(equivalent to)──►  Erdos287Statement
                                              │
                        ┌─────────────────────┴────────────────────┐
                        ▼                                          ▼
              end-to-end compiler  [kernel-proved]        WindowPairSupply  [OPEN]
                        │                                          │
        ┌───────────────┴───────────────┐                          ▼
        ▼                               ▼             banked local analytic interfaces
   finite range               window-certificate                [conditional]
  [kernel-proved]                    engine                          │
        │                        [kernel-proved]                     ▼
        └──────────────►                │             source-normalisation interfaces
                                        ▼                        [conditional]
                          top-layer congruence package
                                 [kernel-proved]
```

Separately marked: finite theorems (finite range, window engine, top layer, prime blockers,
Sophie interface); local analytic interfaces; source-normalisation interfaces;
`WindowPairSupply`; the final end-to-end compiler. **No node is labelled CLOSED because an
implication theorem exists.**

## FILES ADDED

* `RequestProject/Erdos287/OrderedSequenceBridge.lean`
* `RequestProject/Status/PublicTreeReconciliation20260901.lean`
* `RequestProject/Status/AxiomAuditPublicTreeReconciliation20260901.lean`
* `ERDOS287_STATEMENT_EQUIVALENCE_2026-09-01.md`
* `ERDOS287_PUBLIC_FORMAL_RECONCILIATION_2026-09-01.md` (this file)

## FILES MODIFIED

* `RequestProject/Main.lean` — three appended `import` lines only (no reordering, no
  deletion). This is the minimal mechanical repair needed for the new modules to be part of
  the default build target.

## FILES DELETED

none.

## STOP
