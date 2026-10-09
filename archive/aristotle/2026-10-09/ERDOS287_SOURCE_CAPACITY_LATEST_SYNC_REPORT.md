# Erdős #287 — source/capacity synchronisation report (checkpoint `SOURCE_CAPACITY_LATEST_v1`)

**Erdős #287 is OPEN here and is not claimed.**  This checkpoint is append-only: no existing
module, theorem statement or ledger value was altered.  One import line was added to
`RequestProject/Main.lean`.

## Files added

| file | contents |
|---|---|
| `RequestProject/Erdos287/FivePrimeSourceGeometry.lean` | §65 one-low/four-high five-prime source geometry |
| `RequestProject/Erdos287/DirectedSelbergFiniteAlgebra.lean` | §66 finite algebra of the directed upper sieve, exact rational `T_box` comparisons |
| `RequestProject/Erdos287/HighXConsumerLedger.lean` | §67 high-`X` consumer ledger, `CHEAP/SIGNED/HARD` classification |
| `RequestProject/Erdos287/PhysicalK1Owner.lean` | §68 corrected quantitative physical `k = 1` owner |
| `RequestProject/Erdos287/CurrentStatusLatest.lean` | §69 authoritative status aggregator, DAG, minimal open cut set |

File modified: `RequestProject/Main.lean` (one added import).

## Build and trust audit

* full `lake build`: **PASS** (8502 jobs, 0 errors);
* `#print axioms` on every principal new theorem: only `propext`, `Classical.choice`,
  `Quot.sound` (three depend on `propext` alone);
* no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `@[implemented_by]` or
  `opaque` in any new file.

## Conventions fixed by §65 (read before using the numbers)

A cell carries one low exponent `a` and four high exponents `h i`, with
`0 < a ≤ 1/10`, `1/5 ≤ h i ≤ 3/10`, `a + Σ h i = 1`.  The low prime is *pinned* to the fixed
side, so a divisor assignment is a subset `S` of the four high primes with exponent
`σ S = Σ_{i∈S} h i`.  With window half-width `δ` and collar half-width `δ'`
(`0 < δ < δ' ≤ 1/10`):

```
N1 = #{S : 1/2 − δ' ≤ σ S < 1/2 − δ}     (lower collar, half-open)
N2 = #{S : 1/2 − δ  ≤ σ S ≤ 1/2 + δ}     (product window, closed)
N3 = #{S : 1/2 + δ  <  σ S ≤ 1/2 + δ'}   (upper collar, half-open)
H  = N2 − N1 − N3
```

## Kernel-proved at this checkpoint

* `H_def`, `three_counts_le_sixteen`, `H_abs_le_sixteen` — the divisor-assignment formula and
  unconditional bounds (the three labelled regions are pairwise disjoint).
* `balanced_counts_window / _collar / _outside` — the exact chamber values of `(N1,N2,N3)`,
  i.e. the positive chamber (`a ≤ 2δ`: `(0,6,0)`), the negative chamber (`2δ < a ≤ 2δ'`:
  `(6,0,0)`) and the inert chamber (`a > 2δ'`), with the boundaries `a = 2δ`, `a = 2δ'`.
* `signSeparation_balanced` — `N1 + N3 > 0 → N2 = 0` on the balanced chamber.
* `straddle_witness` — an explicit legal *unbalanced* cell with `N1 > 0` **and** `N2 > 0`:
  the balanced hypothesis in sign separation is necessary, not cosmetic.
* `H_mem_balanced`, `H_abs_le_six_balanced` — `H ∈ {−6, 0, +6}` on the balanced chamber.
* `plusSix_cell_legal`, `plusSix_cell_counts`, `plusSix_cell_H` — the exact `+6` cell
  (`a = 1/50`, `h ≡ 49/200`, `δ = 1/20`, `δ' = 1/10`), `H = +6` exactly.
* `separationCost_le_six`, `plusSix_separationCost` — separation-cost certificate `≤ 6`,
  exactly `6` on the physical cell.
* `plusSix_representation_exact` — representation error `= 0`: the box is exactly `6·v`.
* `prodBox_injective`, `fivePrimeBox_unique_factorisation` — unique factorisation in disjoint
  labelled prime boxes.
* `G_pos`, `capacity_pos`, `quadraticForm_ge_inv_capacity`, `quadraticForm_optimal`,
  `selberg_optimum_of_diagonalisation`, `G_mono`, `capacity_antitone`,
  `prime_le_sqrt_of_proper_power`, `allocation_eq_capacity_div_comparison` — the finite
  Selberg algebra: the optimum on the normalised simplex (`λ₁ = 1`) is exactly the capacity
  `1/G`, capacities are monotone, proper prime powers are square-root-thin, and
  `6.3e−7 / 0.3 = 2.1e−6` exactly.
* `availableLeakageBudget_le_transferred`, `availableLeakageBudget_antitone_in_costs`,
  `fits_mono`, `box_allocation_fits_of_budget`, `box_allocation_not_fits_of_small_budget`,
  `early_slab_budget_too_small`, `allocation_verdict_undecided`, `cheap_requires_affordable`,
  `cheap_requires_decision`, `plusSix_not_cheap_yet` — the high-`X` ledger arithmetic and the
  source-union classification with its proof obligation attached.
* `centredWeighted_full_period_vanishes`, `exists_physicalK1_budget`,
  `physicalK1Budget_mono`, `physicalK1_consumer_bound`, `refuted_targets_not_reused` — the
  corrected `k = 1` owner.
* `physicalK1_of_perConductor`, `constantWeight_centred_bound`, `constantWeight_physicalK1`,
  `k1_open_content_is_nonconstant_weights` — narrowing of the `k = 1` node: the owner splits
  over conductors, and the **constant-weight** case is closed outright with the
  `X`-independent constant `centredBudget`, so the open content is exactly the per-conductor
  bound for *non-constant* true source weights.
* `u2_reconciliation_pending`, `cutSet_all_open`, `cutSet_prerequisites_closed`,
  `erdos287_needs_cutSet`, `latest_open_frontier`, `banked_layers_preserved_latest`,
  `k1_owner_replacement`, `allocation_affordability_open`, `tBox_bound_is_conditional`.

## Conditional (not kernel-proved)

* `T_box_bound_of_capacity` and `T_box_ratio_bound` are **deterministic bridges**: they prove
  `|T| ≤ 6.3e−7·W` from a capacity input `A ≤ W/G` with `G ≥ 9523810` and separation cost
  `≤ 6`, and `|T/B| ≤ 2.1e−6` from the prime comparison `B ≥ 0.3·W`.  The capacity estimate
  and the prime comparison are hypotheses; they are **not** proved here and no external
  prime estimate was introduced as an axiom.  Status: `CONDITIONAL_ANALYTIC`.

## Not done / not claimed

* The continuous one-low/four-high integral is **not** kernel-proved; only the finite
  exponent-chamber geometry above is.  The remaining analytic proposition is precisely a
  region-level directed-sieve bound over the source union.
* No theorem asserts that every character twist of the box is small (the arbitrary-log
  Type-II and character-enlarged claims stay banked as FALSE).
* The `U2` finite project was **not supplied**; nothing was invented for it.

## Minimal open cut set (see `latestCutSet`)

1. `Erdos287.Effectivity.PhysicalK1Budget b` for a ledger-admissible `b` — the quantitative
   physical `k = 1` owner (bounded source weights, physical hyperbola windows, correct
   centring).  Consumer: `physicalK1_consumer_bound` → the high-`X` owner ledger.  Narrowed
   form after §68.6: a per-conductor bound `|∑_{s∈[A,B)} w(s)(K_ℓ(s,z) − mean_ℓ(z))| ≤ c ℓ·X`
   for *non-constant* bounded weights, with `∑_ℓ c ℓ` ledger-admissible (the constant-weight
   case is already closed).
2. `Erdos287.HighX.Fits L boxAllocationRequest` for the true ledger `L` — affordability of
   the `2.1e−6·B_prime` allocation.  Consumer: the `CHEAP` classification of the `+6` cell.
3–10. `Ω(k)=2`, `Ω(k)=1`, EARLY_4490 residual, proper gamma, `S_live`, `R_012`, signed floor,
   final splice (unchanged owners, all `OPEN`).
