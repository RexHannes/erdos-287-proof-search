# Erdős #287 — Anchored V4: ENTRY, exact endgame, reconciliation report

**Erdős #287 status: OPEN.**  Nothing in this layer proves or refutes the conjecture.
Anchored V2 and Anchored V3 are untouched.

---

## A. Files added

```
RequestProject/Erdos287/AnchoredV4.lean            (aggregator)
RequestProject/Erdos287/AnchoredV4/
  PrimePowerHeight.lean
  DoubledLattice.lean
  GuardGeometry.lean
  Entry.lean
  DescentState.lean
  PrimePowerDescent.lean
  GuardedReservoir.lean
  FourierAbsorber.lean
  ConditionalExactEndgame.lean
  EntryColumns.lean
  TransitionSystem.lean
  EntryMobility.lean
  EntryObstructions.lean
  Reconciliation.lean
  OriginalBridge.lean          (added to the plan: bridge to the public #287 statement)
  OpenOwners.lean
  AxiomAudit.lean
```

## B. Imports changed

Exactly one line was added to an existing file:

```
RequestProject/Main.lean :  import RequestProject.Erdos287.AnchoredV4
```

Frozen and untouched (verified by `git status` / `git diff`):
`RequestProject/Erdos287/AnchoredV2/**`, `RequestProject/Erdos287/AnchoredV3/**`,
`RequestProject/Erdos287/AnchoredV3.lean`.  No V2/V3 theorem was edited, renamed, weakened,
re-proved or re-stated; V3 results are imported and used.

## C. Build

```
lake build      →  Build completed successfully (8584 jobs)
```

All normal project targets build, including `RequestProject.Main`.

## D. Placeholder audit

Repository search over the whole V4 layer for
`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `opaque`, `implemented_by`:

* **no declarations** of any of these forms;
* the only textual hits are inside doc-comments that *state* their absence
  (`AxiomAudit.lean`, `OpenOwners.lean`, `PrimePowerDescent.lean`).

Verdict: **PASS**.

## E. Axiom audit

`AxiomAudit.lean` runs `#print axioms` on every principal V4 theorem.  Result for all of them:

```
[propext, Classical.choice, Quot.sound]        (most theorems)
[propext, Quot.sound]                          (some finite/decidable statements)
does not depend on any axioms                  (the ledger theorems open_owners, false_shortcuts)
```

No additional axiom of any kind occurs.  Verdict: **PASS**.

## F. Theorem ledger

| THEOREM | FILE | STATUS | UNCOND./COND. | DEPENDENCIES | AXIOMS | ROLE |
|---|---|---|---|---|---|---|
| `prime_pow_dvd_L_iff` | PrimePowerHeight | proved | unconditional | mathlib | std | exact `p`-adic description of `lcm(1..t)` |
| `normalizedHeight_le_iff_dvd_two_lcm` | PrimePowerHeight | proved | unconditional | mathlib | std | `n ∣ 2L(t) ↔ 𝔥(n) ≤ t` |
| `two_factor_essential`, `normalizedHeight_not_le_iff_dvd_lcm` | PrimePowerHeight | proved | unconditional | — | std | factor `2` is essential (firewall) |
| `den_two_mul_dvd_iff`, `den_two_mul_dvd_L_iff_normHeight` | DoubledLattice | proved | unconditional | height thm | std | the three equivalent denominator conditions |
| `doubled_lattice_regression`, `den_dvd_not_iff_den_two_mul_dvd` | DoubledLattice | proved | unconditional | — | std | finite regression certificate `1/1056+1/1080` |
| `noAdjacent_of_all_even`, `NoAdjacent.subset`, `noAdjacent_insert_even_of_mask`, `noAdjacent_union_even_of_mask` | GuardGeometry | proved | unconditional | — | std | exact `no-00` geometry |
| `wordSum_insert`, `wordSum_erase`, `wordSum_union` | GuardGeometry | proved | unconditional | — | std | exact word-value bookkeeping |
| `Entry.height_gt`, `Entry.noAdjacent_union_safe`, `Entry.normHeight_den_init_le` | Entry | proved | unconditional | height thm | std | consequences of the exact ENTRY datum |
| `entryDegenerate` | Entry | proved | unconditional | — | std | consistency witness (degenerate only) |
| `DescentStep.next_value`, `next_component_lower`, `next_fresh` | DescentState | proved | unconditional | guard geometry | std | exact descent bookkeeping, strict height drop, no reuse |
| `descent_terminates`, `descent_normHeight_le` | PrimePowerDescent | proved | conditional on `DescentSupply` | descent data | std | well-founded descent to the floor height |
| `GuardedReservoir.noAdjacent_absorb`, `wordSum_absorb`, `mask_absorb` | GuardedReservoir | proved | unconditional | guard geometry | std | absorption preserves all invariants |
| `positive_mass_not_exact_coverage` | GuardedReservoir | proved | unconditional | — | std | firewall: mass ≠ coverage |
| `exact_absorption_iff_weight_subsetSum` | FourierAbsorber | proved | unconditional | — | std | absorption = integer subset sum |
| `exact_absorption_of_congruence` | FourierAbsorber | proved | conditional (explicit finite hyps) | above | std | no-wraparound firewall (exact vs mod) |
| `fourier_count_identity` | FourierAbsorber | proved | unconditional | mathlib roots of unity | std | exact finite Fourier counting identity |
| `congCount_pos_of_dominance` | FourierAbsorber | proved | conditional (dominance inequality) | identity | std | spectral dominance ⇒ congruence solution |
| `exact_absorption_of_fourier_dominance` | FourierAbsorber | proved | conditional (all inputs visible) | the three above | std | exact absorber interface |
| `entry_to_low_height` | ConditionalExactEndgame | proved | conditional on `DescentSupply` | descent | std | stage 1 of the endgame |
| `low_height_to_exact_absorb` | ConditionalExactEndgame | proved | conditional on exact absorption | reservoir | std | stage 2 of the endgame |
| `conditional_entry_to_exact_one` | ConditionalExactEndgame | proved | conditional on both supplies | stages 1,2 | std | ENTRY + supplies ⇒ exact `S = 1` |
| `den_dvd_quotient_iff`, `descent_congruence_iff` | EntryColumns | proved | unconditional | — | std | descent move = exact integer congruence |
| `dvd_mul_iff_of_coprime`, `dvd_iff_forall_component` | EntryColumns / Reconciliation | proved | unconditional | — | std | component splitting of the global constraint |
| `TransitionSystem.solves_of_independent_repairs` | TransitionSystem | proved | unconditional | — | std | when a rowwise split is legitimate |
| `TransitionSystem.unsolvable_of_common_divisor` | TransitionSystem | proved | unconditional | — | std | dual/congruence obstruction certificate |
| `gcdWitnessSystem_unsolvable` | TransitionSystem | proved | unconditional | — | std | Route A obstruction: full lattice ≠ `0/1` hit |
| `descentStep_of_congruence` | TransitionSystem | proved | conditional (explicit congruence solution) | descent data, column arithmetic | std | reduces `SAFE_DESCENT_SUPPLY` to an exact subset-sum congruence |
| `coset_meets_subgroup_iff` | EntryMobility | proved | unconditional | mathlib | std | Route B exact intersection theorem |
| `mobility_targets_not_hit` | EntryMobility | proved | unconditional | — | std | firewall: many targets ≠ hit |
| `normHeight_le_self`, `Entry.Q_lt_mem`, `noAdjacent_card_bound`, `Entry.two_mul_card_le` | EntryObstructions | proved | unconditional | — | std | necessary conditions on any ENTRY |
| `mobility_preserves_doubled_lattice` | Reconciliation | proved | unconditional | V3 `den_dvd_Dcore` | std | V3 mobility respects the V4 lattice |
| `absorber_is_sumset_membership` | Reconciliation | proved | unconditional | absorber | std | V4 absorber has the V3 sumset shape |
| `noAdjacent_to_V3_no00` | Reconciliation | proved | unconditional | V3 `No00` | std | V4 guard ⇒ frozen V3 guard predicate |
| `v4_firewalls_in_force` | Reconciliation | proved | unconditional | the four firewalls | std | audited list of killed shortcuts |
| `final_configuration_is_counterexample` | OriginalBridge | proved | unconditional | guard geometry | std | **bridge to the original #287 statement** |
| `conditional_entry_gives_counterexample` | OriginalBridge | proved | conditional on both supplies | endgame + bridge | std | what a future supply proof would buy |
| `no_entry_supply_of_no_counterexample` | OriginalBridge | proved | unconditional | bridge | std | contrapositive reading |
| `OpenOwners.entry_to_original_287_bridge` | OpenOwners | proved | unconditional | bridge | std | discharges the bridge owner |
| `OpenOwners.open_owners`, `false_shortcuts` | OpenOwners | proved | unconditional | — | none | machine-readable owner ledger |

`std` = `propext, Classical.choice, Quot.sound` (or fewer).

## G. Dependency DAG

```
V2 (frozen)
 ↓
V3 (frozen): global neutrality · column compiler · packets · Boolean column lattice · mobility
 ↓                                  ↘ (used, never re-proved)
V4 PrimePowerHeight ──► DoubledLattice ──► GuardGeometry ──► Entry
                                                   │            │
                                                   ▼            ▼
                                            DescentState ──► PrimePowerDescent
                                                                │
                                      GuardedReservoir ──► FourierAbsorber
                                                                │
                                                ConditionalExactEndgame
                                                                │
                                   EntryColumns ─► TransitionSystem ─► EntryMobility
                                                                │            │
                                                          EntryObstructions  │
                                                                └─► Reconciliation (V3 ↔ V4)
                                                                        │
                                                                 OriginalBridge
                                                                        │
                                                            OpenOwners · AxiomAudit
```

Remaining OPEN premises (and only these):

```
ENTRY_EXISTENCE
SAFE_DESCENT_SUPPLY                (∀ states above the floor, a valid descent move exists)
GUARDED_ABSORBER_ANALYTIC_SUPPLY   (∀ low-height states, a guarded reservoir absorbs S − 1 exactly)
```

## H. What was genuinely proved

1. The normalized prime-power height and the exact lattice theorem `n ∣ 2L(t) ↔ 𝔥(n) ≤ t`,
   **with** the proof that the factor `2` is not removable.
2. The doubled denominator lattice, its exchange lemma, and the finite regression certificate
   `1/1056 + 1/1080 = 89/47520` with `den(2Δ) ∣ L(30)` and `den(Δ) ∤ L(30)`.
3. The complete finite `no-00` guard geometry and exact word-value bookkeeping.
4. The exact `ENTRY` structure (all conditions explicit, no "large primes handled" hand-waving),
   with proved necessary conditions: every omitted position exceeds `Q`, and the omission set has
   at most `(M − aM)/2` elements.
5. Well-founded prime-power descent: a genuine `Nat` descent argument, preserving interval, guard,
   mask discipline, freshness and the doubled denominator condition.
6. The absorber split into (i) an exact lattice reduction to integer subset sums, (ii) an exact
   no-wraparound upgrade from congruence to equality, (iii) the **exact finite Fourier counting
   identity** and the dominance criterion.  Positive reservoir mass is formally shown *not* to
   imply coverage.
7. The exact translation of one descent move into an integer congruence, the component splitting,
   and the finite global transition system with a dual obstruction certificate.
8. Route A refuted in the general model (full lattice, no `0/1` solution); Route B given its only
   legitimate exact form (coset ∩ subgroup); the mobility-abundance fallacy refuted by a witness.
9. `descentStep_of_congruence`: a descent move exists as soon as a guarded, fresh, even position
   set solves the exact integer congruence — so `SAFE_DESCENT_SUPPLY` is *exactly* a subset-sum
   problem over the guarded reservoir, i.e. the same technology as the absorber.
10. **The bridge to the original Erdős #287 statement**: any final V4 configuration
   (interval word, non-adjacent omissions, selected endpoints, value exactly `1`) *is* a set of
   distinct integers `> 1` with reciprocal sum `1` and all consecutive gaps `≤ 2`.

## I. What remained conditional

* `conditional_entry_to_exact_one` and `conditional_entry_gives_counterexample` are implications
  from `ENTRY`, `DescentSupply` and `AbsorberSupply`.  None of the three is inhabited.
* `exact_absorption_of_fourier_dominance` is an implication from explicit finite hypotheses
  (lattice, no wraparound, spectral dominance).  Its asymptotic supply is open.

## J. Killed shortcuts (firewalls, all formally proved)

| shortcut | verdict | witness |
|---|---|---|
| `den(Δ) ∣ P` in place of `den(2Δ) ∣ P` | FALSE | `1/1056 + 1/1080` at `L(30)` |
| `n ∣ L(t) ↔ 𝔥(n) ≤ t` (no factor 2) | FALSE | `32`, `t = 16` |
| positive reservoir mass ⇒ exact coverage | FALSE | reservoir `{4}`, target `1/8` |
| `gcd = 1` / global column surjectivity ⇒ hit | FALSE | effects `{2,3}` mod `7`, target `1` |
| many mobility targets ⇒ hit | FALSE | four targets mod `8` disjoint from `{0,4}` |
| rowwise neutrality necessary (V3) | FALSE (frozen V3) | re-checked, not revived |
| many packets ⇒ exact target hit (V3) | FALSE (frozen V3) | re-checked, not revived |

## K. ENTRY status

`ENTRY_EXISTENCE` is **OPEN**.  What is new:

* ENTRY is now an exact structure rather than a slogan, so a candidate can be checked mechanically;
* three proved necessary conditions constrain any candidate;
* the transition problem is now an exact finite congruence system, treated globally (never split
  into rows without the proved `solves_of_independent_repairs` hypotheses);
* Routes A, B and the mobility-abundance route are pinned down: A is refuted in the general model,
  B is reduced to an exact coset/subgroup intersection, abundance arguments are firewalled.

No route to ENTRY existence succeeded; no route was silently assumed.

## L. Bridge to the original problem

Proved (`final_configuration_is_counterexample`).  Consequently the programme is now a genuine
test of #287: either the two supplies plus ENTRY are established — which by the bridge yields an
actual counterexample — or #287 is true and, contrapositively, no ENTRY admits both supplies
(`no_entry_supply_of_no_counterexample`).  **No counterexample is constructed here.**
