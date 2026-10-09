# Erdős #287 — Direct Reciprocal route (Route D): append-only formal sync

**Erdős #287 is OPEN and is not claimed.**  Nothing in this synchronisation proves the problem,
and no research-report conclusion has been imported as a theorem.

## Mode

Append-only on the pinned toolchain.  No existing module, theorem statement, theorem name or
ledger value was altered; the only edit to an existing file is one added import line in
`RequestProject/Main.lean`.  No custom axiom, `sorry`, `admit`, `native_decide`, `unsafe`,
`@[implemented_by]` or `opaque` was introduced.

## Files added

New namespace `Erdos287.Direct`, aggregator `RequestProject/Erdos287/Direct.lean`, modules under
`RequestProject/Erdos287/Direct/`:

| module | content |
|---|---|
| `Core.lean` | interval, Boolean selection, selected set, reciprocal sum, endpoint pin, no-two-consecutive-omissions, exact Route-D counterexample predicate, both bridges to `Erdos287Counterexample` |
| `ReciprocalCompiler.lean` | ambient / selected / free LCMs, exact cleared-denominator compiler (equivalence), empty-subset consistency, `0 ∉ I` firewall |
| `RawMask.lean` | largest prime factor, raw mask `F`, augmented mask `F_aug`, `n = d·r` factorisation with `d ≤ 136`, uniqueness for `M ≥ 18632`, neighbour/path consequences, mask-count interface |
| `BoundaryKernel.lean` | kernel variables, forced-zero / forced-positive pins, feasibility, pin disjointness, forced neighbours, restriction bridge (proved), extension interface (open), top prime-power congruence bridges |
| `LCMCarry.lean` | `L_N = lcm(1..N)`, `p^e ∣ L_N ↔ p^e ≤ N`, `L_N = J_N·L_{N-1}` with `J_N = p` at prime powers and `1` otherwise, exact layer quotients, fibrewise carry aggregation, descending recurrence |
| `PathPolynomial.lean` | physical path polynomial, coefficient formula, **exact reciprocal target theorem**, path recurrence `F_i = F_{i-1} + X^{w_i}F_{i-2}`, product factorisation across separated components |
| `LargePrimeCompletionFinite.lean` | binary subset-sum counts in `ZMod q`, exact additive-character identity, all-target sufficient condition, reciprocal exponential-sum interface and its consumer |
| `SparseSubreservoir.lean` | monotonicity, information-theoretic floor `q ≤ 2^{|C|}`, sparse claim (open) and its reduction to an exponential-sum bound on the sparse set |
| `ProtectedSwitches.lean` | `1/(6k)=1/(10k)+1/(15k)`, carry neutrality under `30k ∣ D` (+ firewall), signed increment, `ProtectedSwitch` predicate, endpoint/isolation/tracked-statistic preservation, exact value shift |
| `TargetTuningFinite.lean` | finite greedy-crossing lemma, four named analytic interfaces, deterministic straddling bridge, straddling ≠ exactness firewall |
| `AbsorberInterfaces.lean` | `D_buf`, `b_buf`, necessary lattice conditions, `ExactSignedAbsorber` predicate (**not inhabited**, OPEN) |
| `CurrentStatus.lean` | Route-D evidence taxonomy, nodes, evidence classes, dependency graph, Route-D cut, independence recorded `unknown` |
| `Reconciliation.lean` | Route-S ledger preservation, no cross-route discharge, proved cross-route bridges, finite-frontier integrity, hostile audit, axiom audit |

## Strict final output

* **PREVIOUS FORMAL BANK:** PRESERVED (`routeS_ledger_preserved`, `routeS_cutSet_unchanged`).
* **FULL LAKE BUILD:** PASS — 8516 jobs, 0 errors.
* **AXIOM AUDIT:** every principal new theorem depends only on `propext`, `Classical.choice`,
  `Quot.sound` (two depend on none, two on `propext, Quot.sound` only).  No `sorryAx`, no custom
  axiom.
* **NEW DIRECT ROUTE MODULES:** the thirteen modules listed above plus the aggregator.
* **DIRECT CORE:** kernel proved, including both bridges to the exact #287 predicate.
* **FINITE FOURIER ALL-TARGET LEMMA:** kernel proved (`char_sum_identity`,
  `subsetSumCount_pos_of_bound`); the exponential-sum bound is an explicit interface, not an axiom.
* **SPARSE SUBRESERVOIR:** OPEN — monotonicity, the floor `q ≤ 2^{|C|}` and the reduction to an
  exponential-sum bound on the sparse set are kernel proved; the claim is not inhabited.
* **LCM CARRY IDENTITIES:** kernel proved.  No complexity claim.
* **PATH POLYNOMIAL EXACT TARGET:** kernel proved, with recurrence and product factorisation.
  The exact cut formula was not attempted.
* **VALUE-PRESERVING SWITCH:** kernel proved; carry neutrality only under `30k ∣ D`, with a
  counterexample when that fails.
* **VALUE-MOVING SWITCH:** kernel proved from the full local `ProtectedSwitch` predicate.
* **TARGET-TUNING BRIDGE:** kernel conditional on `CoarseSwitchSupply`, `FineSwitchSupply`,
  `HarmonicInterior`, `SparseRepairCost`.
* **EXACT ABSORBER:** OPEN; only the necessary lattice conditions are proved.
* **ANALYTIC INTERFACES:** `ReciprocalExpSumInterface` (external published, unformalised),
  `MaskCardInput` (external counting input), `KernelExtensionInterface` (open — and *refutable*
  for an explicit kernel), `CoarseSwitchSupply` / `FineSwitchSupply` / `HarmonicInterior` /
  `SparseRepairCost` (open).  None is an axiom.
* **FINITE FRONTIER:** exactly the existing certified ceiling `67108856338751594`; `U2` remains
  `pendingExternalImport`; Route D adds no finite exclusion node at all.
* **ROUTE S:** old cut set preserved verbatim (ten nodes, same order, all open).
* **ROUTE D:** ledger `directEvidence`, cut
  `maskSurvivorClassification, switchSupply, kernelExtension, sparseSubreservoir,
  exactSignedAbsorber, fullAssembly`; all open; mutual independence recorded `unknown`.
* **CROSS-ROUTE BRIDGES:** exactly two, both proved — Route-D source into
  `Erdos287Counterexample`, and the elementary top-layer congruence for Route-D counterexamples.
* **HOSTILE AUDIT:** four refutations proved — conditional survivor ⇏ actual survivor;
  independent feasibility ⇏ common feasibility; approximate straddling ⇏ exactness;
  value-moving switch ⇏ tracked neutrality without the agreement hypothesis.
* **ERDŐS #287:** OPEN in both ledgers (`erdos287_open_in_both_routes`).

## Next-generation state

Route D's frontier is: (D1) classify or exclude augmented-mask/kernel survivors; (D2) the
analytic activation/supply interfaces (switch supply, exponential-sum input); (D3) the exact
signed absorber; (D4) the full exact assembly.  D1–D4 are *not* certified independent.  Route S
is untouched and keeps its own ten-node cut.
