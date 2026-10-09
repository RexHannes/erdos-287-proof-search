# Erdős #287 — Anchored exceptional core / contact-graph formal sync

**Erdős #287 is recorded `OPEN` and is not claimed.**  No research-report conclusion was
imported as a theorem, no custom axiom was introduced, and nothing in the existing bank was
weakened, renamed, replaced or silently discharged.

## 1. Mode

Append-only.  Route S and its ten-node cut, the complete Direct / Route-D programme (both
proved bridges, reciprocal compiler, raw-mask arithmetic, boundary kernel, LCM/carry algebra,
path polynomial, finite Fourier all-target lemma, sparse subreservoir interfaces, protected
switches, finite target tuning, absorber interfaces, `ExactSignedAbsorber` OPEN, the hostile
countermodels), the certified finite frontier `67108856338751594`, the pending U2 node and the
`OPEN` status of #287 are all preserved unchanged and are re-checked by theorem in
`RequestProject/Erdos287/Anchored/Reconciliation.lean`.

The new route is **proof-side** and is kept formally separate from Route D: it has its own
namespace, its own ledger and its own cut set, and no node of one route discharges a node of
another.

## 2. Files

New namespace `Erdos287.Anchored`, aggregator `RequestProject/Erdos287/Anchored.lean`, with

| module | content |
| --- | --- |
| `Anchored/Core.lean` | exact conventions: reciprocal sums (reusing the Route-D definition), ambient lcm, integral cofactor numerator, and the compiler identity `recipSum E = cofactorNum C E / lcmOf C` |
| `Anchored/ReciprocalState.lean` | anchored state `(C, P, N)`, allowed subsets, permitted value set, explicit zero state, `AnchoredFeasible`, and the exact reduced-numerator criterion for **every** prime |
| `Anchored/Fingerprint.lean` | finite fingerprint and the exact equivalence `feasible ↔ zero state allowed ∨ p ∣ F`; decidability |
| `Anchored/PrimePowerLayer.lean` | full prime-power layer condition ⟺ anchored valuation condition; `p ∣ c` retained (explicit witness); empty-subset firewall |
| `Anchored/ContactGraph.lean` | local contact relation of a layer (noncontact cofactors existentially quantified, full equation required), finite contact constraint system, exact decision procedure |
| `Anchored/PathTransfer.lean` | exact Boolean transfer along a contact path and its specification |
| `Anchored/ForestElimination.lean` | exact leaf elimination, termination, iterated peeling, forest decision |
| `Anchored/CycleElimination.lean` | exact decision of isolated cycle components |
| `Anchored/CycleRank.lean` | excess (cyclomatic count), invariance under peeling, excess of paths (`0`) and cycles (`1`), reduction to a leafless branching kernel |
| `Anchored/BicyclicInterface.lean` | the `OPEN` global rejection interface (not inhabited), its unconditional form refuted, and the endpoint theorem |
| `Anchored/RouteBridge.lean` | bridge to the elementary top-layer package and to the exact #287 counterexample predicate |
| `Anchored/Reconciliation.lean` | anchored ledger, preservation of the Route-S and Route-D ledgers, route independence, finite-frontier integrity |
| `Anchored/AxiomAudit.lean` | `#print axioms` on every principal new theorem |

One file modified: `RequestProject/Main.lean` — a single added import of the new aggregator.

## 3. Endpoint

`Erdos287.Anchored.anchored_contact_endpoint`: for every finite contact instance,

1. satisfiability is exactly decided by a finite procedure;
2. forest components (those peeling to an edgeless instance) are decided exactly by
   nonemptiness of the surviving unary domains;
3. isolated cycle components are decided exactly by the four-pair transfer criterion;
4. every remaining component reduces, by finitely many exact leaf eliminations, to a finite
   **leafless branching kernel**, with satisfiability preserved and still exactly decidable.

`anchored_endpoint_of_layerRel` records the same conclusion for instances whose edge relations
are realized by the anchored prime-power layer relations.

**The global rejection of all branching kernels is `OPEN`.**  It is stated as the
parameterised interface `BranchingKernelRejection` and deliberately not inhabited; its
unconditional form is *refuted* by an explicit satisfiable leafless instance of excess `2`.

## 4. Firewalls proved

* the empty subset is a genuine exception to the layer equivalence (`v_p(0) = 0`);
* the layer condition retains cofactors divisible by `p` (explicit witness `C = {2,3,6}`,
  `E = {2,6}`, `p = 2`), so no reduction to the unit-cofactor case is performed;
* the unconditional branching-kernel rejection is false.

## 5. Build and trust

* Full `lake build`: **PASS** (8530 jobs, 0 errors).
* `#print axioms` on every principal new theorem: only `propext`, `Classical.choice`,
  `Quot.sound`.
* No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `opaque` or
  `@[implemented_by]` in any new file.

## 6. Status after this run

* Route S: unchanged, cut open.
* Route D: unchanged, cut open, `ExactSignedAbsorber` OPEN.
* Route A (anchored): reciprocal state, fingerprint, prime-power layer, contact relation,
  forest elimination, cycle elimination, cycle rank and the top-layer bridge are
  `KERNEL-PROVED`; the branching-kernel rejection is `OPEN`; its unconditional form is
  `REFUTED`.
* Certified finite frontier: `67108856338751594`; U2 pending.
* **Erdős #287: OPEN.**
