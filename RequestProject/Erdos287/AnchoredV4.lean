import RequestProject.Erdos287.AnchoredV4.PrimePowerHeight
import RequestProject.Erdos287.AnchoredV4.DoubledLattice
import RequestProject.Erdos287.AnchoredV4.GuardGeometry
import RequestProject.Erdos287.AnchoredV4.Entry
import RequestProject.Erdos287.AnchoredV4.DescentState
import RequestProject.Erdos287.AnchoredV4.PrimePowerDescent
import RequestProject.Erdos287.AnchoredV4.GuardedReservoir
import RequestProject.Erdos287.AnchoredV4.FourierAbsorber
import RequestProject.Erdos287.AnchoredV4.ConditionalExactEndgame
import RequestProject.Erdos287.AnchoredV4.EntryColumns
import RequestProject.Erdos287.AnchoredV4.TransitionSystem
import RequestProject.Erdos287.AnchoredV4.EntryMobility
import RequestProject.Erdos287.AnchoredV4.EntryObstructions
import RequestProject.Erdos287.AnchoredV4.Reconciliation
import RequestProject.Erdos287.AnchoredV4.OriginalBridge
import RequestProject.Erdos287.AnchoredV4.OpenOwners
import RequestProject.Erdos287.AnchoredV4.AxiomAudit

/-!
# Erdős #287 — Anchored V4 aggregator

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Strictly append-only layer on top of the frozen Anchored V2 and Anchored V3 banks.  Nothing in
V2 or V3 is edited, renamed, weakened or re-proved; the V3 firewalls remain in force and are
re-checked in `Reconciliation.lean`.

New unconditional bank:

* the normalized prime-power height `normHeight` and the exact characterization
  `n ∣ 2 * L t ↔ normHeight n ≤ t`, with the explicit proof that the factor `2` cannot be dropped
  (`PrimePowerHeight.lean`);
* the doubled denominator lattice `den (2 q) ∣ P ↔ den q ∣ 2 P`, and the finite regression
  certificate `1/1056 + 1/1080 = 89/47520` (`DoubledLattice.lean`);
* the finite `no-00` guard geometry: all-even omission sets are guarded, restoring a position can
  never create an adjacency, safe even centers and fresh even reservoirs preserve the guard, with
  exact word-value bookkeeping (`GuardGeometry.lean`);
* the exact `Entry` datum and its consequences (`Entry.lean`, `EntryObstructions.lean`);
* exact descent data and **well-founded** prime-power descent to any floor height
  (`DescentState.lean`, `PrimePowerDescent.lean`);
* the guarded reservoir, with the firewall that positive mass is not exact coverage
  (`GuardedReservoir.lean`);
* the exact finite Fourier counting identity for reservoir subset sums, the no-wraparound
  firewall, and exact absorption from spectral dominance (`FourierAbsorber.lean`);
* the exact translation of a descent move into an integer congruence, and the finite global
  transition system with its dual obstruction certificate (`EntryColumns.lean`,
  `TransitionSystem.lean`);
* the exact coset/subgroup intersection theorem for mobility (`EntryMobility.lean`);
* the **bridge** proving that any final V4 configuration is literally an Erdős #287 counterexample
  (`OriginalBridge.lean`).

Conditional interfaces (all premises visible, none inhabited):

* `conditional_entry_to_exact_one` — `ENTRY + DescentSupply + AbsorberSupply ⟹ S_final = 1`;
* `exact_absorption_of_fourier_dominance` — exact absorption from explicit finite hypotheses.

Remaining open owners: `ENTRY_EXISTENCE`, `SAFE_DESCENT_SUPPLY`,
`GUARDED_ABSORBER_ANALYTIC_SUPPLY` (`OpenOwners.lean`).
-/
