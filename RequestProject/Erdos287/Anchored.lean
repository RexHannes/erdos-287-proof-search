import RequestProject.Erdos287.Anchored.Core
import RequestProject.Erdos287.Anchored.ReciprocalState
import RequestProject.Erdos287.Anchored.Fingerprint
import RequestProject.Erdos287.Anchored.PrimePowerLayer
import RequestProject.Erdos287.Anchored.ContactGraph
import RequestProject.Erdos287.Anchored.PathTransfer
import RequestProject.Erdos287.Anchored.ForestElimination
import RequestProject.Erdos287.Anchored.CycleElimination
import RequestProject.Erdos287.Anchored.CycleRank
import RequestProject.Erdos287.Anchored.BicyclicInterface
import RequestProject.Erdos287.Anchored.RouteBridge
import RequestProject.Erdos287.Anchored.Reconciliation
import RequestProject.Erdos287.Anchored.AxiomAudit

/-!
# Erdős #287 — Route A (anchored / contact-graph programme) aggregator

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This aggregator collects the append-only, *proof-side* anchored namespace.  It is a third
programme, kept disjoint from Route S and from the Direct Route D; the earlier ledgers, cut
sets and the certified finite frontier are re-checked unchanged in `Anchored/Reconciliation.lean`.

The certified endpoint of this route is `anchored_contact_endpoint`: for every finite contact
instance, satisfiability is exactly decidable, forest and isolated-cycle components are
decided exactly, and every remaining component reduces by exact leaf eliminations to a finite
leafless branching kernel.  The **global rejection of all branching kernels is `OPEN`**, and
its unconditional form is refuted here.
-/
