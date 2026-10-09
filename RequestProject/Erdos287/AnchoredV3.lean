import RequestProject.Erdos287.AnchoredV3.GlobalNeutrality
import RequestProject.Erdos287.AnchoredV3.OldEmptyNewHit
import RequestProject.Erdos287.AnchoredV3.ColumnZeroPatterns
import RequestProject.Erdos287.AnchoredV3.GlobalColumnCompiler
import RequestProject.Erdos287.AnchoredV3.ColumnPackets
import RequestProject.Erdos287.AnchoredV3.SupportMultiplicity
import RequestProject.Erdos287.AnchoredV3.ColumnLattice
import RequestProject.Erdos287.AnchoredV3.TargetMobility
import RequestProject.Erdos287.AnchoredV3.MobilityStructure
import RequestProject.Erdos287.AnchoredV3.AlignmentPolynomial
import RequestProject.Erdos287.AnchoredV3.FourierHitInterface
import RequestProject.Erdos287.AnchoredV3.BaselineCentrality
import RequestProject.Erdos287.AnchoredV3.ResonanceInterfaces
import RequestProject.Erdos287.AnchoredV3.ConditionalClosure
import RequestProject.Erdos287.AnchoredV3.OpenOwners
import RequestProject.Erdos287.AnchoredV3.Reconciliation
import RequestProject.Erdos287.AnchoredV3.AxiomAudit

/-!
# Erdős #287 — Anchored V3 aggregator

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Strictly append-only layer on top of the frozen Anchored V2.  Route S, Route D, Anchored V1 and
Anchored V2 are untouched; the certified finite frontier is unchanged and is **not** extended;
no new asymptotic prime theorem is declared; no #287 counterexample is inferred from any finite
rational certificate; no unproved analytic statement is turned into an axiom.

Contents:

* global multiplier neutrality, the rowwise ⇒ global implication, the finite witness that the
  converse fails, and the `D = D_core * U_mult` decomposition (`GlobalNeutrality.lean`);
* the exact old-empty / new-global-hit terminal certificate (`OldEmptyNewHit.lean`);
* column zero patterns with their exact integer weights and the complete fixed-bank global
  column compiler (`ColumnZeroPatterns.lean`, `GlobalColumnCompiler.lean`);
* column zero-sum packet extraction with the packet-abundance firewall (`ColumnPackets.lean`);
* the finite support-size / multiplicity skeleton and its OPEN analytic owner
  (`SupportMultiplicity.lean`);
* the Boolean column-lattice gcd theorem, its constructive telescoping certificate and its
  sharpness witness (`ColumnLattice.lean`);
* fixed-bank target mobility (`TargetMobility.lean`) and the distinctness / AP-free negative
  structure of the mobility family (`MobilityStructure.lean`);
* the exact combined terminal × mobility coefficient identity and the mobility congruence coset
  (`AlignmentPolynomial.lean`);
* the exponential-tilt / Fourier closure interface, the bounded-tilt / central-baseline
  interface and the resonance classification interface, all conditional
  (`FourierHitInterface.lean`, `BaselineCentrality.lean`, `ResonanceInterfaces.lean`);
* the conditional terminal closure dependency theorem (`ConditionalClosure.lean`);
* the actual remaining open owners (`OpenOwners.lean`), the append-only ledger
  (`Reconciliation.lean`) and the axiom audit (`AxiomAudit.lean`).
-/
