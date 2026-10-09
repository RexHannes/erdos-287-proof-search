import RequestProject.Erdos287.AnchoredV2.FeedbackEdge
import RequestProject.Erdos287.AnchoredV2.BlockCut
import RequestProject.Erdos287.AnchoredV2.CactusMessage
import RequestProject.Erdos287.AnchoredV2.AffineNormalForm
import RequestProject.Erdos287.AnchoredV2.ThetaFirewall
import RequestProject.Erdos287.AnchoredV2.TrackedKernel
import RequestProject.Erdos287.AnchoredV2.UnitSubsetSum
import RequestProject.Erdos287.AnchoredV2.CoupledCharge
import RequestProject.Erdos287.AnchoredV2.CoupledBatchSupply
import RequestProject.Erdos287.AnchoredV2.FiniteExtension
import RequestProject.Erdos287.AnchoredV2.Capacity
import RequestProject.Erdos287.AnchoredV2.CapacityCertificate
import RequestProject.Erdos287.AnchoredV2.CapacityGap
import RequestProject.Erdos287.AnchoredV2.Level2
import RequestProject.Erdos287.AnchoredV2.RouteBridge
import RequestProject.Erdos287.AnchoredV2.Reconciliation
import RequestProject.Erdos287.AnchoredV2.AxiomAudit

/-!
# Erdős #287 — Anchored V2 aggregator

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Append-only extension of the Anchored route.  Route S, Route D and Anchored V1 are untouched;
the certified finite frontier is unchanged and is not extended here.

Contents:

* exact feedback-edge reduction with the `2 ^ β` branch bound and the `β = 2` four-test
  corollary (`FeedbackEdge.lean`);
* exact block-cut / cactus message solver (`BlockCut.lean`, `CactusMessage.lean`);
* affine path normal form and the integral root progression (`AffineNormalForm.lean`);
* the theta / bicyclic logical firewall (`ThetaFirewall.lean`);
* the tracked-prime kernel, its feasibility and its monotonicity (`TrackedKernel.lean`);
* the unit-list subset-sum theorem and the coupled `2^e × p` charge theorem
  (`UnitSubsetSum.lean`, `CoupledCharge.lean`);
* the finite coupled-batch supply record, the asymptotic-supply firewall and the finite coupled
  extension theorem (`CoupledBatchSupply.lean`, `FiniteExtension.lean`);
* the weighted capacity function, the negative capacity certificate, and the capacity
  incompleteness firewall (`Capacity.lean`, `CapacityCertificate.lean`, `CapacityGap.lean`);
* the Level-2 fractional interface (`Level2.lean`);
* the bridges to the actual anchored kernels and the new explicit open owners
  (`RouteBridge.lean`);
* the Anchored V2 ledger and the reconciliation with Route S, Route D and Anchored V1
  (`Reconciliation.lean`), and the axiom audit (`AxiomAudit.lean`).
-/
