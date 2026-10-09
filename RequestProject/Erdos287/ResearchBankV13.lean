import RequestProject.Erdos287.ResearchBankV12
import RequestProject.Erdos287.ResearchBankV13.FiniteRepresentationModel
import RequestProject.Erdos287.ResearchBankV13.PrimeLayer
import RequestProject.Erdos287.ResearchBankV13.HarmonicTwoHole
import RequestProject.Erdos287.ResearchBankV13.AdjacentPrimeLayer
import RequestProject.Erdos287.ResearchBankV13.PrimeCertificates
import RequestProject.Erdos287.ResearchBankV13.FiniteIntervalCertificate
import RequestProject.Erdos287.ResearchBankV13.DemonstrationPayload
import RequestProject.Erdos287.ResearchBankV13.AuditedEndpoint
import RequestProject.Erdos287.ResearchBankV13.UpdatedSplice
import RequestProject.Erdos287.ResearchBankV13.EffectiveFrontier
import RequestProject.Erdos287.ResearchBankV13.Ledger
import RequestProject.Erdos287.ResearchBankV13.AxiomAudit

/-!
# Erdős #287 — Research Bank V13 (aggregator): finite interval certificate + updated splice

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN. This research bank does not
prove or disprove it.**

Strictly **append-only**: no pre-existing file is modified; this layer only imports earlier layers.

No `sorry`, no new axiom, no `native_decide`/`bv_decide`, no `opaque`/`implemented_by`/`unsafe`.
The audited 10^500 payload is **not present** in the workspace: `concreteFinitePayload =
.notSupplied`, no `auditedFiniteEndpoint` is defined.  No numerical `M_an` is available; the
decisive splice condition is `M_an ≤ U + 1`.

## Contents
* `FiniteRepresentationModel` — §18 `NoCounterexampleAt`, `NoCounterexampleUpTo` (exact type)
* `PrimeLayer` — §19 `L J`, `A J`, `primeLayer_exclusion`, kernel values
* `HarmonicTwoHole` — §20 `η = 685/252 < e`, harmonic tail, `two_hole_exclusion`, interval theorem
* `AdjacentPrimeLayer` — §21 Family A (`p = 2q+1`), Family B (`p = 4q+1`), outside good-prime half
* `PrimeCertificates` — §23 Proth / Pocklington soundness, checkers, fixtures
* `FiniteIntervalCertificate` — §22 generic certificate, soundness, record checker
* `DemonstrationPayload` — a small generated payload replayed by the checker (endpoint `< 10^61`;
  **not** the audited payload)
* `AuditedEndpoint` — §24–25 payload status NOT SUPPLIED, external metadata, firewalls (e), (f)
* `UpdatedSplice` — §26 `finite_eventual_splice`, exact `U+1` boundary, two finite routes
* `EffectiveFrontier` — §27–28 `current_M_an = none`, `effectiveOverlap`, updated block reason
* `Ledger` — V13 ledger, `v13_preserves_v12_ledger`, status ledger, regression fixtures
* `AxiomAudit` — `#print axioms` for every V13 theorem
-/
