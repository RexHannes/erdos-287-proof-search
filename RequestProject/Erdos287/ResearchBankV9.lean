import RequestProject.Erdos287.ResearchBankV8
import RequestProject.Erdos287.ResearchBankV9.AffineContact
import RequestProject.Erdos287.ResearchBankV9.ArchitectureLimit
import RequestProject.Erdos287.ResearchBankV9.AsraCRT
import RequestProject.Erdos287.ResearchBankV9.AsraClearing
import RequestProject.Erdos287.ResearchBankV9.AsraInterfaces
import RequestProject.Erdos287.ResearchBankV9.AsraPrimeSlot
import RequestProject.Erdos287.ResearchBankV9.AsraZeroMode
import RequestProject.Erdos287.ResearchBankV9.CircularGraph
import RequestProject.Erdos287.ResearchBankV9.Gates
import RequestProject.Erdos287.ResearchBankV9.GcdClique
import RequestProject.Erdos287.ResearchBankV9.GraphLocalization
import RequestProject.Erdos287.ResearchBankV9.Occupancy
import RequestProject.Erdos287.ResearchBankV9.Splice
import RequestProject.Erdos287.ResearchBankV9.Ledger
import RequestProject.Erdos287.ResearchBankV9.AxiomAudit

/-!
# Erdős #287 — Research Bank V9 (aggregator)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN. This research bank does not
prove or disprove it.**

Strictly **append-only**: no declaration of `AnchoredV2`–`AnchoredV4`, `ResearchBankV5`–`ResearchBankV8`
is edited, renamed, moved, weakened or replaced; this layer only imports them.

No `sorry`, no new axiom, no `native_decide`/`bv_decide`, no `opaque`/`implemented_by`/`unsafe`.
External analytic statements appear only as explicit theorem hypotheses / structures that are
never inhabited.

## Contents
* `AffineContact` — 3B affine contact identity (a_j/g)F_i − (a_i/g)F_j = 1
* `ArchitectureLimit` — 3G single-contact architecture upper limit χ_f ≤ ρ+1 (combinatorial part)
* `AsraCRT` — 4A–4C polynomial-root CRT normalization, within-product collision zero, lcm main modulus + counterfixture
* `AsraClearing` — 4G rational-root bilinear clearing with base progression firewall
* `AsraInterfaces` — 4H/4I open ASRA interfaces (uninhabited parameters) and conditional assembly
* `AsraPrimeSlot` — 4D/4E prime-slot truncation identity, upper-sieve step, large-overlap decomposition with external Shiu input
* `AsraZeroMode` — 4F small-overlap zero-mode density and centred kernel; external ratio-BV interface
* `CircularGraph` — 3C circular annulus graph G(n,r): α = r+1, fractional colouring certificate n/(r+1)
* `Gates` — 3E exact gates G(13,3), G(145,38), 26/7 < 145/39, 7/13 − 78/145 = 1/1885, θ-gate equivalence, rational bound on e
* `GcdClique` — 3A prescribed-shape gcd-clique elementary CRT core (gcd(C+b_i,C+b_j)=|b_i−b_j|); separated from PrimeValuesOnClique
* `GraphLocalization` — 3F deterministic graph-localization → no #287 representation implication
* `Occupancy` — 3D graph-selective occupancy theorem
* `Splice` — 5 conditional eventual exclusion and finite splice; M_an = none, splice BLOCKED
* `Ledger` — 6 epoch-aware V9 ledger; no CLOSED row; no ledger path closes Erdős #287
* `AxiomAudit` — `#print axioms` for every V9 theorem
-/
