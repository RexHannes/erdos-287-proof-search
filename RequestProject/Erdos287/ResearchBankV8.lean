import RequestProject.Erdos287.ResearchBankV7
import RequestProject.Erdos287.ResearchBankV8.ActiveResidueDP
import RequestProject.Erdos287.ResearchBankV8.CertificateInterval
import RequestProject.Erdos287.ResearchBankV8.ExactEntrySystem
import RequestProject.Erdos287.ResearchBankV8.GoodM
import RequestProject.Erdos287.ResearchBankV8.RigidK2
import RequestProject.Erdos287.ResearchBankV8.RoughWindow
import RequestProject.Erdos287.ResearchBankV8.Saturation
import RequestProject.Erdos287.ResearchBankV8.TernaryBlocker
import RequestProject.Erdos287.ResearchBankV8.VirtualEdge
import RequestProject.Erdos287.ResearchBankV8.WeakCutoffSeed
import RequestProject.Erdos287.ResearchBankV8.WholeParentCap
import RequestProject.Erdos287.ResearchBankV8.Ledger
import RequestProject.Erdos287.ResearchBankV8.AxiomAudit

/-!
# Erdős #287 — Research Bank V8 (aggregator)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN. This research bank does not
prove or disprove it.**

Strictly **append-only**: no declaration of `AnchoredV2`–`AnchoredV4`, `ResearchBankV5`–`ResearchBankV7`
is edited, renamed, moved, weakened or replaced; this layer only imports them.

No `sorry`, no new axiom, no `native_decide`/`bv_decide`, no `opaque`/`implemented_by`/`unsafe`.
External analytic statements appear only as explicit theorem hypotheses / structures that are
never inhabited.

## Contents
* `ActiveResidueDP` — 2F exact active-residue path DP: state equivalence, forgetting rule, resource exhaustion ≠ UNSAT, boundary-bit-only counterexample
* `CertificateInterval` — 2J certificate source interval C_Q(M) = [a,b] ↔ M ∈ J(Q;a,b), intersections
* `ExactEntrySystem` — 2E exact prime-power owner equations (Q_p, m_p, J_p, r_p, d_p), full-precision row congruence, top-digit-only counterfixture
* `GoodM` — 2I GOOD-M bookkeeping: exact ENTRY-SAT count, first-moment criterion as implication
* `RigidK2` — 2H rigid K2 logical core αp − βq = 1, adjacent contact, each row alone compatible, joint UNSAT, κ firewall
* `RoughWindow` — 2C rough-multiplier uniqueness, disjoint supports, non-coprime rough labels counterexample, lcm gluing, endpoint loss, conditional RoughLabelSupply → LocalDeletionInput → SharedGridOutput chain
* `Saturation` — 2B canonical saturation `x*_n = 1 if n ∣ L_T` (0→1 only, endpoints, no-00, entry, forbidden sets shrink)
* `TernaryBlocker` — 2G finite ternary blocker truth table: pairwise extendible, ternary UNSAT
* `VirtualEdge` — 2K virtual edge ≠ physical contact firewall
* `WeakCutoffSeed` — 2D weak-cutoff seed family P=2^(6k), M=P+2, T=M/2, A=M/3 (elementary parts) + firewall T=M/2 ≠ T=M/(2H)
* `WholeParentCap` — 2A whole-parent cap obstruction (analytic inputs as explicit structure), killed sufficient hypothesis ≠ ENTRY false
* `Ledger` — 6 epoch-aware V8 ledger extending V7; no CLOSED row; Erdős #287 OPEN
* `AxiomAudit` — `#print axioms` for every V8 theorem
-/
