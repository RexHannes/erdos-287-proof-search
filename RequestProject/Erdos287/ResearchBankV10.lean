import RequestProject.Erdos287.ResearchBankV9
import RequestProject.Erdos287.ResearchBankV10.AsymptoticComposition
import RequestProject.Erdos287.ResearchBankV10.AxiomAudit
import RequestProject.Erdos287.ResearchBankV10.EndpointCounterfixture
import RequestProject.Erdos287.ResearchBankV10.ExponentGate
import RequestProject.Erdos287.ResearchBankV10.FrozenFrontier
import RequestProject.Erdos287.ResearchBankV10.HBSelection
import RequestProject.Erdos287.ResearchBankV10.HBSupportCoverage
import RequestProject.Erdos287.ResearchBankV10.Ledger
import RequestProject.Erdos287.ResearchBankV10.Providers
import RequestProject.Erdos287.ResearchBankV10.RoughSeedIdentities
import RequestProject.Erdos287.ResearchBankV10.TypeIGroupedCoefficient
import RequestProject.Erdos287.ResearchBankV10.TypeIICoefficient
import RequestProject.Erdos287.ResearchBankV10.TypeIICompatibleCells
import RequestProject.Erdos287.ResearchBankV10.TypeIIHighLow
import RequestProject.Erdos287.ResearchBankV10.TypeIProvider
import RequestProject.Erdos287.ResearchBankV10.TypeIRescaling
import RequestProject.Erdos287.ResearchBankV10.TypeIRoughness
import RequestProject.Erdos287.ResearchBankV10.WellFactorableCutoff

/-!
# Erdős #287 — Research Bank V10 (aggregator)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN. This research bank does not
prove or disprove it.**

Strictly **append-only**: no pre-existing file is modified; this layer only imports earlier layers.

No `sorry`, no new axiom, no `native_decide`/`bv_decide`, no `opaque`/`implemented_by`/`unsafe`.
External analytic statements appear only as explicit hypotheses / `Prop` structures.  No theorem
inhabits them for the actual arithmetic error terms; the only inhabitants are the trivial
zero-error models used in the non-vacuity / regression fixtures.

The repaired Type-II/HB composition is formalized only relative to explicitly visible analytic providers.

## Contents
* `AsymptoticComposition` — §O `mtSpecificAsymptotic_of_repairedProviders` (conditional) + specialization
* `AxiomAudit` — §X `#print axioms` for every V10 theorem
* `EndpointCounterfixture` — §J permanent endpoint-only counterfixture
* `ExponentGate` — §O exact exponent arithmetic (ϑ > 78/145, 145/39 − 2/ϑ = 52426455/18953756081)
* `FrozenFrontier` — §B frozen input firewall: `FrozenV9Bank` (re-used V9 proofs), `Erdos287Closed`
* `HBSelection` — §K proved three-way HB selection trichotomy + counterfixtures
* `HBSupportCoverage` — §L parameters, BV region, Case II parameters, vertex argument, gap systems, Case III d* overlap, routing theorem
* `Ledger` — §P V10 ledger, preservation of V9, no reclassification, closure firewall
* `Providers` — §C external analytic providers (structures), aggregation lemma, dependency checks
* `RoughSeedIdentities` — §N ρ_z = 1 ⋆ (μ 1_{P⁺≤z}), μρ_z = μ ⋆ 1_{P⁺≤z}, Rankin split, SW provider
* `TypeIGroupedCoefficient` — §F grouped-coefficient dependency contract (types) + negative fixture
* `TypeIICoefficient` — §H Type-II index map (u,v,w), grouped coefficient factorization, reciprocal phase
* `TypeIICompatibleCells` — §G compatible-α count = d (not |k|d), fixtures, prefactor ratio K
* `TypeIIHighLow` — §I collision identities, high-H skeleton (exact/divisor/envelope separated), w = 0 count, low-H diagonal, cost comparison + fixtures
* `TypeIProvider` — smooth Type-I provider interface and ∑_e T_e bound
* `TypeIRescaling` — §D Type-I e-rescaling: β_e, support, divisor bound, bijection, physical product, reference term, lattice identity, 2/5/1 density fixture
* `TypeIRoughness` — §E Bonferroni roughness: exact evaluation, odd-J sandwich, U_J − L_J = shell, e ≤ z₀^J, ∑ 1/e ≤ s₀^J/J!, exp((log log X)²) ≤ X^δ
* `WellFactorableCutoff` — §M well-factorability truncation firewall + data-flow theorem
-/
