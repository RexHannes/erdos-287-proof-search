import RequestProject.Erdos287.ResearchBankV11
import RequestProject.Erdos287.ResearchBankV12.ConcreteParameters
import RequestProject.Erdos287.ResearchBankV12.EndpointCounterfixture
import RequestProject.Erdos287.ResearchBankV12.CompatibleCellsConcrete
import RequestProject.Erdos287.ResearchBankV12.RestoredTypeIIEnvelope
import RequestProject.Erdos287.ResearchBankV12.TypeIIWholeRectangle
import RequestProject.Erdos287.ResearchBankV12.HBSelectionConcrete
import RequestProject.Erdos287.ResearchBankV12.HBCaseI
import RequestProject.Erdos287.ResearchBankV12.HBCaseII
import RequestProject.Erdos287.ResearchBankV12.HBCaseIII
import RequestProject.Erdos287.ResearchBankV12.HBFullSupportConcrete
import RequestProject.Erdos287.ResearchBankV12.RoughSeedConcrete
import RequestProject.Erdos287.ResearchBankV12.ConcreteAsymptoticGate
import RequestProject.Erdos287.ResearchBankV12.Ledger
import RequestProject.Erdos287.ResearchBankV12.AxiomAudit

/-!
# Erdős #287 — Research Bank V12 (aggregator): concrete repaired Type-II/HB specialization

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN. This research bank does not
prove or disprove it.**

Strictly **append-only**: no pre-existing file is modified; this layer only imports earlier layers.

No `sorry`, no new axiom, no `native_decide`/`bv_decide`, no `opaque`/`implemented_by`/`unsafe`.
External analytic statements (spectral, BV, SW, Type-I) appear only as explicit hypotheses /
`Prop` structures; the only inhabitants are zero-error models used in non-vacuity fixtures.

## Contents
* `ConcreteParameters` — §3 exact θ₀, ε₀, ζ, λ = ϑ; gates; §9 `smallBV`; §10 `s*`, `r*`
* `EndpointCounterfixture` — §4 `endpointOnlyHBArgument_false` (permanent firewall)
* `CompatibleCellsConcrete` — §5 compatible classes = `d` (not `|k|d`), lift structure, fixtures
* `RestoredTypeIIEnvelope` — §6 layers A/B/C, `RestoredTypeIISpectralProvider`,
  `restoredTypeII_of_provider`; §7 high-H/low-H comparisons
* `TypeIIWholeRectangle` — §10 Case II gaps `g1, g2, g3` on the whole clipped rectangle
* `HBSelectionConcrete` — §8 three-way selection, minimal classification hypothesis, fixtures
* `HBCaseI` / `HBCaseII` / `HBCaseIII` — §11 / §10 / §12 case routing and margins
* `HBFullSupportConcrete` — §13 `every_actual_HB_box_routed`; §14 well-factorability firewall
* `RoughSeedConcrete` — §15 rough-seed identities; SW external
* `ConcreteAsymptoticGate` — §16 `mtSpecificAsymptotic_concrete`, exact gate
* `Ledger` — V12 ledger, `v12_preserves_v11_ledger`, closure firewall
* `AxiomAudit` — `#print axioms` for every V12 theorem
-/
