import RequestProject.Erdos287.ResearchBankV10
import RequestProject.Erdos287.ResearchBankV11.AnalyticActivation
import RequestProject.Erdos287.ResearchBankV11.AxiomAudit
import RequestProject.Erdos287.ResearchBankV11.EffectiveConstants
import RequestProject.Erdos287.ResearchBankV11.EffectiveSplice
import RequestProject.Erdos287.ResearchBankV11.ExceptionalFactor
import RequestProject.Erdos287.ResearchBankV11.FiniteArchitectureFrontier
import RequestProject.Erdos287.ResearchBankV11.Ledger
import RequestProject.Erdos287.ResearchBankV11.PowerToLog

/-!
# Erdős #287 — Research Bank V11 (aggregator)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 remains OPEN. This research bank does not
prove or disprove it.**

Strictly **append-only**: no pre-existing file is modified; this layer only imports earlier layers.

No `sorry`, no new axiom, no `native_decide`/`bv_decide`, no `opaque`/`implemented_by`/`unsafe`.
External analytic statements appear only as explicit hypotheses / `Prop` structures.  No theorem
inhabits them for the actual arithmetic error terms; the only inhabitants are the trivial
zero-error models used in the non-vacuity / regression fixtures.

No numerical M_an is available in the current bank.  The effective finite splice is BLOCKED.

## Contents
* `AnalyticActivation` — §R `analyticActivation`, sufficiency, `current_M_an_eq_none`, status firewall, fixture 7
* `AxiomAudit` — §X `#print axioms` for every V11 theorem
* `EffectiveConstants` — §Q `NumericalExternalConstants` (no instance), symbolic error, `currentConstants = none`
* `EffectiveSplice` — §U refined splice bundle, BLOCKED theorems, fixture 8
* `ExceptionalFactor` — §S exceptional-safe full modulus predicate, W-shortcut refutation
* `FiniteArchitectureFrontier` — §T OPEN finite-architecture contract, killed architectures, scoped kills
* `Ledger` — V11 ledger, preservation of V10, frontier, closure firewall
* `PowerToLog` — §Q generic explicit power-to-log conversion
-/
