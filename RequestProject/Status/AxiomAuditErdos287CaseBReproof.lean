import Mathlib
import RequestProject.Status.CurrentStatusErdos287CaseBFrontier

/-!
# Axiom audit — Erdős #287, CASE-B reproof bank Δ

`#print axioms` for every new principal declaration of this delta.

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs in
any module of this delta.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace CaseBReproofAudit

/-! ## Reproof bank -/

#print axioms Erdos287.CaseBReproof.separation_of_distinct_pairs
#print axioms Erdos287.CaseBReproof.caseB_pipeline_QH_bound
#print axioms Erdos287.CaseBReproof.normalised_ratio_le_of_comparable
#print axioms Erdos287.CaseBReproof.rpow_max_eq
#print axioms Erdos287.CaseBReproof.kappa_le_of_critical_range
#print axioms Erdos287.CaseBReproof.loglog_div_log_tendsto_zero
#print axioms Erdos287.CaseBReproof.kappa_le_eventually
#print axioms Erdos287.CaseBReproof.kappa_le_max_zero
#print axioms Erdos287.CaseBReproof.projector_S1_at_two_G

/-! ## Frontier ledger -/

#print axioms Erdos287.CaseBFrontierStatus.spacingPairForm_row_is_a_theorem
#print axioms Erdos287.CaseBFrontierStatus.comparabilityFirewall_row_is_a_theorem
#print axioms Erdos287.CaseBFrontierStatus.criticalExponent_row_is_a_theorem
#print axioms Erdos287.CaseBFrontierStatus.stage
#print axioms Erdos287.CaseBFrontierStatus.frontierLedger
#print axioms Erdos287.CaseBFrontierStatus.frontier_no_closed_rows
#print axioms Erdos287.CaseBFrontierStatus.frontier_unique
#print axioms Erdos287.CaseBFrontierStatus.primitiveFractionCritical_strictly_before_frontier
#print axioms Erdos287.CaseBFrontierStatus.primitiveFractionCritical_not_frontier
#print axioms Erdos287.CaseBFrontierStatus.chain_is_strictly_increasing
#print axioms Erdos287.CaseBFrontierStatus.frontier_erdos287_open
#print axioms Erdos287.CaseBFrontierStatus.caseB_ledger_preserved

end CaseBReproofAudit
end Erdos287
