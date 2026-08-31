import Mathlib
import RequestProject.Status.CurrentAuthoritativeStatusErdos287

/-!
# Axiom audit — Erdős #287 semantic re-anchoring layer

`#print axioms` for every declaration of the semantic-firewall and authoritative-status modules.

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as a
code construct in either module; all metadata facts are discharged by `decide +kernel` and all
firewalls are explicit countermodels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SemanticReanchorAudit

/-! ## Semantic firewalls / semantic unit tests -/

#print axioms Erdos287.SemanticFirewalls.singletonGap2CE
#print axioms Erdos287.SemanticFirewalls.singleton_not_counterexample
#print axioms Erdos287.SemanticFirewalls.gap2CE_firewall
#print axioms Erdos287.SemanticFirewalls.PointwiseBound
#print axioms Erdos287.SemanticFirewalls.AggregateBound
#print axioms Erdos287.SemanticFirewalls.pointwise_not_aggregate
#print axioms Erdos287.SemanticFirewalls.aggregate_not_pointwise
#print axioms Erdos287.SemanticFirewalls.branch_coverage_not_global
#print axioms Erdos287.SemanticFirewalls.smallX_bound_does_not_transfer
#print axioms Erdos287.SemanticFirewalls.QRole
#print axioms Erdos287.SemanticFirewalls.qRoles_pairwise_distinct
#print axioms Erdos287.SemanticFirewalls.qRole_card
#print axioms Erdos287.SemanticFirewalls.status_labels_pairwise_distinct

/-! ## Authoritative status, ledgers, risk classification -/

#print axioms Erdos287.AuthoritativeStatus.StatusLayer
#print axioms Erdos287.AuthoritativeStatus.layerIndex
#print axioms Erdos287.AuthoritativeStatus.authoritativeLayer
#print axioms Erdos287.AuthoritativeStatus.authoritative_layer_is_latest
#print axioms Erdos287.AuthoritativeStatus.layerIndex_injective
#print axioms Erdos287.AuthoritativeStatus.ObjectRole
#print axioms Erdos287.AuthoritativeStatus.SemanticObject
#print axioms Erdos287.AuthoritativeStatus.objectRole
#print axioms Erdos287.AuthoritativeStatus.modulus_is_not_scale
#print axioms Erdos287.AuthoritativeStatus.smallX_ne_bigX
#print axioms Erdos287.AuthoritativeStatus.gap2CE_ne_statement
#print axioms Erdos287.AuthoritativeStatus.qRoleName
#print axioms Erdos287.AuthoritativeStatus.qRoleName_distinct
#print axioms Erdos287.AuthoritativeStatus.C0Level
#print axioms Erdos287.AuthoritativeStatus.c0LevelStatus
#print axioms Erdos287.AuthoritativeStatus.c0_levels_have_distinct_status
#print axioms Erdos287.AuthoritativeStatus.OmegaNorm
#print axioms Erdos287.AuthoritativeStatus.omegaNormStatus
#print axioms Erdos287.AuthoritativeStatus.omega_norms_are_four_separate_pins
#print axioms Erdos287.AuthoritativeStatus.CoverageScope
#print axioms Erdos287.AuthoritativeStatus.coverage_scopes_distinct
#print axioms Erdos287.AuthoritativeStatus.TypeIIName
#print axioms Erdos287.AuthoritativeStatus.typeIIStatus
#print axioms Erdos287.AuthoritativeStatus.typeII_names_have_distinct_status
#print axioms Erdos287.AuthoritativeStatus.InputClass
#print axioms Erdos287.AuthoritativeStatus.windowPairSupplyClass
#print axioms Erdos287.AuthoritativeStatus.windowPairSupply_is_not_proved
#print axioms Erdos287.AuthoritativeStatus.FrontierNode
#print axioms Erdos287.AuthoritativeStatus.frontierStatus
#print axioms Erdos287.AuthoritativeStatus.dependsOn
#print axioms Erdos287.AuthoritativeStatus.erdos287_depends_on_open_nodes
#print axioms Erdos287.AuthoritativeStatus.dependsOn_irrefl
#print axioms Erdos287.AuthoritativeStatus.RetractionEntry
#print axioms Erdos287.AuthoritativeStatus.retractionStatus
#print axioms Erdos287.AuthoritativeStatus.retraction_ledger_wellformed
#print axioms Erdos287.AuthoritativeStatus.Resource
#print axioms Erdos287.AuthoritativeStatus.resourceAvailable
#print axioms Erdos287.AuthoritativeStatus.resource_ledger
#print axioms Erdos287.AuthoritativeStatus.ConstantSelection
#print axioms Erdos287.AuthoritativeStatus.constantFixed
#print axioms Erdos287.AuthoritativeStatus.constants_all_free
#print axioms Erdos287.AuthoritativeStatus.SourceNormalisationStage
#print axioms Erdos287.AuthoritativeStatus.stageFormallyAvailable
#print axioms Erdos287.AuthoritativeStatus.source_normalisation_ledger
#print axioms Erdos287.AuthoritativeStatus.RiskClass
#print axioms Erdos287.AuthoritativeStatus.RiskItem
#print axioms Erdos287.AuthoritativeStatus.riskClass
#print axioms Erdos287.AuthoritativeStatus.riskGuarded
#print axioms Erdos287.AuthoritativeStatus.risk_counts
#print axioms Erdos287.AuthoritativeStatus.PreClosureBlocker
#print axioms Erdos287.AuthoritativeStatus.blockerDischarged
#print axioms Erdos287.AuthoritativeStatus.preClosure_blockers_remain

end SemanticReanchorAudit
end Erdos287