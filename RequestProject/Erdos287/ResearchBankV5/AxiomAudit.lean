import RequestProject.Erdos287.ResearchBankV5.Routes
import RequestProject.Erdos287.ResearchBankV5.GateLedger
import RequestProject.Erdos287.ResearchBankV5.AsymptoticInputs
import RequestProject.Erdos287.ResearchBankV5.KilledRoutes
import RequestProject.Erdos287.ResearchBankV5.Regressions
import RequestProject.Erdos287.ResearchBankV5.RouteReconciliation
import RequestProject.Erdos287.ResearchBankV5.ContactCore.PathTransfer
import RequestProject.Erdos287.ResearchBankV5.ContactCore.StrictHeight
import RequestProject.Erdos287.ResearchBankV5.ContactCore.ProperPowerRow
import RequestProject.Erdos287.ResearchBankV5.ContactCore.PadicSaturation
import RequestProject.Erdos287.ResearchBankV5.ContactCore.ExternalInterfaces

/-!
# Research Bank V5 — axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every principal **new** kernel theorem of the V5 layer is checked here with `#print axioms`.
Only Lean's standard `propext`, `Classical.choice` and `Quot.sound` may appear (several theorems
use fewer).  There is no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `opaque` or
`@[implemented_by]` anywhere in this layer; the finite fixtures are discharged by kernel-reducible
`decide`, which introduces no axiom dependency.
-/

namespace Erdos287
namespace ResearchBankV5

-- A.  Meta layer: routes, evidence kinds, status firewalls
#print axioms Erdos287.ResearchBankV5.externalBank_not_kernelProof
#print axioms Erdos287.ResearchBankV5.conditionalInterface_not_inhabited
#print axioms Erdos287.ResearchBankV5.externalBank_not_inhabited
#print axioms Erdos287.ResearchBankV5.open_not_closed
#print axioms Erdos287.ResearchBankV5.killed_not_false_target
#print axioms Erdos287.ResearchBankV5.superseded_not_false
#print axioms Erdos287.ResearchBankV5.open_status_does_not_propagate
#print axioms Erdos287.ResearchBankV5.no_closure_without_bridge

-- B.  PATH transfer
#print axioms Erdos287.ResearchBankV5.ContactCore.path_transfer
#print axioms Erdos287.ResearchBankV5.ContactCore.Rseq_eq_sum
#print axioms Erdos287.ResearchBankV5.ContactCore.Rseq_div_Cseq
#print axioms Erdos287.ResearchBankV5.ContactCore.Cseq_eq_prod
#print axioms Erdos287.ResearchBankV5.ContactCore.Dseq_eq_prod
#print axioms Erdos287.ResearchBankV5.ContactCore.fixture_path_transfer
#print axioms Erdos287.ResearchBankV5.ContactCore.direct_splice_not_unit
#print axioms Erdos287.ResearchBankV5.ContactCore.depthOne_only

-- C.  STRICT-HEIGHT
#print axioms Erdos287.ResearchBankV5.ContactCore.strictHeight_no_unit_contact
#print axioms Erdos287.ResearchBankV5.ContactCore.strictHeight_no_unit_contact_symm
#print axioms Erdos287.ResearchBankV5.ContactCore.strictHeight_floor_lt
#print axioms Erdos287.ResearchBankV5.ContactCore.sameHeight_cycle_impossible
#print axioms Erdos287.ResearchBankV5.ContactCore.strict_change_not_monotone
#print axioms Erdos287.ResearchBankV5.ContactCore.strictHeight_regression_sweep300
#print axioms Erdos287.ResearchBankV5.ContactCore.strictHeight_regression_sweep1000

-- D.  Proper-power row, layer counting, valuation lift
#print axioms Erdos287.ResearchBankV5.ContactCore.mulCount_le
#print axioms Erdos287.ResearchBankV5.ContactCore.mulCount_ge
#print axioms Erdos287.ResearchBankV5.ContactCore.layer_split
#print axioms Erdos287.ResearchBankV5.ContactCore.layerCount_le
#print axioms Erdos287.ResearchBankV5.ContactCore.sparse_layer_bound
#print axioms Erdos287.ResearchBankV5.ContactCore.deficient_layer_bound
#print axioms Erdos287.ResearchBankV5.ContactCore.heavy_layer_majority
#print axioms Erdos287.ResearchBankV5.ContactCore.rawPort_cap
#print axioms Erdos287.ResearchBankV5.ContactCore.ppRow_ne_naive
#print axioms Erdos287.ResearchBankV5.ContactCore.valuationLift_mul
#print axioms Erdos287.ResearchBankV5.ContactCore.valuationLift_floor
#print axioms Erdos287.ResearchBankV5.ContactCore.valuationLift_unit_cofactor

-- E.  p-adic saturation (layer-local digit step)
#print axioms Erdos287.ResearchBankV5.ContactCore.subsetSums_univ_of_closed
#print axioms Erdos287.ResearchBankV5.ContactCore.subsetSums_card_ge
#print axioms Erdos287.ResearchBankV5.ContactCore.subsetSums_eq_univ
#print axioms Erdos287.ResearchBankV5.ContactCore.padicLayer_hits_target
#print axioms Erdos287.ResearchBankV5.ContactCore.heavy_obstruction_charged
#print axioms Erdos287.ResearchBankV5.ContactCore.sparse_obstruction_small

-- F.  Conditional consequences of the external interfaces
#print axioms Erdos287.ResearchBankV5.ContactCore.valTrans_of_raw_terminal
#print axioms Erdos287.ResearchBankV5.ContactCore.fullCube_no_restriction
#print axioms Erdos287.ResearchBankV5.ContactCore.fullCube_elimination
#print axioms Erdos287.ResearchBankV5.ContactCore.linear_charge

-- G.  Killed architectures
#print axioms Erdos287.ResearchBankV5.primorial_local_factor_cancellation
#print axioms Erdos287.ResearchBankV5.primorial_local_factor_cancellation_prime
#print axioms Erdos287.ResearchBankV5.height_drop_20_19
#print axioms Erdos287.ResearchBankV5.no_universal_height_ratio

-- H.  Gate ledger and no-fake-closure
#print axioms Erdos287.ResearchBankV5.routeOwners_disjoint
#print axioms Erdos287.ResearchBankV5.currentOwner_mem_routeOwners
#print axioms Erdos287.ResearchBankV5.anchoredLedger_open_entries
#print axioms Erdos287.ResearchBankV5.gateD_closed
#print axioms Erdos287.ResearchBankV5.gateA_split
#print axioms Erdos287.ResearchBankV5.gateB_open
#print axioms Erdos287.ResearchBankV5.gateC_open
#print axioms Erdos287.ResearchBankV5.erdos287_not_marked_closed
#print axioms Erdos287.ResearchBankV5.both_routes_open
#print axioms Erdos287.ResearchBankV5.no_closure_from_status
#print axioms Erdos287.ResearchBankV5.ledger_is_not_a_proof
#print axioms Erdos287.ResearchBankV5.gateD_closed_does_not_close_287
#print axioms Erdos287.ResearchBankV5.externalInputs_not_formalized
#print axioms Erdos287.ResearchBankV5.externalInputs_not_kernelProof

-- I.  Bridges
#print axioms Erdos287.ResearchBankV5.Reconciliation.anchoredV4_bridge
#print axioms Erdos287.ResearchBankV5.Reconciliation.contactCore_gateD_bridge
#print axioms Erdos287.ResearchBankV5.Reconciliation.ContactFinalConfig.toCounterexample
#print axioms Erdos287.ResearchBankV5.Reconciliation.routes_not_claimed_equivalent

-- J.  Regressions
#print axioms Erdos287.ResearchBankV5.Regressions.regression_factor_two
#print axioms Erdos287.ResearchBankV5.Regressions.regression_doubled_lattice
#print axioms Erdos287.ResearchBankV5.Regressions.regression_depth_two_splice
#print axioms Erdos287.ResearchBankV5.Regressions.regression_properPower_forced_zero
#print axioms Erdos287.ResearchBankV5.Regressions.regression_valuation_lift_34_100
#print axioms Erdos287.ResearchBankV5.Regressions.regression_padic_saturation
#print axioms Erdos287.ResearchBankV5.Regressions.regression_raw_port_cap
#print axioms Erdos287.ResearchBankV5.Regressions.regression_strict_height
#print axioms Erdos287.ResearchBankV5.Regressions.regression_no_fixed_ratio
#print axioms Erdos287.ResearchBankV5.Regressions.regression_primorial_cancellation

end ResearchBankV5
end Erdos287
