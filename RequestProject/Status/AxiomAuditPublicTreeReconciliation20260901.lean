import RequestProject.Status.PublicTreeReconciliation20260901

/-!
# Axiom audit — public-tree reconciliation layer (2026-09-01)

`#print axioms` for every declaration added by the 2026-09-01 reconciliation pass, together
with a regression re-print of the end-to-end chain.  Every line below must report either
"does not depend on any axioms" or a subset of `propext`, `Classical.choice`, `Quot.sound`.
No `sorryAx`, no user axiom, no `native_decide`, no `unsafe`, no `opaque`, no
`implemented_by` occurs in the audited files.
-/

namespace Erdos287

section OrderedSequenceBridgeAudit

#print axioms Erdos287.Erdos287SeqStatement
#print axioms Erdos287.sum_recip_rat_iff_real
#print axioms Erdos287.enum
#print axioms Erdos287.enum_mem
#print axioms Erdos287.enum_lt_enum
#print axioms Erdos287.exists_enum_eq
#print axioms Erdos287.enum_succ_le
#print axioms Erdos287.sum_enum_recip
#print axioms Erdos287.erdos287SeqStatement_of_statement
#print axioms Erdos287.erdos287Statement_of_seqStatement
#print axioms Erdos287.erdos287Statement_iff_seqStatement
#print axioms Erdos287.gap_le_two_iff_orderEmb_gap

end OrderedSequenceBridgeAudit

section PublicTreeAudit

open Erdos287.PublicTree20260901

#print axioms Erdos287.PublicTree20260901.nodeStatus
#print axioms Erdos287.PublicTree20260901.nodeKind
#print axioms Erdos287.PublicTree20260901.classification_of_open_nodes
#print axioms Erdos287.PublicTree20260901.analytic_nodes_not_kernelProved
#print axioms Erdos287.PublicTree20260901.kernelProved_node_count
#print axioms Erdos287.PublicTree20260901.dependsOn
#print axioms Erdos287.PublicTree20260901.rank
#print axioms Erdos287.PublicTree20260901.dependsOn_rank_decreasing
#print axioms Erdos287.PublicTree20260901.dependsOn_irrefl
#print axioms Erdos287.PublicTree20260901.erdos287Statement_terminal
#print axioms Erdos287.PublicTree20260901.implication_does_not_close_target
#print axioms Erdos287.PublicTree20260901.reconfirm_endToEnd
#print axioms Erdos287.PublicTree20260901.reconfirm_endToEnd_seq
#print axioms Erdos287.PublicTree20260901.closureInputs_supply_visible
#print axioms Erdos287.PublicTree20260901.not_windowPairSupply_zero
#print axioms Erdos287.PublicTree20260901.not_windowPairSupply_one
#print axioms Erdos287.PublicTree20260901.not_windowPairSupply_two
#print axioms Erdos287.PublicTree20260901.closureInputs_threshold_ge_three
#print axioms Erdos287.PublicTree20260901.windowPairSupply_forces_large_primePowers
#print axioms Erdos287.PublicTree20260901.constructsClosureInputs
#print axioms Erdos287.PublicTree20260901.no_banked_interface_constructs_closureInputs
#print axioms Erdos287.PublicTree20260901.interface_status_not_theorem
#print axioms Erdos287.PublicTree20260901.plain_l2_ne_weighted_l2
#print axioms Erdos287.PublicTree20260901.packetwise_not_aggregate
#print axioms Erdos287.PublicTree20260901.supply_is_input_not_output

end PublicTreeAudit

section EndToEndRegression

#print axioms Erdos287.no_Erdos287Counterexample_of_closure
#print axioms Erdos287.erdos287_seq_of_closure
#print axioms Erdos287.Gap2CE.no_of_windowPairSupply
#print axioms Erdos287.windowPairSupply_of_sophieWitness
#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_4e9
#print axioms Erdos287.no_Erdos287Counterexample_of_prime_max
#print axioms Erdos287.erdos287_seq_of_no_counterexample

end EndToEndRegression

end Erdos287
