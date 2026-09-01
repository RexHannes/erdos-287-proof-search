import RequestProject.Status.CurrentStatusErdos287MasterSourceFrontier

/-!
# Erdős #287 — axiom audit for the master-source frontier bank

`#print axioms` for every principal declaration added by the master-source frontier pass,
plus an end-to-end regression re-print.  Each report must show a subset of
`propext`, `Classical.choice`, `Quot.sound`.  There is no `sorry`, no `sorryAx`, no user
axiom, no `unsafe`, no `opaque`, no `native_decide` and no `implemented_by` in any of the
new modules.
-/

namespace Erdos287

section MasterSourceFrontierAudit

-- §1  Master source interface
#print axioms Erdos287.MasterSource.unprojectedSource
#print axioms Erdos287.MasterSource.unprojectedSource_insert
#print axioms Erdos287.MasterSource.norm_unprojectedSource_le
#print axioms Erdos287.MasterSource.norm_unprojectedSource_le_mass
#print axioms Erdos287.MasterSource.MasterPhysicalSourceRealisation.parent_eq
#print axioms Erdos287.MasterSource.MasterPhysicalSourceRealisation.parent_eq_zero_of_coefficient_zero
#print axioms Erdos287.MasterSource.MasterPhysicalSourceRealisation.toDictionary
#print axioms Erdos287.MasterSource.no_realisation_vanishingWeightSpec
#print axioms Erdos287.MasterSource.no_realisation_zeroGcdSpec
#print axioms Erdos287.MasterSource.sourceDictionary_ne_physicalRealisation
#print axioms Erdos287.MasterSource.dictionary_population_does_not_construct_parent
#print axioms Erdos287.MasterSource.toyRealisation
#print axioms Erdos287.MasterSource.toy_model_is_not_the_physical_source

-- §2  Proof-local Ω: abstract partition, insertion identity, local finiteness
#print axioms Erdos287.ProofOmega.DyadicPartition.weight_le_one
#print axioms Erdos287.ProofOmega.DyadicPartition.scales_nonempty
#print axioms Erdos287.ProofOmega.DyadicPartition.one_le_overlapBound
#print axioms Erdos287.ProofOmega.DyadicPartition.reconstruction
#print axioms Erdos287.ProofOmega.projectedSource
#print axioms Erdos287.ProofOmega.unprojectedSource_eq_sum_projectedSource
#print axioms Erdos287.ProofOmega.unprojectedSource_eq_sum_projectedSource_of_partition
#print axioms Erdos287.ProofOmega.card_le_three_of_spread_le_two
#print axioms Erdos287.ProofOmega.contributingScales_spread
#print axioms Erdos287.ProofOmega.dyadicLocalFiniteness
#print axioms Erdos287.ProofOmega.dyadicLocalFiniteness_sharp
#print axioms Erdos287.ProofOmega.contributingScales_nonempty
#print axioms Erdos287.ProofOmega.physical_insertion
#print axioms Erdos287.ProofOmega.trivialPartition
#print axioms Erdos287.ProofOmega.abstractProofOmegaPartition_does_not_construct_physicalInsertion
#print axioms Erdos287.ProofOmega.insertion_identity_is_not_physical_insertion

-- §3  Single Perron contour
#print axioms Erdos287.PerronContour.singleContour_integral_eq_arsinh
#print axioms Erdos287.PerronContour.arsinh_le_log_one_add_two_mul
#print axioms Erdos287.PerronContour.singleContour_integral_le_log
#print axioms Erdos287.PerronContour.perronContour_integral_eq
#print axioms Erdos287.PerronContour.perronContour_log_budget
#print axioms Erdos287.PerronContour.singleContourL1Bound_log
#print axioms Erdos287.PerronContour.perronSingleContourL1Bound
#print axioms Erdos287.PerronContour.contour_compile
#print axioms Erdos287.PerronContour.contour_total_compile

-- §4  Typed source packets
#print axioms Erdos287.TypedPackets.typedPacket_compile
#print axioms Erdos287.TypedPackets.SourcePacketDecomposition.compile
#print axioms Erdos287.TypedPackets.typedPacket_compile_logBudget
#print axioms Erdos287.TypedPackets.packetwise_coefficient_bound_does_not_bound_total
#print axioms Erdos287.TypedPackets.no_nuclearBudget_from_packetwise_bound
#print axioms Erdos287.TypedPackets.typedPacketCompiler_does_not_construct_masterSource
#print axioms Erdos287.TypedPackets.trivialDecomposition

-- §5  Per-contour counterguard
#print axioms Erdos287.PerronCounterguard.contourMass_le_one
#print axioms Erdos287.PerronCounterguard.total_contourMass
#print axioms Erdos287.PerronCounterguard.perContour_bound_does_not_imply_total_without_cardinality
#print axioms Erdos287.PerronCounterguard.perContour_datum_compatible_with_unbounded_total
#print axioms Erdos287.PerronCounterguard.total_bound_of_perContour_and_cardinality
#print axioms Erdos287.PerronCounterguard.no_global_total_from_perContour_bound

-- §6  Abstract `Δ × q_a` Fourier kernel
#print axioms Erdos287.BDiagonalDeltaQ.deltaQ_unitaryFourier_bound
#print axioms Erdos287.BDiagonalDeltaQ.phase_fiberwise
#print axioms Erdos287.BDiagonalDeltaQ.deltaQ_residueAggregation_compiler
#print axioms Erdos287.BDiagonalDeltaQ.deltaQ_residueAggregation_sqrt
#print axioms Erdos287.BDiagonalDeltaQ.deltaQ_interval_compiler
#print axioms Erdos287.BDiagonalDeltaQ.cauchy_over_t
#print axioms Erdos287.BDiagonalDeltaQ.deltaQ_cauchy_over_t
#print axioms Erdos287.BDiagonalDeltaQ.deltaQ_cauchy_over_t_withMultiplicities

-- §7  Physical dictionaries (all uninhabited)
#print axioms Erdos287.PhysicalDictionary.bDiagonalPhysical_compiler
#print axioms Erdos287.PhysicalDictionary.bDiagonalPhysicalDictionary_open
#print axioms Erdos287.PhysicalDictionary.abstractDeltaQKernel_does_not_close_bDiagonal
#print axioms Erdos287.PhysicalDictionary.c0Bridge_owner_unique
#print axioms Erdos287.PhysicalDictionary.c0SourceRealisationBridge_open
#print axioms Erdos287.PhysicalDictionary.transverseSourceRealisationBridge_open
#print axioms Erdos287.PhysicalDictionary.owner_labels_distinct

-- §8  Source coverage
#print axioms Erdos287.SourceCoverage.PhysicalOwnerMap.no_double_spending
#print axioms Erdos287.SourceCoverage.PhysicalOwnerMap.exhaustive
#print axioms Erdos287.SourceCoverage.PhysicalOwnerMap.coverage_of_domain
#print axioms Erdos287.SourceCoverage.abstractOwnerMap_does_not_imply_physicalSourceCoverage100
#print axioms Erdos287.SourceCoverage.coverage100_total
#print axioms Erdos287.SourceCoverage.physicalSourceCoverage100_open
#print axioms Erdos287.SourceCoverage.ownerBookkeeping_available_coverage_open

-- §9  Frontier status layer
#print axioms Erdos287.MasterSourceFrontier.erdos287_open
#print axioms Erdos287.MasterSourceFrontier.first_frontier_open
#print axioms Erdos287.MasterSourceFrontier.next_frontier_open
#print axioms Erdos287.MasterSourceFrontier.fullSourceLocalAnalyticKernel_open
#print axioms Erdos287.MasterSourceFrontier.windowPairSupply_open
#print axioms Erdos287.MasterSourceFrontier.status_labels_distinct
#print axioms Erdos287.MasterSourceFrontier.kernelProved_node_count
#print axioms Erdos287.MasterSourceFrontier.open_node_count
#print axioms Erdos287.MasterSourceFrontier.backing_proofOmegaAbstractPartition
#print axioms Erdos287.MasterSourceFrontier.backing_proofOmegaLocalFiniteness
#print axioms Erdos287.MasterSourceFrontier.backing_perronSingleContour
#print axioms Erdos287.MasterSourceFrontier.backing_perronInterfaceFail
#print axioms Erdos287.MasterSourceFrontier.backing_bDiagonalDeltaQAbstract
#print axioms Erdos287.MasterSourceFrontier.backing_uninhabited_rows
#print axioms Erdos287.MasterSourceFrontier.no_frontier_module_constructs_closureInputs
#print axioms Erdos287.MasterSourceFrontier.reconfirm_endToEnd_frontier
#print axioms Erdos287.MasterSourceFrontier.closureInputs_supply_still_visible
#print axioms Erdos287.MasterSourceFrontier.frontier_work_does_not_close_statement
#print axioms Erdos287.MasterSourceFrontier.oldClaims_relabelled
#print axioms Erdos287.MasterSourceFrontier.superseded_claims_retain_content
#print axioms Erdos287.MasterSourceFrontier.proofOmega_is_abstract_certificate

-- §10  End-to-end regression (unchanged historical chain)
#print axioms Erdos287.no_Erdos287Counterexample_of_closure
#print axioms Erdos287.erdos287_seq_of_closure
#print axioms Erdos287.Gap2CE.no_of_windowPairSupply
#print axioms Erdos287.windowPairSupply_of_sophieWitness
#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_4e9
#print axioms Erdos287.no_Erdos287Counterexample_of_prime_max

end MasterSourceFrontierAudit

end Erdos287
