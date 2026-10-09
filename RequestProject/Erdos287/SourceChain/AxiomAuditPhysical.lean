import RequestProject.Erdos287.SourceChain.AxiomAudit
import RequestProject.Erdos287.SourceChain.OAIImport.BVTransfer
import RequestProject.Erdos287.SourceChain.OneSidedTail

/-!
# Erdős #287 — source chain: build-time trust audit of the BV/SW import and the one-sided
seven-block layer

* `#sc_assert_all_std_axioms` re-runs over the whole `Erdos287.SourceChain` namespace, now
  including `Erdos287.SourceChain.OAIImport` and the one-sided consumer;
* `#ct_assert_std_axioms` on each new principal theorem;
* the external BV/SW statements enter only as hypotheses (`OAIBombieriVinogradov`); no axiom.
-/

#sc_assert_all_std_axioms

#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.abs_progErr_le_endpointError
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.psiBVProjectForm_of_OAI
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.tinyModulusSW_of_OAIBV
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.apSW_of_OAIBV
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.sbp_identity
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.apError_sbp
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.sum_inv_totient_le
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.eventual_bv_pi
#ct_assert_std_axioms Erdos287.SourceChain.OAIImport.ordinaryBVProvider_of_OAI
#ct_assert_std_axioms Erdos287.SourceChain.one_sided_moment_ineq
#ct_assert_std_axioms Erdos287.SourceChain.oneSided_of_twoSided
#ct_assert_std_axioms Erdos287.SourceChain.seven_block_contact_false_oneSided
#ct_assert_std_axioms Erdos287.SourceChain.tail_of_remainder_littleO_oneSided
#ct_assert_std_axioms Erdos287.SourceChain.Tail287_of_MinimalAnalyticProviders_oneSided

#check @Erdos287.SourceChain.OAIImport.ordinaryBVProvider_of_OAI
#print axioms Erdos287.SourceChain.OAIImport.ordinaryBVProvider_of_OAI
#print axioms Erdos287.SourceChain.Tail287_of_MinimalAnalyticProviders_oneSided
