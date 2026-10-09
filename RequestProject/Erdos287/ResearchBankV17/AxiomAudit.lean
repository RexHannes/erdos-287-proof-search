import RequestProject.Erdos287.ResearchBankV17.CorrectedLogP
import RequestProject.Erdos287.ResearchBankV17.Ledger
import RequestProject.Erdos287.ResearchBankV17.ThinConsumer
import RequestProject.Erdos287.ResearchBankV17.ThinEffectivityFirewall
import RequestProject.Erdos287.ResearchBankV17.ThinFunctionalCertificate
import RequestProject.Erdos287.ResearchBankV17.ThinParameters
import RequestProject.Erdos287.ResearchBankV17.ThinSupportLedger
import RequestProject.Erdos287.ResearchBankV17.UniformThinning

/-!
# Erdős #287 — Research Bank V17: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V17 (35 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV17.CorrectedLogP.log_twelve_pow
#print axioms Erdos287.ResearchBankV17.CorrectedLogP.logP_eq
#print axioms Erdos287.ResearchBankV17.CorrectedLogP.old_formula_is_log_3K
#print axioms Erdos287.ResearchBankV17.CorrectedLogP.logP_sub_old
#print axioms Erdos287.ResearchBankV17.CorrectedLogP.old_formula_ne_logP
#print axioms Erdos287.ResearchBankV17.CorrectedLogP.one_lt_log_three
#print axioms Erdos287.ResearchBankV17.CorrectedLogP.log_three_lt
#print axioms Erdos287.ResearchBankV17.CorrectedLogP.a_sub_logP_bounds
#print axioms Erdos287.ResearchBankV17.Ledger.v17_preserves_v16_ledger
#print axioms Erdos287.ResearchBankV17.Ledger.v17_erdos287_open
#print axioms Erdos287.ResearchBankV17.ThinConsumer.thin_eventually_no_counterexample
#print axioms Erdos287.ResearchBankV17.ThinConsumer.bad_bounds_fail_check
#print axioms Erdos287.ResearchBankV17.ThinConsumer.thin_margin_is_certified_input_dependent
#print axioms Erdos287.ResearchBankV17.ThinEffectivityFirewall.eventual_gives_no_bound
#print axioms Erdos287.ResearchBankV17.ThinEffectivityFirewall.no_uniform_x0
#print axioms Erdos287.ResearchBankV17.ThinEffectivityFirewall.logP_regression
#print axioms Erdos287.ResearchBankV17.ThinEffectivityFirewall.v17_effectivity_firewall
#print axioms Erdos287.ResearchBankV17.ThinFunctional.toRouteC
#print axioms Erdos287.ResearchBankV17.ThinFunctional.thin_margin_pos
#print axioms Erdos287.ResearchBankV17.ThinFunctional.certificate_does_not_give_moments
#print axioms Erdos287.ResearchBankV17.ThinParameters.K_pos
#print axioms Erdos287.ResearchBankV17.ThinParameters.L_mul_delta
#print axioms Erdos287.ResearchBankV17.ThinParameters.L_ge_threshold
#print axioms Erdos287.ResearchBankV17.ThinSupportLedger.thresholds_ordered
#print axioms Erdos287.ResearchBankV17.ThinSupportLedger.support_comparisons
#print axioms Erdos287.ResearchBankV17.ThinSupportLedger.thetaD_comparisons
#print axioms Erdos287.ResearchBankV17.ThinSupportLedger.thetaD_certificate
#print axioms Erdos287.ResearchBankV17.ThinSupportLedger.provider_fails_linear
#print axioms Erdos287.ResearchBankV17.ThinSupportLedger.level_below_threshold_does_not_construct_provider
#print axioms Erdos287.ResearchBankV17.UniformThinning.bdelta_eq
#print axioms Erdos287.ResearchBankV17.UniformThinning.Ldelta_spec
#print axioms Erdos287.ResearchBankV17.UniformThinning.b_ge
#print axioms Erdos287.ResearchBankV17.UniformThinning.a_gt_b
#print axioms Erdos287.ResearchBankV17.UniformThinning.uniform_thinning_conditional
#print axioms Erdos287.ResearchBankV17.UniformThinning.no_uniform_x0
