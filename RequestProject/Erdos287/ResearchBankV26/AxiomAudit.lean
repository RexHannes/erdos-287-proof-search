import RequestProject.Erdos287.ResearchBankV26.RoughConvolution
import RequestProject.Erdos287.ResearchBankV26.HeathBrownIdentity
import RequestProject.Erdos287.ResearchBankV26.RoughSWAdapter
import RequestProject.Erdos287.ResearchBankV26.ProductIntervalBoxes
import RequestProject.Erdos287.ResearchBankV26.SingletonBins
import RequestProject.Erdos287.ResearchBankV26.DyadicSourceMap
import RequestProject.Erdos287.ResearchBankV26.HBBranchCoverage
import RequestProject.Erdos287.ResearchBankV26.BoundaryBudget
import RequestProject.Erdos287.ResearchBankV26.Ledger

/-!
# Erdős #287 — Research Bank V26: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V26 (57 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV26.RoughConvolution.primeIndicator_apply
#print axioms Erdos287.ResearchBankV26.RoughConvolution.primeIndicator_isMultiplicative
#print axioms Erdos287.ResearchBankV26.RoughConvolution.primeIndicator_prime_pow
#print axioms Erdos287.ResearchBankV26.RoughConvolution.sum_antidiag_prime_pow
#print axioms Erdos287.ResearchBankV26.RoughConvolution.moebius_prime_pow'
#print axioms Erdos287.ResearchBankV26.RoughConvolution.rough_mu_identity
#print axioms Erdos287.ResearchBankV26.RoughConvolution.rough_one_identity
#print axioms Erdos287.ResearchBankV26.RoughConvolution.rough_mu_identity_apply
#print axioms Erdos287.ResearchBankV26.RoughConvolution.rough_one_identity_apply
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.My_apply
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.Mb_apply_ne_zero
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.one_sub_zeta_My
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.supportedAbove_mul
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.zeta_Mb_supported
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.pow_supported
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.vanish_of_supported
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.dlt_mul_apply
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.hb_ring_identity
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.heath_brown_identity
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.heath_brown_k3
#print axioms Erdos287.ResearchBankV26.HeathBrownIdentity.hb_k3_at_most_six_variables
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.rough_truncation_split
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.H_nonneg_le_one
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.truncation_error_le
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.truncation_error_conditional
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.R_values
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.roughMu_oneBounded
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.roughMu_roughSupported
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.roughOne_oneBounded
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.roughOne_roughSupported
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.roughLog_roughSupported
#print axioms Erdos287.ResearchBankV26.RoughSWAdapter.rough_does_not_imply_SW
#print axioms Erdos287.ResearchBankV26.ProductIntervalBoxes.prod_bounds
#print axioms Erdos287.ResearchBankV26.ProductIntervalBoxes.interior_rectangular
#print axioms Erdos287.ResearchBankV26.ProductIntervalBoxes.exterior_zero
#print axioms Erdos287.ResearchBankV26.ProductIntervalBoxes.box_decomposition
#print axioms Erdos287.ResearchBankV26.ProductIntervalBoxes.product_boxing_conditional
#print axioms Erdos287.ResearchBankV26.ProductIntervalBoxes.boundary_bound_not_multiplied
#print axioms Erdos287.ResearchBankV26.SingletonBins.singleton_apply
#print axioms Erdos287.ResearchBankV26.SingletonBins.pad_singleton
#print axioms Erdos287.ResearchBankV26.SingletonBins.hb_term_six_variables
#print axioms Erdos287.ResearchBankV26.SingletonBins.singleton_bin_values
#print axioms Erdos287.ResearchBankV26.DyadicSourceMap.dyadic_mem
#print axioms Erdos287.ResearchBankV26.DyadicSourceMap.dyadic_unique
#print axioms Erdos287.ResearchBankV26.DyadicSourceMap.dyadic_partition_of_unity
#print axioms Erdos287.ResearchBankV26.DyadicSourceMap.source_sum_by_boxes
#print axioms Erdos287.ResearchBankV26.HBBranchCoverage.greedy_subset_sum
#print axioms Erdos287.ResearchBankV26.HBBranchCoverage.branch_trichotomy
#print axioms Erdos287.ResearchBankV26.HBBranchCoverage.trichotomy_fails_beyond
#print axioms Erdos287.ResearchBankV26.HBBranchCoverage.classify_spec
#print axioms Erdos287.ResearchBankV26.HBBranchCoverage.source_level_coverage
#print axioms Erdos287.ResearchBankV26.BoundaryBudget.sqrt_rpow_neg
#print axioms Erdos287.ResearchBankV26.BoundaryBudget.boundary_first_term
#print axioms Erdos287.ResearchBankV26.BoundaryBudget.boundary_second_term
#print axioms Erdos287.ResearchBankV26.BoundaryBudget.boundary_budget
#print axioms Erdos287.ResearchBankV26.Ledger.v26_final_status
#print axioms Erdos287.ResearchBankV26.Ledger.v26_bank_certificate
