import RequestProject.Erdos287.CurrentTail.AxiomAudit
import RequestProject.Erdos287.SourceChain.TypeIISplit
import RequestProject.Erdos287.SourceChain.ZeroModeCovariance
import RequestProject.Erdos287.SourceChain.PoissonRemainder
import RequestProject.Erdos287.SourceChain.ScalarWeight
import RequestProject.Erdos287.SourceChain.AffinePhase
import RequestProject.Erdos287.SourceChain.FourierPoisson
import RequestProject.Erdos287.SourceChain.CleanFAA
import RequestProject.Erdos287.SourceChain.SpectralExponent
import RequestProject.Erdos287.SourceChain.Separation
import RequestProject.Erdos287.SourceChain.MinimalTail
import RequestProject.Erdos287.SourceChain.PaymentCalculus
import RequestProject.Erdos287.SourceChain.PieceDerivations
import RequestProject.Erdos287.SourceChain.NarrowTail
import RequestProject.Erdos287.SourceChain.ClosureDAG
import RequestProject.Erdos287.SourceChain.ActualAtomW4Comparison
import RequestProject.Erdos287.SourceChain.UpstreamRepairs

/-!
# Erdős #287 — source chain: trust / axiom / provider audit (build time)

* `#sc_assert_all_std_axioms` — fails the build unless **every** theorem in the namespace
  `Erdos287.SourceChain` depends only on `propext`, `Classical.choice`, `Quot.sound`
  (rejects `sorryAx`, any project axiom and `Lean.ofReduceBool`, i.e. `native_decide`).
* `#ct_assert_std_axioms` on each principal theorem (printed individually).
* `#ct_assert_avoids` — no source-chain provider mentions `R_Σ^P`, the tail statement,
  counterexamples or exact words; the narrow analytic providers additionally do not mention the
  little-o target or the tail source family.
* `#ct_assert_mentions` — the conditional tail theorems visibly carry their inputs.
-/

open Lean Elab Command Meta

elab "#sc_assert_all_std_axioms" : command => do
  let env ← getEnv
  let pre : Name := `Erdos287.SourceChain
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    unless pre.isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless ok.contains a do throwError "{n} depends on non-standard axiom {a}"
    count := count + 1
  logInfo m!"SourceChain: all {count} theorems use only standard axioms"

#sc_assert_all_std_axioms

/-! ## Providers never contain their downstream conclusion -/

#ct_assert_avoids Erdos287.SourceChain.PascadiSpectralY [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_avoids Erdos287.SourceChain.SharpMembership [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_avoids Erdos287.SourceChain.PascadiRangeExport
  [Erdos287.CurrentTail.TensorSource.RSigmaP, Erdos287.CurrentTail.Tail287Statement,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord,
  Erdos287.CurrentTail.IsLittleOTarget, Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_avoids Erdos287.SourceChain.OrderingBPoissonReduction
  [Erdos287.CurrentTail.TensorSource.RSigmaP, Erdos287.CurrentTail.Tail287Statement,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord,
  Erdos287.CurrentTail.IsLittleOTarget]
#ct_assert_avoids Erdos287.SourceChain.PiecePaid [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.SourceChain.CenteringPaid [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.SourceChain.CoprimalityPaid [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord]
#ct_assert_avoids Erdos287.SourceChain.SpectatorReciprocalNorm
  [Erdos287.CurrentTail.TensorSource.RSigmaP, Erdos287.CurrentTail.Tail287Statement,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord,
  Erdos287.CurrentTail.IsLittleOTarget]
#ct_assert_avoids Erdos287.SourceChain.PowerSavingCell [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget]
#ct_assert_avoids Erdos287.SourceChain.LogSavingCell [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget]

/-! ## The conditional tail theorems visibly carry their inputs -/

#ct_assert_mentions Erdos287.SourceChain.Tail287_of_MinimalAnalyticProviders
  [Erdos287.CurrentTail.SevenBlockTailFramework, Erdos287.CurrentTail.BaseSWProvider,
  Erdos287.SourceChain.CoprimalityPaid, Erdos287.SourceChain.OrderingBPoissonReduction,
  Erdos287.SourceChain.CenteringPaid, Erdos287.SourceChain.PiecePaid]
#ct_assert_mentions Erdos287.SourceChain.Tail287_of_NarrowProviders
  [Erdos287.CurrentTail.SevenBlockTailFramework, Erdos287.CurrentTail.BaseSWProvider,
  Erdos287.SourceChain.CoprimalityPaid, Erdos287.SourceChain.OrderingBPoissonReduction,
  Erdos287.SourceChain.CenteringPaid, Erdos287.SourceChain.PiecePaid,
  Erdos287.SourceChain.PascadiSpectralY, Erdos287.SourceChain.SharpMembership,
  Erdos287.SourceChain.SpectatorReciprocalNorm]

/-! ## Axioms of the principal theorems (printed) -/

-- §2 Ordering-B source dictionary
#ct_assert_std_axioms Erdos287.SourceChain.typeII_split
#ct_assert_std_axioms Erdos287.SourceChain.typeII_split_sum
#ct_assert_std_axioms Erdos287.SourceChain.secondTerm_eq_DeltaRel
#ct_assert_std_axioms Erdos287.SourceChain.residueFibre_card_le
#ct_assert_std_axioms Erdos287.SourceChain.residueFibre_density
#ct_assert_std_axioms Erdos287.SourceChain.orderingB_physical_square
#ct_assert_std_axioms Erdos287.SourceChain.zeroMode_covariance
#ct_assert_std_axioms Erdos287.SourceChain.zeroMode_covariance_full
#ct_assert_std_axioms Erdos287.SourceChain.poissonP_scale
-- §3 F_AB
#ct_assert_std_axioms Erdos287.SourceChain.rho_factor
#ct_assert_std_axioms Erdos287.SourceChain.rho_crt
#ct_assert_std_axioms Erdos287.SourceChain.poissonP_rho
#ct_assert_std_axioms Erdos287.SourceChain.lattice_discrepancy
#ct_assert_std_axioms Erdos287.SourceChain.PF_scale
#ct_assert_std_axioms Erdos287.SourceChain.PF_decay_bound
#ct_assert_std_axioms Erdos287.SourceChain.k1_modulus_exponent
#ct_assert_std_axioms Erdos287.SourceChain.FABData.FAB_eq_sum_PF
#ct_assert_std_axioms Erdos287.SourceChain.FABData.FAB_split
#ct_assert_std_axioms Erdos287.SourceChain.FABData.FAB_kgt1_count
#ct_assert_std_axioms Erdos287.SourceChain.AB2_cauchy
#ct_assert_std_axioms Erdos287.SourceChain.fabKgt1_cell_bound
-- §4 clean F_AA♯
#ct_assert_std_axioms Erdos287.SourceChain.FAAData.FAA_eq_sectors
#ct_assert_std_axioms Erdos287.SourceChain.FAAData.clean_conditions
#ct_assert_std_axioms Erdos287.SourceChain.FAAData.commonN_empty_of_not_rough
#ct_assert_std_axioms Erdos287.SourceChain.AA1_cauchy
#ct_assert_std_axioms Erdos287.SourceChain.nearDiag_cauchy
#ct_assert_std_axioms Erdos287.SourceChain.zeroMode_full_vanishes
#ct_assert_std_axioms Erdos287.SourceChain.rec1_recombination
#ct_assert_std_axioms Erdos287.SourceChain.aaShape_cell_bound
#ct_assert_std_axioms Erdos287.SourceChain.nearDiag_cell_bound
-- §5 scalar weight
#ct_assert_std_axioms Erdos287.SourceChain.lowHigh_unique
#ct_assert_std_axioms Erdos287.SourceChain.abs_Gamma1_le_one
#ct_assert_std_axioms Erdos287.SourceChain.scalarWeight_eq_sectors
#ct_assert_std_axioms Erdos287.SourceChain.labelled_eq_canonical
#ct_assert_std_axioms Erdos287.SourceChain.canonical_gamma_one
#ct_assert_std_axioms Erdos287.SourceChain.parity_sign_routing
-- §6 range / separation
#ct_assert_std_axioms Erdos287.SourceChain.PascadiRangeExport.ineq2_holds
#ct_assert_std_axioms Erdos287.SourceChain.Q1_absorb
#ct_assert_std_axioms Erdos287.SourceChain.hsep_cost_subpower
#ct_assert_std_axioms Erdos287.SourceChain.hsep_membership
#ct_assert_std_axioms Erdos287.SourceChain.eErrors_absent_at_one
-- §7 affine phase
#ct_assert_std_axioms Erdos287.SourceChain.affine_phase_decomposition
#ct_assert_std_axioms Erdos287.SourceChain.fixedLocal_split_phase
#ct_assert_std_axioms Erdos287.SourceChain.ph1_phase
#ct_assert_std_axioms Erdos287.SourceChain.ph1_ePhase
-- §9–10 T_H and ledger
#ct_assert_std_axioms Erdos287.SourceChain.th_exponent_propagation
#ct_assert_std_axioms Erdos287.SourceChain.QuantitativeTH_of_spectralY
#ct_assert_std_axioms Erdos287.SourceChain.messageLedger_coefficient
#ct_assert_std_axioms Erdos287.SourceChain.ledger_391_iff
#ct_assert_std_axioms Erdos287.SourceChain.TH3_of_sigma_lt
#ct_assert_std_axioms Erdos287.SourceChain.sharp_cell_bound
#ct_assert_std_axioms Erdos287.SourceChain.sharp_powerSaving
-- §11–14 payments and conditional tails
#ct_assert_std_axioms Erdos287.SourceChain.RrelMain_eq_sum_Sxi
#ct_assert_std_axioms Erdos287.SourceChain.cell_bound
#ct_assert_std_axioms Erdos287.SourceChain.RrelMain_bound
#ct_assert_std_axioms Erdos287.SourceChain.piecePaid_of_powerSaving
#ct_assert_std_axioms Erdos287.SourceChain.piecePaid_of_logSaving
#ct_assert_std_axioms Erdos287.SourceChain.centeringPaid_of_RBDH
#ct_assert_std_axioms Erdos287.SourceChain.RSigmaP_littleO_of_minimal
#ct_assert_std_axioms Erdos287.SourceChain.Tail287_of_MinimalAnalyticProviders
#ct_assert_std_axioms Erdos287.SourceChain.sharpPaid_of_spectralY
#ct_assert_std_axioms Erdos287.SourceChain.Tail287_of_NarrowProviders
-- §17 closure DAG
#ct_assert_std_axioms Erdos287.SourceChain.scDag_acyclic
#ct_assert_std_axioms Erdos287.SourceChain.scOrderingA_no_path_to_tail
#ct_assert_std_axioms Erdos287.SourceChain.scMetadata_feeds_nothing
#ct_assert_std_axioms Erdos287.SourceChain.scGlobal_preds
#ct_assert_std_axioms Erdos287.SourceChain.scTail_reaches_global
#ct_assert_std_axioms Erdos287.SourceChain.scSplice_reaches_global
#ct_assert_std_axioms Erdos287.SourceChain.scTerminal_statuses

/-! ## Actual-atom → positive `W₄` layer -/

#ct_assert_avoids Erdos287.SourceChain.W4DiagEstimate [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_avoids Erdos287.SourceChain.W4RamEstimate [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_avoids Erdos287.SourceChain.W4SpecEstimate [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.CurrentTail.TailSourceFamily, Erdos287.SourceChain.pascadiInnerOld]
#ct_assert_avoids Erdos287.SourceChain.specRHS [Erdos287.SourceChain.pascadiInnerOld]
#ct_assert_avoids Erdos287.SourceChain.AstraAtomBound [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_mentions Erdos287.SourceChain.Tail287_of_AtomProviders
  [Erdos287.CurrentTail.SevenBlockTailFramework, Erdos287.CurrentTail.BaseSWProvider,
  Erdos287.SourceChain.CoprimalityPaid, Erdos287.SourceChain.OrderingBPoissonReduction,
  Erdos287.SourceChain.CenteringPaid, Erdos287.SourceChain.PiecePaid,
  Erdos287.SourceChain.AstraAtomBound, Erdos287.SourceChain.SpectatorReciprocalNorm]

#ct_assert_std_axioms Erdos287.SourceChain.CleanAtom.noDilation_phase
#ct_assert_std_axioms Erdos287.SourceChain.colour_deletion_counterfixture
#ct_assert_std_axioms Erdos287.SourceChain.unit_class_expansion
#ct_assert_std_axioms Erdos287.SourceChain.unit_class_expansion_factor
#ct_assert_std_axioms Erdos287.SourceChain.character_mass_le
#ct_assert_std_axioms Erdos287.SourceChain.fixedPhase_den_le
#ct_assert_std_axioms Erdos287.SourceChain.source_to_W4
#ct_assert_std_axioms Erdos287.SourceChain.fixedA_domination
#ct_assert_std_axioms Erdos287.SourceChain.cauchy_prefactor_bound
#ct_assert_std_axioms Erdos287.SourceChain.regr_old_FHS
#ct_assert_std_axioms Erdos287.SourceChain.pascadiInner_ge_old
#ct_assert_std_axioms Erdos287.SourceChain.W4_bound_of_pieces
#ct_assert_std_axioms Erdos287.SourceChain.TH_sqrt_propagation
#ct_assert_std_axioms Erdos287.SourceChain.packet_exponent
#ct_assert_std_axioms Erdos287.SourceChain.astra_packet_391
#ct_assert_std_axioms Erdos287.SourceChain.v101_packet_775
#ct_assert_std_axioms Erdos287.SourceChain.astra_strong_to_weak
#ct_assert_std_axioms Erdos287.SourceChain.colourClass_coprime
#ct_assert_std_axioms Erdos287.SourceChain.colourings_card
#ct_assert_std_axioms Erdos287.SourceChain.coprime_indicator_identity
#ct_assert_std_axioms Erdos287.SourceChain.route_final_of_kernel
#ct_assert_std_axioms Erdos287.SourceChain.no_retired_shortcut
#ct_assert_std_axioms Erdos287.SourceChain.sharpPowerSaving_of_atom
#ct_assert_std_axioms Erdos287.SourceChain.sharpPaid_of_atom
#ct_assert_std_axioms Erdos287.SourceChain.Tail287_of_AtomProviders

/-! ## Exact signatures of the conditional tail theorems -/

#check @Erdos287.SourceChain.Tail287_of_MinimalAnalyticProviders
#check @Erdos287.SourceChain.Tail287_of_NarrowProviders
#check @Erdos287.SourceChain.Tail287_of_AtomProviders
#print axioms Erdos287.SourceChain.Tail287_of_MinimalAnalyticProviders

/-! ## Upstream repairs (final Astra audit) -/

#ct_assert_avoids Erdos287.SourceChain.TwoLargeEstimate [Erdos287.CurrentTail.TensorSource.RSigmaP,
  Erdos287.CurrentTail.Tail287Statement, Erdos287.Erdos287Counterexample,
  Erdos287.PostV71V87.ExactWord, Erdos287.CurrentTail.IsLittleOTarget,
  Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_avoids Erdos287.SourceChain.UpperSieveWellFactorable
  [Erdos287.CurrentTail.TensorSource.RSigmaP, Erdos287.CurrentTail.Tail287Statement,
  Erdos287.Erdos287Counterexample, Erdos287.PostV71V87.ExactWord,
  Erdos287.CurrentTail.IsLittleOTarget, Erdos287.CurrentTail.TailSourceFamily]
#ct_assert_std_axioms Erdos287.SourceChain.upperSieveSupport_prod_lt
#ct_assert_std_axioms Erdos287.SourceChain.large_count_le_two
#ct_assert_std_axioms Erdos287.SourceChain.prefix_hits_window
#ct_assert_std_axioms Erdos287.SourceChain.twoLarge_cell_saving
#ct_assert_std_axioms Erdos287.SourceChain.pair_coefficient
#ct_assert_std_axioms Erdos287.SourceChain.pair_coefficient_safety
#ct_assert_std_axioms Erdos287.SourceChain.partition_after_power_saving
#ct_assert_std_axioms Erdos287.SourceChain.partition_on_log_saving_fails
