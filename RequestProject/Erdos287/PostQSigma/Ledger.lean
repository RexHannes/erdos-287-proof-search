import RequestProject.Erdos287.QSigma
import RequestProject.Erdos287.PostQSigma.Conductor
import RequestProject.Erdos287.PostQSigma.Contacts
import RequestProject.Erdos287.PostQSigma.CoreCarry
import RequestProject.Erdos287.PostQSigma.DiameterPrimary
import RequestProject.Erdos287.PostQSigma.ExactMassAutomaton
import RequestProject.Erdos287.PostQSigma.FirstDigit
import RequestProject.Erdos287.PostQSigma.HardCore
import RequestProject.Erdos287.PostQSigma.MandatoryDecomp
import RequestProject.Erdos287.PostQSigma.MandatoryDeep
import RequestProject.Erdos287.PostQSigma.MandatoryLocal
import RequestProject.Erdos287.PostQSigma.MandatoryPrimary
import RequestProject.Erdos287.PostQSigma.PG287
import RequestProject.Erdos287.PostQSigma.PathCount
import RequestProject.Erdos287.PostQSigma.PrimaryCover
import RequestProject.Erdos287.PostQSigma.PrimeResonance
import RequestProject.Erdos287.PostQSigma.ProperModulusGram
import RequestProject.Erdos287.PostQSigma.QSigmaStrong
import RequestProject.Erdos287.PostQSigma.RawSource
import RequestProject.Erdos287.PostQSigma.SC287Firewall
import RequestProject.Erdos287.PostQSigma.SquareFirewall
import RequestProject.Erdos287.PostQSigma.StatusCarry
import RequestProject.Erdos287.PostQSigma.TerminalBridge
import RequestProject.Erdos287.PostQSigma.TransferMatrix
import RequestProject.Erdos287.PostQSigma.TranslatedRows

/-!
# Erdős #287 — post-`Q_Σ` bank: status ledger / owner graph (§43)

Machine-readable status ledger.  Every Lean declaration listed here is referenced with a
double-backtick name, so the file fails to compile if any listed declaration is missing.

**ERDŐS #287 REMAINS OPEN.**  The sole research owner is `PG287` (PG-287, proper-modulus Gram
capacity), which is *defined* but never proved, assumed globally or instantiated.  SC-287 is
RETIRED (`SC287.prime_moduleA_false` refutes its prime module on physical sources).
-/

namespace Erdos287.PostQSigma.Ledger

/-- Mathematical status labels. -/
inductive MathStatus
  | BANK | PAY | STRICT_REDUCE | PROVISIONAL | RETIRED | OPEN | CLOSED
  deriving Repr, DecidableEq

/-- Formal status categories. -/
inductive FormalStatus
  /-- proved in Lean, unconditionally -/
  | provedInLean
  /-- proved in Lean, conditional on an explicit provider/hypothesis -/
  | provedConditional
  /-- external formalised input -/
  | externalFormalised
  /-- external mathematical input not formalised locally -/
  | externalNotFormalised
  /-- paper-level internal result (not formalised) -/
  | paperLevel
  /-- open -/
  | open_
  deriving Repr, DecidableEq

/-- A ledger entry. -/
structure Entry where
  object : String
  decls : List Lean.Name
  math : MathStatus
  formal : FormalStatus
  note : String := ""

open MathStatus FormalStatus

/-- The status ledger. -/
def ledger : List Entry := [
  ⟨"original Erdős #287 (ordered form)", [``Erdos287.erdos287_seq_of_no_counterexample,
    ``Erdos287.Erdos287Counterexample], OPEN, open_, "remains open"⟩,
  ⟨"ExactSource", [``Erdos287.ExactSource.sourceSol_of_counterexample,
    ``Erdos287.ExactSource.counterexample_of_sourceSol, ``Erdos287.ExactSource.erdos287_iff_no_source,
    ``Erdos287.PostQSigma.original_erdos287_iff_exact_source], BANK, provedInLean, ""⟩,
  ⟨"QSigma", [``Erdos287.ExactSource.QSigma_dvd_prod,
    ``Erdos287.ExactSource.no_solution_of_QSigma_gt_Pmax], BANK, provedInLean,
    "universal QSigma > Pmax as final owner is RETIRED"⟩,
  ⟨"QSigmaStrong", [``Erdos287.PostQSigma.QSigmaStrong, ``Erdos287.PostQSigma.QSigmaStrong_dvd_prod,
    ``Erdos287.PostQSigma.GammaSum_le_factorization, ``Erdos287.PostQSigma.Qold_dvd_QSigmaStrong,
    ``Erdos287.PostQSigma.no_solution_of_QSigmaStrong_gt_Pmax,
    ``Erdos287.PostQSigma.Fixture.fixture_strict_improvement], BANK, provedInLean,
    "fixture V={2..7}, W=420, T=235 is DIAGNOSTIC"⟩,
  ⟨"weighted primary cover", [``Erdos287.PostQSigma.weighted_primary_cover_excludes,
    ``Erdos287.PostQSigma.no_solution_of_marginalLP_infeasible], BANK, provedInLean, ""⟩,
  ⟨"mandatory primary", [``Erdos287.PostQSigma.mandatory_subset_solution,
    ``Erdos287.PostQSigma.mandatory_adjacency_excludes, ``Erdos287.PostQSigma.infeasible_excludes],
    BANK, provedInLean, ""⟩,
  ⟨"exact-mass automaton", [``Erdos287.PostQSigma.exact_mass_automaton_iff,
    ``Erdos287.PostQSigma.modW_false_acceptance], BANK, provedInLean,
    "modulo-W automaton RETIRED (false acceptance fixture)"⟩,
  ⟨"V57 local criterion", [``Erdos287.PostQSigma.mandatory_iff_local,
    ``Erdos287.PostQSigma.selected_complement_congruence,
    ``Erdos287.PostQSigma.exists_unreachable_iff_deepest], BANK, provedInLean, ""⟩,
  ⟨"V57 deep classification", [``Erdos287.PostQSigma.deep_mandatory_classification,
    ``Erdos287.PostQSigma.deep_classification_needs_harmonic], BANK, provedInLean,
    "needs H(a,M) ≥ 1; 2a ≤ M alone is insufficient (counterfixture (22,50))"⟩,
  ⟨"MAND = MAND1 ∪ Ddeep", [``Erdos287.PostQSigma.mandatory_eq_first_digit_union_deep_exception,
    ``Erdos287.PostQSigma.Ddeep_disjoint, ``Erdos287.PostQSigma.Ddeep_localised], BANK, provedInLean, ""⟩,
  ⟨"|Ddeep| ≤ 5", [], BANK, paperLevel, "not formalised"⟩,
  ⟨"first-digit structure", [``Erdos287.PostQSigma.firstDigit_mandatory_no_endpoint,
    ``Erdos287.PostQSigma.firstDigit_singleton, ``Erdos287.PostQSigma.firstDigit_pair_iff],
    BANK, provedInLean, "size ≤ 3 classification not supplied / not formalised"⟩,
  ⟨"harmonic corridor", [``Erdos287.PostQSigma.harmonic_source_le_half,
    ``Erdos287.PostQSigma.exp_mul_pred_lt_of_harmonic, ``Erdos287.PostQSigma.eight_mul_pred_lt_three_mul,
    ``Erdos287.PostQSigma.counterexample_corridor], BANK, provedInLean, ""⟩,
  ⟨"translated-row theorem", [``Erdos287.PostQSigma.translated_row_mandatory,
    ``Erdos287.PostQSigma.fixture_prefix_fails, ``Erdos287.PostQSigma.fixture_translated_ok],
    BANK, provedInLean, ""⟩,
  ⟨"every-M contacts", [``Erdos287.PostQSigma.contacts_card_ge, ``Erdos287.PostQSigma.ContactSupply],
    BANK, provedConditional, "explicit prime-count supply isolated as provider ContactSupply"⟩,
  ⟨"owner-disjoint matching", [``Erdos287.PostQSigma.contact_matching,
    ``Erdos287.PostQSigma.greedy_matching, ``Erdos287.PostQSigma.distinct_rows_activated],
    BANK, provedInLean, ""⟩,
  ⟨"diameter-primary cap", [``Erdos287.PostQSigma.diameter_primary_cap,
    ``Erdos287.PostQSigma.top_strip_omitted], BANK, provedInLean, ""⟩,
  ⟨"contact defect", [``Erdos287.PostQSigma.defect_contradiction,
    ``Erdos287.PostQSigma.ContactDefect287], PROVISIONAL, open_, "ContactDefect287 defined, not asserted"⟩,
  ⟨"exact core/carry identity", [``Erdos287.PostQSigma.CoreCarry.core_carry_identity,
    ``Erdos287.PostQSigma.CoreCarry.core_carry_iff], BANK, provedInLean, ""⟩,
  ⟨"contact-carry bridge", [``Erdos287.PostQSigma.CoreCarry.contact_carry_lower_bound,
    ``Erdos287.PostQSigma.CoreCarry.contact_carry_cut], PAY, provedConditional,
    "conditional on the abundance/path-geometry hypotheses stated in CoreCarry.Hyp"⟩,
  ⟨"three-status GF / carry cosets", [``Erdos287.PostQSigma.StatusCarry.three_status_factorisation,
    ``Erdos287.PostQSigma.StatusCarry.carry_modEq, ``Erdos287.PostQSigma.StatusCarry.gco_eq,
    ``Erdos287.PostQSigma.StatusCarry.gco_eq_one_of_lcm_complete], BANK, provedInLean, ""⟩,
  ⟨"square-certificate firewall", [``Erdos287.PostQSigma.square_certificate_excludes,
    ``Erdos287.PostQSigma.interpolation_firewall, ``Erdos287.PostQSigma.punctured_cube_degree],
    BANK, provedInLean, "arbitrary-degree polynomial certificate RETIRED"⟩,
  ⟨"approximate-mass firewall (Croot)", [], RETIRED, externalNotFormalised,
    "fixed Archimedean mass gap RETIRED; Croot construction not formalised"⟩,
  ⟨"hard-core coefficient", [``Erdos287.PostQSigma.hard_core_coefficient_exact], BANK, provedInLean, ""⟩,
  ⟨"no-wrap", [``Erdos287.PostQSigma.no_wrap, ``Erdos287.PostQSigma.no_wrap_recip], BANK, provedInLean, ""⟩,
  ⟨"root-of-unity filter", [``Erdos287.PostQSigma.root_of_unity_exact_coefficient], BANK, provedInLean, ""⟩,
  ⟨"conductor decomposition", [``Erdos287.PostQSigma.physical_conductor_decomposition,
    ``Erdos287.PostQSigma.conductor_decomposition], BANK, provedInLean, ""⟩,
  ⟨"Ramanujan blocks", [``Erdos287.PostQSigma.A_eq_sum_ramanujan,
    ``Erdos287.PostQSigma.physical_ramanujan_block_identity], BANK, provedInLean, ""⟩,
  ⟨"transfer matrix", [``Erdos287.PostQSigma.Transfer.Zw_succ_succ,
    ``Erdos287.PostQSigma.Transfer.transfer_matrix_product], BANK, provedInLean,
    "no spectral/contraction claim"⟩,
  ⟨"prime resonance firewall", [``Erdos287.PostQSigma.prime_resonance_dvd_iff,
    ``Erdos287.PostQSigma.prime_resonance_fib, ``Erdos287.PostQSigma.SC287.abs_A_p_lower,
    ``Erdos287.PostQSigma.SC287.prime_moduleA_false], BANK, provedInLean,
    "prime square-root Module A RETIRED"⟩,
  ⟨"composite resonance firewall", [], RETIRED, externalNotFormalised,
    "needs PNT + affine Selberg upper bound; not formalised"⟩,
  ⟨"SC-287", [``Erdos287.PostQSigma.SC287.PrimeModuleA], RETIRED, provedInLean,
    "prime module refuted in Lean; aggregate version retired on V64 authority"⟩,
  ⟨"proper-modulus set", [``Erdos287.PostQSigma.Lset, ``Erdos287.PostQSigma.proper_modulus_firewall],
    BANK, provedInLean, ""⟩,
  ⟨"Gram PSD", [``Erdos287.PostQSigma.proper_modulus_gram_psd, ``Erdos287.PostQSigma.gram_psd],
    BANK, provedInLean, ""⟩,
  ⟨"exact Gram majorant", [``Erdos287.PostQSigma.proper_modulus_majorant,
    ``Erdos287.PostQSigma.gram_majorant], BANK, provedInLean, ""⟩,
  ⟨"PG strictness fixture W=30", [``Erdos287.PostQSigma.W30.constrained_optimum_ge_one,
    ``Erdos287.PostQSigma.W30.target_absent], BANK, provedInLean, "DIAGNOSTIC"⟩,
  ⟨"PG-287", [``Erdos287.PostQSigma.PG287], OPEN, open_, "sole research owner; never instantiated"⟩,
  ⟨"psi(M) ≥ 0.9M", [``Erdos287.PostQSigma.PsiLowerBound], BANK, externalNotFormalised,
    "explicit hypothesis only"⟩,
  ⟨"finite exclusion interface", [``Erdos287.PostQSigma.FiniteExclusionUpTo,
    ``Erdos287.PostQSigma.finiteExclusionUpTo_4e9], BANK, provedInLean,
    "4e9 proved; Huang U_fin certificate absent"⟩,
  ⟨"PG tail theorem", [``Erdos287.PostQSigma.PG287_implies_no_tail_source,
    ``Erdos287.PostQSigma.no_large_counterexample_of_PG287], STRICT_REDUCE, provedConditional, ""⟩,
  ⟨"finite/tail splice", [``Erdos287.PostQSigma.finite_exclusion_and_PG287_imply_erdos287,
    ``Erdos287.PostQSigma.erdos287_of_PG287_repository_native], STRICT_REDUCE, provedConditional,
    "conditional on PG287, PsiLowerBound and finite exclusion"⟩,
  ⟨"global QSigma > Pmax owner", [], RETIRED, paperLevel, ""⟩,
  ⟨"finite-coverage extension owner", [], RETIRED, paperLevel, ""⟩,
  ⟨"pure > 1/2 mandatory packing", [], RETIRED, paperLevel, ""⟩,
  ⟨"unary-forcing accumulation closure", [], RETIRED, paperLevel, ""⟩,
  ⟨"Maynard graph pigeonhole repair", [], RETIRED, paperLevel, ""⟩,
  ⟨"automatic CRT tensorisation", [], RETIRED, paperLevel, ""⟩,
  ⟨"modulo-W automaton", [``Erdos287.PostQSigma.modW_false_acceptance], RETIRED, provedInLean, ""⟩
]

/-- The current research frontier consists of exactly one OPEN owner besides the original
problem itself. -/
theorem open_entries :
    (ledger.filter (fun e => decide (e.math = MathStatus.OPEN))).map Entry.object =
      ["original Erdős #287 (ordered form)", "PG-287"] := by
  decide

end Erdos287.PostQSigma.Ledger
