import RequestProject.Erdos287.PostV64V71.RegressionFixtures
import RequestProject.Erdos287.PostQSigma.Ledger

/-!
# Erdős #287 — CURRENT status ledger (V67–V71 frontier)

This ledger **supersedes as current** the historical `PostQSigma/Ledger.lean`, which is left
untouched (its `open_entries` theorem remains correct for that historical status universe:
it reported only the original problem and PG-287).

Every Lean declaration listed is referenced by a double-backtick name, so this file fails to
compile if any listed declaration is missing.

**ERDŐS #287 REMAINS OPEN.**  The current research owner is `DeterminantSupply287` (OPEN).
The global theorem additionally needs the absent finite certificate (`HuangFiniteExclusion287`)
and the external explicit Chebyshev bound (`LcmUpperBound12`).
-/

namespace Erdos287.PostV64V71.CurrentLedger

/-- Mathematical status. -/
inductive MathStatus
  | BANK | PAY | STRICT_REDUCE | PROVISIONAL | RETIRED | OPEN | CLOSED
  deriving Repr, DecidableEq

/-- Formal status (exactly the five classes; never identified with the mathematical status). -/
inductive FormalStatus
  /-- LEAN PROVED -/
  | leanProved
  /-- LEAN PROVED CONDITIONAL ON EXPLICIT INPUT -/
  | leanProvedConditional
  /-- KNOWN EXTERNAL MATHEMATICS / NOT FORMALISED LOCALLY -/
  | externalNotFormalised
  /-- PAPER-LEVEL INTERNAL PROOF / NOT YET LEAN -/
  | paperLevel
  /-- OPEN -/
  | open_
  deriving Repr, DecidableEq

/-- The role of an entry in the dependency graph. -/
inductive Role
  | original | bank | researchOwner | proposedRoute | externalInput | missingCertificate
  | historical
  deriving Repr, DecidableEq

/-- A ledger entry. -/
structure Entry where
  object : String
  decls : List Lean.Name
  math : MathStatus
  formal : FormalStatus
  role : Role
  note : String := ""

open MathStatus FormalStatus Role

/-- The current ledger. -/
def ledger : List Entry := [
  ⟨"original Erdős #287", [``Erdos287.erdos287_seq_of_no_counterexample,
    ``Erdos287.Erdos287Counterexample], OPEN, open_, original, "remains open"⟩,
  -- V67
  ⟨"V67 pinned selected-mass identity X(E) = P(D - Y(A))",
    [``Erdos287.PostV64V71.pinned_selected_mass, ``Erdos287.PostV64V71.pinned_selected_mass_iff,
     ``Erdos287.PostV64V71.pinned_W_dvd_iff, ``Erdos287.PostV64V71.pinned_D_dvd_iff_of_coprime,
     ``Erdos287.PostV64V71.pinned_mass_bounds], BANK, leanProved, bank,
    "REPAIR: third equivalent is W | X(E) (or D | X(E) under gcd(P,D)=1)"⟩,
  ⟨"V67 pinned D | X(E) literal reading", [``Erdos287.PostV64V71.pinned_D_dvd_counterfixture],
    RETIRED, leanProved, bank, "algebraic counterfixture P = D = 2, Y = 1"⟩,
  ⟨"V67 free-component factorisation",
    [``Erdos287.PostV64V71.compPoly_union, ``Erdos287.PostV64V71.compPoly_biUnion,
     ``Erdos287.PostV64V71.component_coefficient_factorization,
     ``Erdos287.PostV64V71.compCount_of_neg, ``Erdos287.PostV64V71.forced_restricted_count_eq],
    BANK, leanProved, bank, "no universal coefficient vanishing claimed"⟩,
  -- V68/V69
  ⟨"V68 reciprocal fingerprint Xi_H and good-row emptiness",
    [``Erdos287.PostV64V71.recipSums, ``Erdos287.PostV64V71.Xi, ``Erdos287.PostV64V71.num_dvd_Xi,
     ``Erdos287.PostV64V71.exists_cofactor_set, ``Erdos287.PostV64V71.good_large_prime_row_empty],
    BANK, leanProved, bank, ""⟩,
  ⟨"Xi_H integer size bank", [``Erdos287.PostV64V71.num_le_BH, ``Erdos287.PostV64V71.Xi_le_BH_pow,
     ``Erdos287.PostV64V71.Xi_le_BH_pow_two_pow], BANK, leanProved, bank, ""⟩,
  ⟨"Xi_H log budget log Xi_H < 2M/L^5", [``Erdos287.PostV64V71.FingerprintLogBound287,
     ``Erdos287.PostV64V71.fingerprintLogBound_of_lcm], PAY, leanProvedConditional, bank,
    "proved in Lean from LcmUpperBound12 (psi(n) <= 1.2 n)"⟩,
  ⟨"exceptional primes E_H and B_E <= log Xi_H",
    [``Erdos287.PostV64V71.exceptionalPrimes, ``Erdos287.PostV64V71.prod_exceptionalPrimes_dvd_Xi,
     ``Erdos287.PostV64V71.BE_le_log_Xi], BANK, leanProved, bank, ""⟩,
  ⟨"residual denominator D2 divisibility", [``Erdos287.PostV64V71.D2,
     ``Erdos287.PostV64V71.Gap2CE.selected_dvd_D2], BANK, leanProved, bank, ""⟩,
  ⟨"D2 log bound 0.872 M / log M", [``Erdos287.PostV64V71.D2LogBound287], PAY, paperLevel,
    externalInput, "not used by the V71 tail chain"⟩,
  ⟨"V69 upper-half singleton prime omission", [``Erdos287.PostV64V71.Gap2CE.upper_half_prime_omitted,
     ``Erdos287.PostV64V71.Gap2CE.upper_half_prime_neighbours], BANK, leanProved, bank,
    "independent of Xi_H"⟩,
  -- V70
  ⟨"V70 all good multiples omitted", [``Erdos287.PostV64V71.Gap2CE.all_good_multiples_omitted],
    BANK, leanProved, bank, ""⟩,
  ⟨"V70 forced neighbours selected", [``Erdos287.PostV64V71.Gap2CE.forced_neighbours_selected],
    BANK, leanProved, bank, ""⟩,
  ⟨"V70 neighbour LCM rough part R_x | Xi_H", [``Erdos287.PostV64V71.LambdaX,
     ``Erdos287.PostV64V71.roughPart, ``Erdos287.PostV64V71.Gap2CE.roughPart_dvd_Xi,
     ``Erdos287.PostV64V71.Gap2CE.log_roughPart_lt], BANK, leanProved, bank, ""⟩,
  ⟨"V70 determinant parametrisation", [``Erdos287.PostV64V71.detBox, ``Erdos287.PostV64V71.det_eq,
     ``Erdos287.PostV64V71.rough_factor_iff_determinant_tuple], BANK, leanProved, bank, ""⟩,
  -- V71
  ⟨"V71 owner multiplicity <= 2H", [``Erdos287.PostV64V71.owner_multiplicity_le_twoH_r,
     ``Erdos287.PostV64V71.owner_multiplicity_le_twoH_q], BANK, leanProved, bank,
    "supersedes the older 2H^2 accounting"⟩,
  ⟨"V71 exception deletion loss", [``Erdos287.PostV64V71.exception_weight_loss], BANK, leanProved,
    bank, "0 <= D_theta - D_gg <= 4 H L B_E"⟩,
  ⟨"V71 von Mangoldt prime-power contamination",
    [``Erdos287.PostV64V71.mangoldt_prime_power_error_exact,
     ``Erdos287.PostV64V71.mangoldt_prime_power_error, ``Erdos287.PostV64V71.PPW_le], BANK,
    leanProved, bank, "Lean constant 8 H sqrt(M) L^2 (paper: 4); closure margin unaffected"⟩,
  ⟨"canonical height facts for M >= 2^1500", [``Erdos287.PostV64V71.canonical_height_facts,
     ``Erdos287.PostV64V71.Hcan_ge_twelve], BANK, leanProved, bank, ""⟩,
  ⟨"D_Lambda > 13M/L^3 => D_theta > 12M/L^3",
    [``Erdos287.PostV64V71.supply_implies_theta_supply], BANK, leanProved, bank, ""⟩,
  ⟨"V71 local admissibility and forbidden residues",
    [``Erdos287.PostV64V71.local_determinant_admissibility,
     ``Erdos287.PostV64V71.determinant_parametrisation, ``Erdos287.PostV64V71.no_common_root,
     ``Erdos287.PostV64V71.local_forbidden_residue_count, ``Erdos287.PostV64V71.parity_collapse],
    BANK, leanProved, bank, ""⟩,
  ⟨"exact local singular factor", [``Erdos287.PostV64V71.local_factor_ratio,
     ``Erdos287.PostV64V71.singularSeries], BANK, leanProved, bank, ""⟩,
  ⟨"average singular series", [``Erdos287.PostV64V71.AverageSingularSeries287], PAY, paperLevel,
    externalInput, "uninhabited"⟩,
  ⟨"weighted correlation C_K <= D_Lambda", [``Erdos287.PostV64V71.CK,
     ``Erdos287.PostV64V71.weighted_subbox_le_full_supply], BANK, leanProved, bank, ""⟩,
  ⟨"circle-method identity", [``Erdos287.PostV64V71.circle_correlation_identity], BANK, leanProved,
    bank, ""⟩,
  ⟨"exact major/minor decomposition", [``Erdos287.PostV64V71.major_minor_exact_decomposition,
     ``Erdos287.PostV64V71.major_minor_exact_decomposition_V71], BANK, leanProved, bank, ""⟩,
  ⟨"Siegel–Walfisz for logarithmic moduli", [``Erdos287.PostV64V71.SiegelWalfiszLogModuli287],
    BANK, externalNotFormalised, externalInput, "ineffective constants; uninhabited"⟩,
  ⟨"eventual major-arc asymptotic", [``Erdos287.PostV64V71.EventualMajorArc287], PAY, paperLevel,
    externalInput, "uses Siegel–Walfisz; ineffective; uninhabited"⟩,
  ⟨"effective major-arc lower bound with onset <= 2^1500",
    [``Erdos287.PostV64V71.EffectiveMajorArc287], OPEN, open_, proposedRoute,
    "must not be inferred from the eventual form"⟩,
  ⟨"SignedMinorArcLowerBound287", [``Erdos287.PostV64V71.MinorArcLowerBound287], OPEN, open_,
    proposedRoute, "current preferred analytic route"⟩,
  ⟨"route: effective major + minor => supply",
    [``Erdos287.PostV64V71.minor_plus_effective_major_implies_supply], STRICT_REDUCE,
    leanProvedConditional, bank, ""⟩,
  ⟨"effectivity firewall", [``Erdos287.PostV64V71.effectivity_firewall,
     ``Erdos287.PostV64V71.splice_requires_explicit_onset], BANK, leanProved, bank, ""⟩,
  ⟨"DeterminantSupply287", [``Erdos287.PostV64V71.DeterminantSupply287], OPEN, open_,
    researchOwner, "CURRENT sole analytic supply owner; never instantiated"⟩,
  ⟨"tail theorem: supply => no counterexample above 2^1500",
    [``Erdos287.PostV64V71.determinant_supply_excludes_source,
     ``Erdos287.PostV64V71.determinant_supply_implies_no_tail,
     ``Erdos287.PostV64V71.determinant_supply_implies_no_tail'], STRICT_REDUCE,
    leanProvedConditional, bank, "conditional on DeterminantSupply287 and LcmUpperBound12"⟩,
  ⟨"current route independent of ContactSupply / |Ddeep| <= 5 / first-digit classification",
    [``Erdos287.PostV64V71.determinant_supply_implies_no_tail'], BANK, leanProved, bank,
    "the tail theorem's only hypotheses are DeterminantSupply287 and LcmUpperBound12"⟩,
  ⟨"explicit Chebyshev bound psi(n) <= 1.2 n", [``Erdos287.PostV64V71.LcmUpperBound12], BANK,
    externalNotFormalised, externalInput, "Rosser–Schoenfeld; not in Mathlib; uninhabited"⟩,
  ⟨"finite bank M <= 4e9", [``Erdos287.PostQSigma.finiteExclusionUpTo_4e9], BANK, leanProved, bank,
    ""⟩,
  ⟨"Huang finite certificate (~502 digits)", [``Erdos287.PostV64V71.HuangFiniteExclusion287],
    BANK, externalNotFormalised, missingCertificate, "certificate absent; uninhabited"⟩,
  ⟨"terminal splices", [``Erdos287.PostV64V71.finite_and_tail_imply_erdos287,
     ``Erdos287.PostV64V71.erdos287_of_determinant_supply,
     ``Erdos287.PostV64V71.erdos287_of_determinant_supply_repository_native,
     ``Erdos287.PostV64V71.erdos287_of_analytic_route], STRICT_REDUCE, leanProvedConditional,
    bank, "repository-native version exposes the range (4e9, 2^1500) as a hypothesis"⟩,
  -- historical owners
  ⟨"SC287", [``Erdos287.PostQSigma.SC287.prime_moduleA_false], RETIRED, leanProved, historical,
    "RETIRED / REFUTED"⟩,
  ⟨"PG287", [``Erdos287.PostQSigma.PG287], RETIRED, open_, historical,
    "HISTORICAL OPEN proposition, SUPERSEDED AS CURRENT OWNER (not refuted)"⟩,
  ⟨"PZ", [], RETIRED, paperLevel, historical, "RETIRED / NONCONTROLLING"⟩,
  ⟨"RNLCM", [], RETIRED, paperLevel, historical, "SUPERSEDED"⟩,
  ⟨"RP-RNLCM (upper-half rough-prime theorem)", [], RETIRED, paperLevel, historical, "SUPERSEDED"⟩,
  ⟨"V70 exception-quantified LDBS", [], RETIRED, paperLevel, historical,
    "SUPERSEDED BY V71 WEIGHTED SUPPLY (exception quantifier removed by exception_weight_loss)"⟩
]

/-- Current OPEN entries. -/
def openObjects : List String :=
  (ledger.filter (fun e => decide (e.math = MathStatus.OPEN))).map Entry.object

/-- Research open entries (excluding the original problem). -/
def researchOpenEntries : List String :=
  (ledger.filter (fun e => decide (e.math = MathStatus.OPEN ∧ e.role ≠ Role.original))).map
    Entry.object

/-- Formally uninhabited external / paper / missing-certificate entries. -/
def formalUninhabitedExternalEntries : List String :=
  (ledger.filter (fun e => decide ((e.formal = FormalStatus.externalNotFormalised ∨
      e.formal = FormalStatus.paperLevel) ∧
      (e.role = Role.externalInput ∨ e.role = Role.missingCertificate)))).map Entry.object

/-- **Current open entries** (honest frontier). -/
theorem current_open_entries : openObjects =
    ["original Erdős #287", "effective major-arc lower bound with onset <= 2^1500",
     "SignedMinorArcLowerBound287", "DeterminantSupply287"] := by
  decide

theorem research_open_entries : researchOpenEntries =
    ["effective major-arc lower bound with onset <= 2^1500", "SignedMinorArcLowerBound287",
     "DeterminantSupply287"] := by
  decide

/-- External / paper inputs and missing certificates that are **not** inhabited in Lean. -/
theorem formal_uninhabited_external_entries : formalUninhabitedExternalEntries =
    ["D2 log bound 0.872 M / log M", "average singular series",
     "Siegel–Walfisz for logarithmic moduli", "eventual major-arc asymptotic",
     "explicit Chebyshev bound psi(n) <= 1.2 n", "Huang finite certificate (~502 digits)"] := by
  decide

/-- The sole current research owner. -/
theorem current_research_owner :
    (ledger.filter (fun e => decide (e.role = Role.researchOwner))).map Entry.object =
      ["DeterminantSupply287"] := by
  decide

/-- Nothing is CLOSED. -/
theorem nothing_closed : ledger.filter (fun e => decide (e.math = MathStatus.CLOSED)) = [] := by
  decide

end Erdos287.PostV64V71.CurrentLedger
