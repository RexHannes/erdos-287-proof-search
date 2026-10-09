# Erdős #287 — Research Bank V28 report: exact parameters, minimal analytic bundle, end-to-end composition, pre-effectivity theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős Problem #287 remains OPEN.**  Nothing in this bank is
a proof of #287; no explicit `M₀` is produced and no finite splice is performed.

Mode: APPEND-ONLY / POST-ASTRA / SOURCE-LITERAL / PROVIDER-MINIMIZATION / NO EFFECTIVITY YET.
Research Banks V2–V24, every historical report and `ARISTOTLE_SUMMARY.md` are untouched
(verified by `git diff --name-status a08308e HEAD`, see §Git audit).

Status classes used (only): LEAN BANK, LEAN CONDITIONAL, EXTERNAL PROVIDER, FINITE REGRESSION,
REPAIRED / RETIRED, OPEN (Lean: `ResearchBankV25.Ledger.StatusClass`).

Exact parameters, the minimal analytic bundle `FinalAnalyticProviders`, the end-to-end pair
composition `routeC_pair_baseline_after_full_repair` and the strongest permitted theorem
`pre_effectivity_asymptotic_287_after_full_repair` (LEAN CONDITIONAL, `∃ M₀`, no explicit `M₀`, no
finite splice).  The V24 `SourceClassDistributionProvider` is DERIVED (`derived_source_class_provider`)
rather than assumed.

## Files and contents

### `RequestProject/Erdos287/ResearchBankV28/ExactParameterInstantiation.lean`

All values are exact rationals / naturals; no floating point.  The parameters are REUSED from the
frozen banks (no redefinition):

* `K = 2^41252000`, `P = 12K`, `a = 28593810`, `δ = 1/40000` — `ResearchBankV17.ThinParameters`;
* `ϑ = 273/500`, `ρ = 1/1000000`, `ϑ₀ = 545999/1000000` — `ResearchBankV22.PositiveSieveParameters`;
* `A_C = 1000273/273000` — `ResearchBankV16.RouteCParameters`;
* `η = 1/1100`, `σ = 1/19000` — `ResearchBankV27.GlobalConductorSum`.

The audited functional bounds `μ_F > 7147687/10000`, `W_F < 98278402/10000` are CERTIFIED INPUTS
(the frozen `ThinFunctionalCertificate` shape); they are not computed here.

**LEAN BANK.**
* `parameter_values` — the literal values above;
* `principal_slack_reused` — `A_C − 2/ϑ₀ − 1/5000 = 147807727/186322158750 > 0` (V23, reused);
* `norm_transfer_witness_pos` — `8746001/25000000 > 0` (supplied witness value; its derivation
  formula is not part of the frozen banks and is recorded as supplied);
* `thin_margin_check_final` — the frozen exact check `ThinMarginCheck μ_lo W_hi (−423/5)`;
  `90 − 423/5 = 27/5`;
* `score_margin_exact` — `μ_lo − (A_C W_hi + 27/5)/99 − 350 − 1/20 = 11479502057/12285000000 > 0`
  (the `1/20` is the reserved slack of the score ledger);
* `clean_savings` — `347/418000 > 0` and `347/836000 > 0` (V27, reused).

Theorems (7): `parameter_values`, `principal_slack_reused`, `norm_transfer_witness_pos`, `baseline_constant`, `thin_margin_check_final`, `score_margin_exact`, `clean_savings`

Definitions / structures: `def muLo`, `def WHi`, `def errFinal`, `def normTransferWitness`

### `RequestProject/Erdos287/ResearchBankV28/RepairedAnalyticBundle.lean`

`FinalAnalyticProviders` collects ONLY genuinely unformalized analytic inputs (EXTERNAL
PROVIDER interfaces; the bundle is never constructed):

* `rosser`, `tuple` — Rosser scalar asymptotic and prime-harmonic tuple input (V22);
* `euler` — principal Euler/Mellin provider (V23; carries the frozen S0 normalization);
* `hat` — tensor/hat reference approximation (V23);
* `di` — the ONE minimal `DISpectralProvider` (V27) at `η = 1/1100` for the class `DIClass`
  of public DI forms (the realized forms must lie in `DIClass`);
* `zeroFreq` — the masked-SW / BDH zero-frequency branch class bound;
* `oneLarge`, `twoLarge` — the one-large / two-large HB branch class bounds;
* `boundary` — the product-boundary branch class bound (V26 union-of-boundary estimate);
* `nonzero` — for every family weight, a clean realization of the nonzero-frequency branch: clean
  states at scale `x = M` together with their per-instance `RepresentationMomentProvider`,
  `DivisorSumProvider` and the named `NonzeroPruningContract` (V27);
* `tensor` — the same-weight actual-measure decomposition `BranchedActualMeasureProvider`
  (tensor approximation / actual measure, still external);
* `s1` — the S1 contract; `cert` — the certified functional bounds `μ_F > μ_lo`, `W_F < W_hi`.

It does NOT contain fixed-modulus centering, residue-energy projection, HB algebra, cell
colouring, positive-sieve finite algebra, finite-label colour grouping, CRT orbit counting or
parameter arithmetic: those are kernel theorems (V21–V27).  Nor does it contain the retired
monolithic source-class provider: the V24 `SourceClassDistributionProvider` is DERIVED here
(`derived_source_class_provider`) from the four branch class bounds.

**LEAN BANK / LEAN CONDITIONAL.**
* `derived_source_class_provider` — the four branch class bounds give the V24
  `SourceClassDistributionProvider` for the summed branch functional;
* `nonzero_branch_small` — from the V27 derived clean-nonzero theorem:
  eventually `[DE_nz(Λ)]_+ ≤ ε`.

Theorems (2): `derived_source_class_provider`, `nonzero_branch_small`

Definitions / structures: `structure BranchClassBound`, `def sumDE`, `def NonzeroCleanRealization`, `structure BranchedActualMeasureProvider`, `structure FinalAnalyticProviders`

### `RequestProject/Erdos287/ResearchBankV28/FinalPairComposition.lean`

**This is NOT a proved pair theorem: it is LEAN CONDITIONAL on `FinalAnalyticProviders`.**

The composition uses, for ONE and the SAME completed weight `Λ = LamFam S τ M` (V24):
1. the completed positive sieve and its coefficient contract (`lamFam_source_decomposition`,
   V24 LEAN BANK);
2./3. the zero-frequency (masked SW / BDH, V25 localization), one-large, two-large and
   product-boundary (V26) branch class bounds, combined through the DERIVED source-class provider;
4. the V27 DERIVED clean-nonzero theorem (`nonzero_branch_small`);
5./6. the zero-frequency and one-large / two-large branches (inside `sumDE`);
7. the V23 same-weight principal budget `principal_budget_le_A_C`;
8. the actual tensor approximation (`hat_approximation_eventually_small`).
No auxiliary weight changes between error and principal; the normalization `N` is the frozen one.

* **`routeC_pair_baseline_after_full_repair`** — the frozen V16 `RouteCBaselineProvider`:
  eventually `Pair/N ≤ A_C W_F + 90 + err + η`.
* `bx_norm_bound` — the non-off-principal part `‖B_x‖²_ν := M_new + |DE_src| + [DE_nz]_+ +
  C_t √|E_AB|` is eventually `≤ A_C W_F + η` (i.e. `A_C W_F + o(1)`).
* `pair_ratio_final` — at `err = −423/5`: eventually `P_actual/N ≤ A_C W_F + 27/5 + η`.

Theorems (3): `bx_norm_bound`, `routeC_pair_baseline_after_full_repair`, `pair_ratio_final`

Definitions / structures: `def BxSq`

### `RequestProject/Erdos287/ResearchBankV28/PreEffectivityTheorem.lean`

* **`pre_effectivity_asymptotic_287_after_full_repair`** (LEAN CONDITIONAL on
  `FinalAnalyticProviders` only, plus the structural sieve geometry / rounding data):

      FinalAnalyticProviders  ⟹  ∃ M₀, ∀ M ≥ M₀, no counterexample has maximum denominator M.

  It reuses the frozen S0 (from the principal provider's normalization field), S1, graph, score,
  compiler, contact, row rigidity and harmonic contradiction chain through
  `ResearchBankV20.ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline`, with the
  exact final margin check `thin_margin_check_final` at `err = −423/5`.

This theorem is NOT the global Erdős #287: `M₀` is only asserted to exist (it may depend on
ineffective analytic constants), no explicit `M₀` is produced, and the finite splice is not
performed.

Theorems (1): `pre_effectivity_asymptotic_287_after_full_repair`

### `RequestProject/Erdos287/ResearchBankV28/EffectivityFirewall.lean`

## §14 Effectivity ledger (OPEN items, recorded as data)

`EffectivityItem` lists `noExplicitM0Yet`, `finiteSpliceOpen`, `exceptionalZeroEffectivityOpen`;
every item has status `OPEN` (`effectivity_all_open`).  The pre-effectivity theorem is an
`∃ M₀` statement that may rest on ineffective analytic constants; it is never converted into a
computable `M₀`.

## §15 Historical overclaim firewalls (FINITE REGRESSION / LEAN BANK)

1. `fw1_small_cost_not_SW` — a fixed-modulus discrepancy of size `1` (small cost) coexists with
   failure of the balance (SW-type) statement;
2. `fw2_residue_restriction_not_SW` — residue restriction does not preserve global balance;
3. `fw3_raw_density_ne_weighted` — raw density `≠` conditioned weighted density;
4. `fw4_support_not_coefficient_factorization` — product support does not force a product
   coefficient;
5. `fw5_no_kloosterman_decoration` — a decoration depending on a final Kloosterman variable is not
   an inner decoration;
6. `fw6_labels_cost_sqrt` — separate labels cost `√L` (not `L`) on the linear sum via the common
   Cauchy; `√2 < 2`;
7. `fw7_character_free_not_DI` — the character-free colour route does not prove DI: the DI
   conclusion fails for some admissible form;
8. `fw8_finite_verifier_not_spectral` — no finite check yields the spectral provider: the
   unrestricted provider is false although it holds vacuously on the empty list;
9. `fw9_asymptotic_not_explicit` — `∃ M₀` does not give an explicit `M₀`;
10. `fw10_explicit_needs_splice` — even an explicit `M₀` needs the finite splice for global #287.

Theorems (14): `effectivity_all_open`, `noExplicitM0Yet_holds`, `finiteSpliceOpen_holds`, `exceptionalZeroEffectivityOpen_recorded`, `fw1_small_cost_not_SW`, `fw2_residue_restriction_not_SW`, `fw3_raw_density_ne_weighted`, `fw4_support_not_coefficient_factorization`, `fw5_no_kloosterman_decoration`, `fw6_labels_cost_sqrt`, `fw7_character_free_not_DI`, `fw8_finite_verifier_not_spectral`, `fw9_asymptotic_not_explicit`, `fw10_explicit_needs_splice`

Definitions / structures: `inductive EffectivityItem`, `def effectivityStatus`, `def NoExplicitM0Yet`, `def FiniteSpliceOpen`, `def ExceptionalZeroEffectivityOpen`

### `RequestProject/Erdos287/ResearchBankV28/FinalStatus.lean`

Status classes are those of `ResearchBankV25.Ledger.StatusClass`
(LEAN BANK / LEAN CONDITIONAL / EXTERNAL PROVIDER / FINITE REGRESSION / REPAIRED-RETIRED / OPEN).
V21–V24 are FROZEN (recorded as the inherited LEAN CONDITIONAL / LEAN BANK chain; not modified).

Theorems (2): `final_status`, `open_rows`

Definitions / structures: `inductive FinalItem`, `def status`

### `RequestProject/Erdos287/ResearchBankV28/AxiomAudit.lean`

`#print axioms` for every theorem of the bank (29 theorems).

Aggregator: `RequestProject/Erdos287/ResearchBankV28.lean` (imports every file above).

## Notes, deviations and honest caveats

* Files use ordinary (non-`module`) Lean headers, exactly like the frozen banks V2–V24, so that they
  import the frozen banks unchanged.
* `μ_F > 7147687/10000` and `W_F < 98278402/10000` do not occur as Lean constants in V2–V24; they are
  CERTIFIED INPUTS through the frozen `ThinFunctionalCertificate` field `cert`.
* The norm-transfer witness `8746001/25000000` is not derived in the frozen banks; it is recorded as
  the supplied constant and only its positivity is checked.
* The score margin is `μ_lo − (A_C W_hi + 27/5)/99 − 350 − 1/20 = 11479502057/12285000000`; this
  formula (frozen Route-C margin at `err = −423/5`, minus a reserved `1/20`) was reconstructed to match
  the supplied value exactly.  The unreserved frozen margin is `12093752057/12285000000`.
* The branch analytic inputs enter at CLASS-BOUND level (`BranchClassBound` for the zero-frequency /
  BDH, one-large, two-large and product-boundary branches).  The V25 / V26 exact identities are
  proved independently; their use inside the analytic derivation of those class bounds is recorded
  in the provider documentation, not as a Lean composition.
* The nonzero-frequency branch is controlled by the V27 THEOREM `clean_nonzero_derived`, applied to
  the clean realization of each family weight (`NonzeroCleanRealization`, containing the
  per-instance representation / divisor-sum providers and the pruning contract).
* `‖B_x‖²_ν` is represented by `BxSq` (the non-off-principal part of the same-weight decomposition).
* The structural sieve geometry `SieveGeometry` and rounding data `RoundedCellData` are explicit
  arguments (as in V24), not providers.

## Trust / validation

* Build commands (all succeed):
  * `lake build RequestProject.Erdos287.ResearchBankV28` — includes `RequestProject.Erdos287.ResearchBankV28.AxiomAudit`;
  * full project `lake build` — `Build completed successfully (8883 jobs)`; no warnings reported in any V25–V28 file.
* `#print axioms` on all 29 theorems of the bank (`AxiomAudit.lean`): every theorem depends
  only on a subset of `propext`, `Classical.choice`, `Quot.sound`.  Across V25–V28 (220 theorems):
  201 use all three, 9 use `propext, Quot.sound`, 2 use `propext` only, 8 use no axioms.
  No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.trustCompiler`, no custom axiom.
* Forbidden-token scan (`rg` for `sorry`, `admit`, `axiom` declarations, `native_decide`,
  `bv_decide`, `unsafe`, `implemented_by`, `opaque`, `skipKernelTC`, `trustCompiler`,
  `ofReduceBool`) over `RequestProject/Erdos287/ResearchBankV25*` … `V28*`: no occurrences (the only
  hits are the words "axiom audit" in the `AxiomAudit.lean` headers and the `#print axioms`
  commands).  Only ordinary kernel `decide` is used.
* External checker: the installed checker is `leanchecker` (bundled with the toolchain);
  `lean4checker` is NOT installed.  Command:
  `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV28` — result: exit code 0, no errors reported (wall time 50m12s; `--fresh` re-checks the module together with all of its imports, including Mathlib and the frozen banks).
* Comparator: not installed (`comparator` not found); no comparator run and no emulation.

## Git audit

* Base commit: `a08308e` (Initial commit of this run).
* `git diff --name-status a08308e HEAD`: 48 entries, ALL of status `A` (added); modified/deleted
  entries: none.
* Modified files: none.  V2–V24, every historical report and `ARISTOTLE_SUMMARY.md` are untouched.
* Full list of added paths (all four banks):

```
A	ERDOS287_RESEARCH_BANK_V25_REPORT.md
A	ERDOS287_RESEARCH_BANK_V26_REPORT.md
A	ERDOS287_RESEARCH_BANK_V27_REPORT.md
A	ERDOS287_RESEARCH_BANK_V28_REPORT.md
A	RequestProject/Erdos287/ResearchBankV25.lean
A	RequestProject/Erdos287/ResearchBankV25/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV25/CorrectionAggregation.lean
A	RequestProject/Erdos287/ResearchBankV25/Counterfixtures.lean
A	RequestProject/Erdos287/ResearchBankV25/ExceptionalStateLocalization.lean
A	RequestProject/Erdos287/ResearchBankV25/FixedModulusCentering.lean
A	RequestProject/Erdos287/ResearchBankV25/FixedResidueEnergy.lean
A	RequestProject/Erdos287/ResearchBankV25/GoodModulusClearing.lean
A	RequestProject/Erdos287/ResearchBankV25/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV25/LocalizationContract.lean
A	RequestProject/Erdos287/ResearchBankV26.lean
A	RequestProject/Erdos287/ResearchBankV26/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV26/BoundaryBudget.lean
A	RequestProject/Erdos287/ResearchBankV26/DyadicSourceMap.lean
A	RequestProject/Erdos287/ResearchBankV26/HBBranchCoverage.lean
A	RequestProject/Erdos287/ResearchBankV26/HeathBrownIdentity.lean
A	RequestProject/Erdos287/ResearchBankV26/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV26/ProductIntervalBoxes.lean
A	RequestProject/Erdos287/ResearchBankV26/RoughConvolution.lean
A	RequestProject/Erdos287/ResearchBankV26/RoughSWAdapter.lean
A	RequestProject/Erdos287/ResearchBankV26/SingletonBins.lean
A	RequestProject/Erdos287/ResearchBankV27.lean
A	RequestProject/Erdos287/ResearchBankV27/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV27/CRTColourOrbit.lean
A	RequestProject/Erdos287/ResearchBankV27/CleanNonzero.lean
A	RequestProject/Erdos287/ResearchBankV27/CommonCauchy.lean
A	RequestProject/Erdos287/ResearchBankV27/DISpectralProvider.lean
A	RequestProject/Erdos287/ResearchBankV27/DecoratedLemma.lean
A	RequestProject/Erdos287/ResearchBankV27/DecoratedMaynardSetup.lean
A	RequestProject/Erdos287/ResearchBankV27/FiniteLabelEnergy.lean
A	RequestProject/Erdos287/ResearchBankV27/GlobalConductorSum.lean
A	RequestProject/Erdos287/ResearchBankV27/GroupedCoefficient.lean
A	RequestProject/Erdos287/ResearchBankV27/Ledger.lean
A	RequestProject/Erdos287/ResearchBankV27/OuterInnerSeparation.lean
A	RequestProject/Erdos287/ResearchBankV27/RepresentationMoment.lean
A	RequestProject/Erdos287/ResearchBankV27/SmoothFrequencyRecovery.lean
A	RequestProject/Erdos287/ResearchBankV28.lean
A	RequestProject/Erdos287/ResearchBankV28/AxiomAudit.lean
A	RequestProject/Erdos287/ResearchBankV28/EffectivityFirewall.lean
A	RequestProject/Erdos287/ResearchBankV28/ExactParameterInstantiation.lean
A	RequestProject/Erdos287/ResearchBankV28/FinalPairComposition.lean
A	RequestProject/Erdos287/ResearchBankV28/FinalStatus.lean
A	RequestProject/Erdos287/ResearchBankV28/PreEffectivityTheorem.lean
A	RequestProject/Erdos287/ResearchBankV28/RepairedAnalyticBundle.lean
```

Files added by this bank:

* `RequestProject/Erdos287/ResearchBankV28.lean`
* `RequestProject/Erdos287/ResearchBankV28/ExactParameterInstantiation.lean`
* `RequestProject/Erdos287/ResearchBankV28/RepairedAnalyticBundle.lean`
* `RequestProject/Erdos287/ResearchBankV28/FinalPairComposition.lean`
* `RequestProject/Erdos287/ResearchBankV28/PreEffectivityTheorem.lean`
* `RequestProject/Erdos287/ResearchBankV28/EffectivityFirewall.lean`
* `RequestProject/Erdos287/ResearchBankV28/FinalStatus.lean`
* `RequestProject/Erdos287/ResearchBankV28/AxiomAudit.lean`
* `ERDOS287_RESEARCH_BANK_V28_REPORT.md`
