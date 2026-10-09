# Erdős #287 — Research Bank V25 report: fixed-modulus localization repair

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős Problem #287 remains OPEN.**  Nothing in this bank is
a proof of #287; no explicit `M₀` is produced and no finite splice is performed.

Mode: APPEND-ONLY / POST-ASTRA / SOURCE-LITERAL / PROVIDER-MINIMIZATION / NO EFFECTIVITY YET.
Research Banks V2–V24, every historical report and `ARISTOTLE_SUMMARY.md` are untouched
(verified by `git diff --name-status a08308e HEAD`, see §Git audit).

Status classes used (only): LEAN BANK, LEAN CONDITIONAL, EXTERNAL PROVIDER, FINITE REGRESSION,
REPAIRED / RETIRED, OPEN (Lean: `ResearchBankV25.Ledger.StatusClass`).

Principal update realised here: the fixed exceptional modulus is repaired by an EXACT centering
identity whose correction term carries an algebraically generated `1/φ(q)`, an exact conditioned
residue-energy contraction (arbitrary complex masses, overlapping moduli), the coprime
localized-energy reindexing, good-modulus affine clearing, and the two historical counterfixtures.

## Files and contents

### `RequestProject/Erdos287/ResearchBankV25/FixedModulusCentering.lean`

For a modulus `q`, a residue `a` and an integer `v` put

    δ(q, a, v) = 1_{v ≡ a (mod q)} − 1_{gcd(v, q) = 1} / φ(q).

**LEAN BANK.**

* `full_centering_fixed_modulus_exact` — for coprime `f, q` and any `r` with `r ≡ c (mod f)`,
  `r ≡ a (mod q)` (i.e. `r = CRT(c, a)`), and for EVERY integer `v` (units and non-units alike):

      δ(fq, r, v) = 1_{v ≡ c (f)} δ(q, a, v) + [1_{gcd(v,q)=1}/φ(q)] δ(f, c, v).

  The unit hypotheses `c ∈ (ℤ/f)^×`, `a ∈ (ℤ/q)^×` of the Astra statement are NOT needed: the
  identity is purely a CRT / totient-multiplicativity identity, so it is proved without them.
* `centered_sum_split` — the summed form for an arbitrary finitely supported complex coefficient:
  the full-modulus discrepancy splits into the localized discrepancy plus the correction whose
  reciprocal weight `1/φ(q)` is produced by the identity itself.
* `correction_term_needed` (regression) — deleting the correction term is FALSE.

Theorems (6): `indMod_mul`, `indCop_mul`, `indMod_congr`, `full_centering_fixed_modulus_exact`, `correction_term_needed`, `centered_sum_split`

Definitions / structures: `def indMod`, `def indCop`, `def delta`, `def CorrectionDeletable`

### `RequestProject/Erdos287/ResearchBankV25/FixedResidueEnergy.lean`

All statements allow ARBITRARY complex residue masses `z_r`.  `‖w‖²` is written
`Complex.normSq w`.

**LEAN BANK.**

* `fibre_pythagoras` — abstract projection identity.  For a finite set of residues `R`, a
  fibre map `π : R → U` all of whose fibres have the same cardinality `k`, arbitrary masses `z`
  and an arbitrary centre `c` (e.g. the full average), with `D_r = z_r − c` and conditioned
  discrepancy `E_r = z_r − (1/k) Σ_{π s = π r} z_s`:

      Σ_r |E_r|² = Σ_r |D_r|² − (1/k) Σ_u |Σ_{π r = u} D_r|².

* `conditioned_energy_le` — hence conditioned energy ≤ full-modulus energy.
* `overlap_fibre_card` / `overlap_pythagoras` — the general overlapping-modulus instance: `R` is
  `(ℤ/m)^×` with `m` any multiple of `f` (e.g. `m = lcm(f,q)`), `π` the reduction to `(ℤ/f)^×`;
  every fibre (the compatible fibre `A_u`) has the same size `k` with `k · φ(f) = φ(m)`.
* `product_pythagoras` / `coprime_conditioned_energy_le` — the coprime instance on
  `(ℤ/f)^× × (ℤ/q)^×` (`g = 1`, `k = φ(q)`).
* `localized_discrepancy_eq` — for `α_u(n) = α(n) 1_{n ≡ u (f)}`, the literal localized
  discrepancy `Δ_{α_u}(q,a)` equals the conditioned discrepancy `E_{u,a}` of the residue masses
  `z(u,a) = Σ_{n ≡ u (f), n ≡ a (q)} α(n)`.
* `full_discrepancy_eq` — the literal full-modulus discrepancy `Δ_α(fq, r)` equals `D_{CRT(r)}`.
* **`localized_energy_le_full`** — `Σ_u Σ_a |Δ_{α_u}(q,a)|² ≤ Σ_r |Δ_α(fq,r)|²`.
* `divisor_reindexing` — `Σ_{q≤U} τ(q)^J S(q) ≤ Σ_{ℓ≤fU} τ(ℓ)^J T(ℓ)` whenever
  `S(q) ≤ T(fq)` and `T ≥ 0` (using `τ(q) ≤ τ(fq)`).

**Semantic firewall.**  `α_u` is NOT asserted to be globally Siegel–Walfisz anywhere; only the
full-modulus energy of `α` is ever consumed.  The final BDH saving for that energy is the
EXTERNAL PROVIDER `BDHEnergyProvider` of `LocalizationContract.lean`.

Theorems (18): `fibre_one`, `fibre_pythagoras`, `conditioned_energy_le`, `overlap_fibre_card`, `overlap_pythagoras`, `prod_fibre_card`, `prod_fibre_sum`, `product_pythagoras`, `coprime_conditioned_energy_le`, `sum_units_ite`, `sum_units_prod_ite`, `coprime_iff_isUnit`, `localized_discrepancy_eq`, `crtUnits_val`, `natCast_eq_iff`, `full_discrepancy_eq`, `localized_energy_le_full`, `divisor_reindexing`

Definitions / structures: `def zres`, `def alphaLoc`, `def Disc`, `def crtUnits`

### `RequestProject/Erdos287/ResearchBankV25/GoodModulusClearing.lean`

Variable typing.  The prime variable is `p = A_i t + 1`.  The fixed exceptional modulus stays on
the ORIGINAL prime variable `p` (equivalently on `m₀ = m / A_j`); rational affine denominators
are cleared only on moduli coprime to the relevant fixed slopes.  No modular inverse of `A_j`
modulo `f` is ever introduced: the only inverse used is `u⁻¹` for a unit `u ∈ (ℤ/f)^×`.

**LEAN BANK.**

* `clearing_identity_j` — with `T = A_j p`:  `T − (A_j − A_i) = A_i (A_j t + 1)`;
* `clearing_identity_k` — `A_k T − A_j (A_k − A_i) = A_i A_j (A_k t + 1)`;
* `physical_divisibility_j` — `s ∣ A_j t + 1 ⟹ s ∣ T − (A_j − A_i)`;
* `physical_divisibility_prod` — `D ∣ ∏_k (A_k t + 1) ⟹ D ∣ ∏_k [A_k T − A_j (A_k − A_i)]`;
* `clearing_iff_of_coprime` — on a GOOD modulus (`gcd(s, A_i) = 1`) the clearing is reversible;
* `betaLift` / `betaLift_lattice` / `betaLift_off_lattice` — the supported-lattice map
  `m = A_j m₀`, `β'_u(m) = 1_{A_j ∣ m} β(m/A_j) 1_{m/A_j ≡ c u⁻¹ (f)}`.

Theorems (8): `clearing_identity_j`, `clearing_identity_k`, `physical_divisibility_j`, `physical_divisibility_prod`, `clearing_iff_of_coprime`, `betaLift_lattice`, `betaLift_off_lattice`, `integer_map_on_lattice`

Definitions / structures: `def betaLift`

### `RequestProject/Erdos287/ResearchBankV25/ExceptionalStateLocalization.lean`

The fixed exceptional modulus `f` stays on the original variable.  The localized pieces are
`α_u(n) = α(n) 1_{n ≡ u (f)}`, `u ∈ (ℤ/f)^×`.

**LEAN BANK.**

* `alphaLoc_partition` — `Σ_{u ∈ G_f} α_u(n) = 1_{(n,f)=1} α(n)`: the localized pieces partition
  the `f`-unit part of `α` exactly;
* `indMod_natCast` / `indCop_natCast` — the integer indicators of §3.1 agree with the `ZMod`
  indicators used in §3.3;
* `sum_delta_eq_Disc` — `Σ_n γ(n) δ(q, a, n) = Δ_γ(q, a)`;
* `sum_localized_delta_eq_Disc` — for `c ≡ u (f)` with `u` a unit,
  `Σ_n γ(n) 1_{n ≡ c (f)} δ(q, a, n) = Δ_{γ_u}(q, a)`.  This is the bridge from the centering
  identity to the conditioned residue energy.

**Firewall.**  No statement here asserts that `α_u` is globally Siegel–Walfisz.

Theorems (5): `alphaLoc_partition`, `indMod_natCast`, `indCop_natCast`, `sum_delta_eq_Disc`, `sum_localized_delta_eq_Disc`

### `RequestProject/Erdos287/ResearchBankV25/CorrectionAggregation.lean`

Summing the exact centering identity of §3.1 against moduli weights `κ_q` and a source
coefficient `γ` (for a bilinear source `γ = β ⋆ α`) gives EXACTLY

    Full = Loc + C_f,
    C_f  = Σ_q κ_q / φ(q) · Σ_n γ(n) 1_{gcd(n,q)=1} δ(f, c, n).

**LEAN BANK.**

* `full_eq_loc_add_corr` — the exact split.  The reciprocal modulus weight `1/φ(q)` in `C_f` is
  ALGEBRAICALLY GENERATED by the centering identity; it is not borrowed from a principal density.

**EXTERNAL PROVIDER.**

* `MaskedSWProvider` — the masked Siegel–Walfisz saving for the masked inner sums
  `S_q = Σ_n γ(n) 1_{(n,q)=1} δ(f,c,n)`, weighted by `τ(q)^J / φ(q)`.  Its contract fixes the
  divisor exponent `C_α` of the source coefficient BEFORE the requested saving `A` is chosen
  (`Calpha` is a structure field, `saving` quantifies `∀ A` afterwards), so `C_α` is independent
  of `A`.

**LEAN CONDITIONAL.**

* `correction_aggregation_conditional` — for every `|κ_q| ≤ τ(q)^J`:
  `|C_f| ≤ C_A · M N · log^{-A} x` eventually, for every `A`.

Theorems (2): `full_eq_loc_add_corr`, `correction_aggregation_conditional`

Definitions / structures: `def FullSum`, `def LocSum`, `def maskedInner`, `def CorrSum`, `structure MaskedSWProvider`

### `RequestProject/Erdos287/ResearchBankV25/LocalizationContract.lean`

**LEAN BANK.**

* `locE`, `fullE` — localized energy `Σ_{u,a} |Δ_{α_u}(q,a)|²` and full energy
  `Σ_r |Δ_α(ℓ,r)|²` (zero at modulus `0`);
* `locE_le_fullE` — `locE(q) ≤ fullE(fq)` for `(f,q) = 1` (from §3.3);
* `weighted_localized_le_full` — the divisor-weighted reindexing
  `Σ_{q∈Qs} τ(q)^J locE(q) ≤ Σ_{ℓ≤fU} τ(ℓ)^J fullE(ℓ)`;
* **`loc_bound`** — `|Loc| ≤ √(Σ_{q∈Qs} τ(q)^J) · √(Σ_{ℓ≤fU} τ(ℓ)^J fullE(ℓ))` (centering bridge +
  single-residue ≤ energy + Cauchy–Schwarz + energy contraction + reindexing).

**EXTERNAL PROVIDER.**

* `BDHEnergyProvider` — the Barban–Davenport–Halberstam-type saving for the FULL-modulus energy
  of the ACTUAL source `γ` (never for `γ_u`).

**LEAN CONDITIONAL.**

* **`zero_frequency_localized_bound`** — `Full = Loc + C_f` with `Loc` bounded through the BDH
  provider and `C_f` through the masked SW provider:  for every `A`, eventually
  `|Full| ≤ √(Σ τ^J) √(C₁ B/log^A x) + C₂ M N/log^A x`.

**Firewall.**  `γ_u` is never assumed globally Siegel–Walfisz; only the full-modulus energy of `γ`
enters the provider.

Theorems (9): `fullE_nonneg`, `locE_nonneg`, `locE_le_fullE`, `single_le_locE`, `tauJ_nonneg`, `weighted_localized_le_full`, `weighted_cauchy`, `loc_bound`, `zero_frequency_localized_bound`

Definitions / structures: `def locE`, `def fullE`, `def tauJ`, `structure BDHEnergyProvider`, `structure ZeroFreqData`

### `RequestProject/Erdos287/ResearchBankV25/Counterfixtures.lean`

**A. Residue restriction does not preserve a global SW statement.**  The constant sequence
`α ≡ 1` on `[1, 6]` is exactly balanced modulo `3` (`Δ_α(3, a) = 0` for every residue class),
but its restriction `α_1 = α · 1_{n ≡ 1 (3)}` to ONE fixed residue class has
`Δ_{α_1}(3, 1) = 2 − 2/2 = 1 ≠ 0`.  (`const_sequence_balanced`,
`restricted_sequence_unbalanced`, `residue_restriction_breaks_SW`.)

**B. A fixed slope can destroy unit status on a bad fixed modulus.**  With `A_i = 2`, `A_j = 3`,
`t = 8`: the prime variable `p = A_i t + 1 = 17` is a unit mod `3`, but `A_j p = 51` is NOT a
unit mod `3`; the good slope `A_i` keeps unit status (`2·17 = 34 ≡ 1`).  (`slope_destroys_unit`.)

Both historical inferences are classified **REPAIRED / RETIRED** (see `Ledger.lean`).

Theorems (8): `totient_three`, `count_residue`, `count_coprime`, `count_restricted`, `const_sequence_balanced`, `restricted_sequence_unbalanced`, `residue_restriction_breaks_SW`, `slope_destroys_unit`

Definitions / structures: `def Balanced`

### `RequestProject/Erdos287/ResearchBankV25/Ledger.lean`

The six admissible status classes (§2 of the V25–V28 request) are the constructors of
`StatusClass`; no other status word is used.  `v25_final_status` checks the classification by
`decide`, and `v25_bank_certificate` ties the LEAN BANK rows to the actual kernel theorems.

Theorems (2): `v25_final_status`, `v25_bank_certificate`

Definitions / structures: `inductive StatusClass`, `inductive V25Item`, `def status`

### `RequestProject/Erdos287/ResearchBankV25/AxiomAudit.lean`

`#print axioms` for every theorem of the bank (58 theorems).

Aggregator: `RequestProject/Erdos287/ResearchBankV25.lean` (imports every file above).

## Notes, deviations and honest caveats

* Files use ordinary (non-`module`) Lean headers, exactly like the frozen banks V2–V24, so that they
  import the frozen banks unchanged.
* `full_centering_fixed_modulus_exact` holds for all integers `v` WITHOUT the unit hypotheses on
  `c`, `a`; the hypotheses are therefore not assumed (a strictly stronger statement).
* The analytic savings (masked SW, BDH) remain EXTERNAL PROVIDERS (`MaskedSWProvider`,
  `BDHEnergyProvider`); `α_u` is never declared globally Siegel–Walfisz.

## Trust / validation

* Build commands (all succeed):
  * `lake build RequestProject.Erdos287.ResearchBankV25` — includes `RequestProject.Erdos287.ResearchBankV25.AxiomAudit`;
  * full project `lake build` — `Build completed successfully (8883 jobs)`; no warnings reported in any V25–V28 file.
* `#print axioms` on all 58 theorems of the bank (`AxiomAudit.lean`): every theorem depends
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
  `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV25` — result: exit code 0, no errors reported (wall time 47m21s; `--fresh` re-checks the module together with all of its imports, including Mathlib and the frozen banks).
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

* `RequestProject/Erdos287/ResearchBankV25.lean`
* `RequestProject/Erdos287/ResearchBankV25/FixedModulusCentering.lean`
* `RequestProject/Erdos287/ResearchBankV25/FixedResidueEnergy.lean`
* `RequestProject/Erdos287/ResearchBankV25/GoodModulusClearing.lean`
* `RequestProject/Erdos287/ResearchBankV25/ExceptionalStateLocalization.lean`
* `RequestProject/Erdos287/ResearchBankV25/CorrectionAggregation.lean`
* `RequestProject/Erdos287/ResearchBankV25/LocalizationContract.lean`
* `RequestProject/Erdos287/ResearchBankV25/Counterfixtures.lean`
* `RequestProject/Erdos287/ResearchBankV25/Ledger.lean`
* `RequestProject/Erdos287/ResearchBankV25/AxiomAudit.lean`
* `ERDOS287_RESEARCH_BANK_V25_REPORT.md`
