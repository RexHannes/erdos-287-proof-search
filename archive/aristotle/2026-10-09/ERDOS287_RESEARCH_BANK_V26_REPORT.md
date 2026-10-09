# Erdős #287 — Research Bank V26 report: actual Heath-Brown / rough source adapters

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős Problem #287 remains OPEN.**  Nothing in this bank is
a proof of #287; no explicit `M₀` is produced and no finite splice is performed.

Mode: APPEND-ONLY / POST-ASTRA / SOURCE-LITERAL / PROVIDER-MINIMIZATION / NO EFFECTIVITY YET.
Research Banks V2–V24, every historical report and `ARISTOTLE_SUMMARY.md` are untouched
(verified by `git diff --name-status a08308e HEAD`, see §Git audit).

Status classes used (only): LEAN BANK, LEAN CONDITIONAL, EXTERNAL PROVIDER, FINITE REGRESSION,
REPAIRED / RETIRED, OPEN (Lean: `ResearchBankV25.Ledger.StatusClass`).

Exact rough/Heath-Brown source identities and the source-level (not merely length-level) HB
branch coverage; the analytic tail and product-boundary estimates are explicit providers.

## Files and contents

### `RequestProject/Erdos287/ResearchBankV26/RoughConvolution.lean`

For `z ∈ ℕ` put

    R_z(n) = 1_{P⁻(n) ≥ z}   (every prime factor of n is ≥ z; R_z(1) = 1),
    H_z(d) = 1_{P⁺(d) < z}   (every prime factor of d is < z; H_z(1) = 1),

both zero at `0`.  `H_z` is the indicator of ALL `z`-smooth integers, prime powers included — it is
NOT silently replaced by its squarefree part.

**LEAN BANK.**

* `primeIndicator_isMultiplicative` — `n ↦ 1_{n ≠ 0 ∧ ∀ p ∣ n, P p}` is multiplicative;
* **`rough_mu_identity`** — `μ · R_z = μ ⋆ H_z` (as arithmetic functions);
* **`rough_one_identity`** — `R_z = 1 ⋆ (μ · H_z)`;
* `rough_mu_identity_apply`, `rough_one_identity_apply` — the pointwise divisor-sum forms
  `μ(n) R_z(n) = Σ_{d ∣ n} μ(d) H_z(n/d)` and `R_z(n) = Σ_{d ∣ n} μ(d) H_z(d)`.

Theorems (9): `primeIndicator_apply`, `primeIndicator_isMultiplicative`, `primeIndicator_prime_pow`, `sum_antidiag_prime_pow`, `moebius_prime_pow'`, `rough_mu_identity`, `rough_one_identity`, `rough_mu_identity_apply`, `rough_one_identity_apply`

Definitions / structures: `def primeIndicator`, `def R`, `def H`

### `RequestProject/Erdos287/ResearchBankV26/HeathBrownIdentity.lean`

Let `M_y(n) = μ(n) 1_{n ≤ y}` (real-valued arithmetic function).  All convolutions are Dirichlet
convolutions in the commutative ring `ArithmeticFunction ℝ`.

**LEAN BANK.**

* `hb_ring_identity` — for every `k`, the exact ring identity
  `Λ = (1 − 1⋆M_y)^k ⋆ Λ + Σ_{j<k} (−1)^j C(k, j+1) · (M_y^{⋆(j+1)} ⋆ 1^{⋆j} ⋆ log)`
  (binomial theorem + `Λ ⋆ 1 = log`);
* `one_sub_zeta_My` — `1 − 1⋆M_y = 1⋆(μ − M_y)`, a function supported on `n > y`;
* `pow_supported` — `(1⋆(μ − M_y))^{⋆k}` is supported on `n > y^k` (`k ≥ 1`, `y ≥ 0`);
* **`heath_brown_identity`** — for `n ≤ y^k` (`k ≥ 1`, `y ≥ 0`):

      Λ(n) = Σ_{j=1}^{k} (−1)^{j−1} C(k, j) (M_y^{⋆j} ⋆ 1^{⋆(j−1)} ⋆ log)(n)

  (written with `j ↦ j+1`, `j < k`);
* `heath_brown_k3` — the instance `k = 3`;
* `hb_k3_at_most_six_variables` — every `k = 3` term has `j + (j−1) + 1 ≤ 6` convolution
  factors; missing factors are the singleton sequence `{1}` (see `SingletonBins.lean`).

No requirement that any rough bin contain a value `> x^ν` is made.

Theorems (12): `My_apply`, `Mb_apply_ne_zero`, `one_sub_zeta_My`, `supportedAbove_mul`, `zeta_Mb_supported`, `pow_supported`, `vanish_of_supported`, `dlt_mul_apply`, `hb_ring_identity`, `heath_brown_identity`, `heath_brown_k3`, `hb_k3_at_most_six_variables`

Definitions / structures: `def My`, `def Mb`, `def SupportedAbove`, `def dlt`, `def hbTerm`, `def hbCoeff`, `def evalAt`

### `RequestProject/Erdos287/ResearchBankV26/RoughSWAdapter.lean`

## §4.2  Truncated smooth-divisor tail

`R_z(n) = Σ_{d ∣ n} μ(d) H_z(d)` (V26 §4.1).  Truncating at `d ≤ y` leaves the error
`E_y(n) = Σ_{d ∣ n, d > y} μ(d) H_z(d)`.

**LEAN BANK.**
* `rough_truncation_split` — `R_z(n) = Σ_{d∣n, d≤y} μ(d)H_z(d) + E_y(n)` exactly;
* `truncation_error_le` — `Σ_{n ≤ N} |E_y(n)| ≤ N · Σ_{y < d ≤ N} H_z(d)/d`.  The count of
  multiples is `⌊N/d⌋ ≤ N/d`; NO extra `+1` per divisor is inserted.

**EXTERNAL PROVIDER.**
* `SmoothTailProvider` — the Rankin-type reciprocal tail
  `Σ_{d > y, P⁺(d) < z} 1/d ≤ exp(−(log log x)²) log^C x`.

**LEAN CONDITIONAL.**
* `truncation_error_conditional` — the absolute source error is at most
  `N · exp(−(log log x)²) log^C x`.

## §4.4  Source sequence types

`RoughMuSequence`, `RoughOneSequence`, `RoughLogSequence`, `ComplementaryDivisorBoundedSequence`
are concrete coefficient sequences.  One-boundedness (`OneBounded`), rough support
(`RoughSupported`), an SW property and an `L²` divisor bound are SEPARATE predicates.

**Firewall (LEAN BANK).**  `rough_does_not_imply_SW`: a one-bounded, rough-supported sequence
(the indicator of `{1}`) is NOT balanced modulo `3`; so no implication `rough ⟹ SW` exists.

Theorems (11): `rough_truncation_split`, `H_nonneg_le_one`, `truncation_error_le`, `truncation_error_conditional`, `R_values`, `roughMu_oneBounded`, `roughMu_roughSupported`, `roughOne_oneBounded`, `roughOne_roughSupported`, `roughLog_roughSupported`, `rough_does_not_imply_SW`

Definitions / structures: `def truncErr`, `structure SmoothTailProvider`, `def OneBounded`, `def RoughSupported`, `def L2DivisorBound`, `def RoughMuSequence`, `def RoughOneSequence`, `def RoughLogSequence`, `structure ComplementaryDivisorBoundedSequence`, `def deltaOne`

### `RequestProject/Erdos287/ResearchBankV26/ProductIntervalBoxes.lean`

Dyadicization alone does NOT remove the product constraint `x < m₁⋯m_k ≤ 2x`.  We use
multiplicative boxes of ratio `1 + h` (`h = log^{-B} x`):
`B = ∏_i [L_i, L_i(1+h))`.  A box is INTERIOR if `x < ∏ L_i` and `∏ L_i (1+h)^k ≤ 2x`,
EXTERIOR if `∏ L_i (1+h)^k ≤ x` or `2x < ∏ L_i`, and BOUNDARY otherwise.

**LEAN BANK.**
* `interior_rectangular` — on an interior box the product cutoff is identically `1`, so the
  constraint is RECTANGULAR there;
* `exterior_zero` — on an exterior box it is identically `0`;
* `box_decomposition` — exact decomposition of the cut sum into interior rectangular sums plus
  ONE sum over the UNION of boundary boxes.

**EXTERNAL PROVIDER.**
* `ProductBoundaryProvider` — the analytic boundary estimate
  `O(x √h log^C x + x^{1/2} log^C x)` for the union of boundary products.

**LEAN CONDITIONAL.**
* `product_boxing_conditional` — the cut sum equals the interior rectangular sums up to the
  provider bound, applied ONCE (no factor `#boxes`).
* `boundary_bound_not_multiplied` (regression) — multiplying by the number of boxes would give a
  strictly larger bound as soon as there are two boundary boxes.

Theorems (6): `prod_bounds`, `interior_rectangular`, `exterior_zero`, `box_decomposition`, `product_boxing_conditional`, `boundary_bound_not_multiplied`

Definitions / structures: `structure MulBox`, `def MulBox.Mem`, `def productCut`, `def Interior`, `def Exterior`, `structure BoxingData`, `def BoxingData.cutSum`, `def BoxingData.interiorSum`, `def BoxingData.boundarySum`, `structure ProductBoundaryProvider`

### `RequestProject/Erdos287/ResearchBankV26/SingletonBins.lean`

A Heath-Brown term with fewer than six variables is padded with the singleton sequence `{1}`
(the Dirichlet unit `δ₁ = 1`), which changes nothing.  No rough bin is required to contain a
value `> x^ν`: the singleton bin contains only `1`.

**LEAN BANK.**
* `singleton_apply` — `δ₁(n) = 1_{n = 1}`;
* `pad_singleton` — `F ⋆ δ₁^{⋆m} = F` for every `m`;
* `hb_term_six_variables` — every `k = 3` HB term equals a product of EXACTLY six factors after
  padding with singleton sequences;
* `singleton_bin_values` — the singleton bin's only nonzero value is at `n = 1`, so no lower
  bound `> x^ν` on bin values is available or needed.

Theorems (4): `singleton_apply`, `pad_singleton`, `hb_term_six_variables`, `singleton_bin_values`

### `RequestProject/Erdos287/ResearchBankV26/DyadicSourceMap.lean`

**LEAN BANK.**
* `dyadic_mem` / `dyadic_unique` — every `n ≥ 1` lies in exactly one dyadic interval
  `[2^k, 2^{k+1})`, namely `k = ⌊log₂ n⌋`;
* `dyadic_partition_of_unity` — `Σ_{k<K} 1_{[2^k,2^{k+1})}(n) = 1` for `1 ≤ n < 2^K`;
* `dyadicBox` / `source_sum_by_boxes` — for any finite set of variable tuples and any source
  coefficient `F`, `Σ_m F(m) = Σ_{boxes b} Σ_{m ∈ box b} F(m)`: every source term is counted in
  exactly one dyadic box (source-level, not a length census).

Dyadicization alone does NOT remove the product constraint `x < m₁⋯m_k ≤ 2x`; that is the job of
the multiplicative boxes (`ProductIntervalBoxes.lean`).

Theorems (4): `dyadic_mem`, `dyadic_unique`, `dyadic_partition_of_unity`, `source_sum_by_boxes`

Definitions / structures: `def dyadicBox`

### `RequestProject/Erdos287/ResearchBankV26/HBBranchCoverage.lean`

Each HB term has at most six variables; a dyadic box assigns to each variable a length exponent
`e_i ≥ 0` with `Σ e_i = 1` (normalised by `log x`).

**LEAN BANK.**
* `greedy_subset_sum` — if every step is `≤ c` and the target window `[L, U]` has length
  `≥ c`, a sub-sum lands in the window;
* **`branch_trichotomy`** — for `0 < α ≤ 2/5`, every length vector is
  TYPE II (some sub-product has length in `[α, 1−α]`), ONE-LARGE (a single variable
  `> 1−α`) or TWO-LARGE (two variables with total `> 1−α`);
* `trichotomy_fails_beyond` (regression) — at `α = 12/25 > 2/5` five equal variables `1/5`
  are in none of the three classes, so the threshold matters;
* `BranchRecord` — the actual branch record (source coefficient, selected Type-II variables,
  complementary variables, roughness, one-bounded / `L²` status, length, dyadic box, provider);
* `classify` / `classify_spec` — every box receives a record whose provider condition HOLDS;
* **`source_level_coverage`** — every source term of the HB sum is counted exactly once, in
  exactly one branch:  `Σ_m F(m) = Σ_{kind} Σ_{boxes b of this kind} Σ_{m ∈ b} F(m)`.

Theorems (5): `greedy_subset_sum`, `branch_trichotomy`, `trichotomy_fails_beyond`, `classify_spec`, `source_level_coverage`

Definitions / structures: `def TypeII`, `def OneLarge`, `def TwoLarge`, `inductive BranchKind`, `inductive SourceKind`, `inductive SizeStatus`, `structure BranchRecord`, `def RecordValid`, `def classify`

### `RequestProject/Erdos287/ResearchBankV26/BoundaryBudget.lean`

With `L = log x` and `h = L^{-B}` the provider bound `x √h L^C + x^{1/2} L^C` is at most
`2 x L^{-A}` once `B ≥ 2(C + A)` and `L^{C+A} ≤ x^{1/2}`.

**LEAN BANK** (exact real-exponent arithmetic):
* `sqrt_rpow_neg` — `√(L^{-B}) = L^{-B/2}`;
* `boundary_first_term` — `x √(L^{-B}) L^C ≤ x L^{-A}` for `B ≥ 2(C+A)`, `L ≥ 1`;
* `boundary_second_term` — `x^{1/2} L^C ≤ x L^{-A}` when `L^{C+A} ≤ x^{1/2}`;
* `boundary_budget` — the sum is `≤ 2 x L^{-A}`.

Theorems (4): `sqrt_rpow_neg`, `boundary_first_term`, `boundary_second_term`, `boundary_budget`

### `RequestProject/Erdos287/ResearchBankV26/Ledger.lean`

Status classes are those of `ResearchBankV25.Ledger.StatusClass`.

Theorems (2): `v26_final_status`, `v26_bank_certificate`

Definitions / structures: `inductive V26Item`, `def status`

### `RequestProject/Erdos287/ResearchBankV26/AxiomAudit.lean`

`#print axioms` for every theorem of the bank (57 theorems).

Aggregator: `RequestProject/Erdos287/ResearchBankV26.lean` (imports every file above).

## Notes, deviations and honest caveats

* Files use ordinary (non-`module`) Lean headers, exactly like the frozen banks V2–V24, so that they
  import the frozen banks unchanged.
* The Rankin-type smooth-divisor tail and the product-boundary estimate are EXTERNAL PROVIDERS
  (`SmoothTailProvider`, `ProductBoundaryProvider`); the boundary is estimated once for the union of
  boundary products (no multiplication by the number of boxes).
* No implication `rough ⇒ SW` exists (`rough_does_not_imply_SW`).

## Trust / validation

* Build commands (all succeed):
  * `lake build RequestProject.Erdos287.ResearchBankV26` — includes `RequestProject.Erdos287.ResearchBankV26.AxiomAudit`;
  * full project `lake build` — `Build completed successfully (8883 jobs)`; no warnings reported in any V25–V28 file.
* `#print axioms` on all 57 theorems of the bank (`AxiomAudit.lean`): every theorem depends
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
  `lake env leanchecker --fresh RequestProject.Erdos287.ResearchBankV26` — result: exit code 0, no errors reported (wall time 47m02s; `--fresh` re-checks the module together with all of its imports, including Mathlib and the frozen banks).
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

* `RequestProject/Erdos287/ResearchBankV26.lean`
* `RequestProject/Erdos287/ResearchBankV26/RoughConvolution.lean`
* `RequestProject/Erdos287/ResearchBankV26/HeathBrownIdentity.lean`
* `RequestProject/Erdos287/ResearchBankV26/RoughSWAdapter.lean`
* `RequestProject/Erdos287/ResearchBankV26/ProductIntervalBoxes.lean`
* `RequestProject/Erdos287/ResearchBankV26/SingletonBins.lean`
* `RequestProject/Erdos287/ResearchBankV26/DyadicSourceMap.lean`
* `RequestProject/Erdos287/ResearchBankV26/HBBranchCoverage.lean`
* `RequestProject/Erdos287/ResearchBankV26/BoundaryBudget.lean`
* `RequestProject/Erdos287/ResearchBankV26/Ledger.lean`
* `RequestProject/Erdos287/ResearchBankV26/AxiomAudit.lean`
* `ERDOS287_RESEARCH_BANK_V26_REPORT.md`
