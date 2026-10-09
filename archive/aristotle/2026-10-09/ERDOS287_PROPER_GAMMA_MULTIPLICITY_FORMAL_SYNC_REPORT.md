# ERDŐS #287 — PROPER-γ MULTIPLICITY FORMAL SYNC REPORT

**Programme:** Erdős #287 effectivity only.
**Mode:** append-only formal sync; long-fibre bank preserved; proper-γ / q-fibre +
multiplicity geometry / shell-6 / current `N ≥ 7` frontier.

**Erdős #287 is NOT claimed. It is recorded as OPEN.**
No computer-assisted analytic certificate was turned into a kernel-proved theorem.

---

## 1. FILES

### FILES ADDED (all under `RequestProject/Erdos287/`)

| File | Content |
|---|---|
| `ProperGammaQFibre.lean` | §31 q-fibre reparametrisation, `β` multiplicativity along the fibre |
| `ProperGammaLaneRecombination.lean` | §32 `c = 1 / c = 2` lane recombination, sign-transfer firewall |
| `ProperGammaSource.lean` | §35 exact source-faithful proper-γ source `S_G^proper`, marker firewalls |
| `ProperGammaMultiplicityGeometry.lean` | §33 `N_X(m)` count, counting interpretation, exact band engine for every `k`, shells, shell certificates |
| `ProperGammaShellSix.lean` | §34 exact `Ω_{=6}` bands, disjointness, `N = 6` certificate |
| `ProperGammaCurrentSurvivor.lean` | §36 `Ω_{≥7}`, region-restricted source `R_{≥7}`, split algebra, no-bound firewall |
| `ProperGammaProductResummation.lean` | §37 `m = q n` change of variables, `m > z` firewall, complementary `n` geometry |
| `ProperGammaOddConvolution.lean` | §38 `g_z = 1_odd * h_z`, `ρ_odd`, factor-two error, divisor-moment certificates |
| `ProperGammaTruncatedDivisor.lean` | §39 truncated divisor coefficient `A_z(m)` vs the all-`q` identity |
| `ProperGammaMultiplicityLedger.lean` | §40 exact ownership arithmetic, parent/child no-double-charge law, global-ledger firewall |
| `CurrentStatusEffectivityMultiplicity.lean` | §41 evidence taxonomy, status ledger, open frontier, axiom audit |

### FILES MODIFIED

| File | Change |
|---|---|
| `RequestProject/Main.lean` | one added import: the new aggregator `CurrentStatusEffectivityMultiplicity` |

**No existing module was rewritten.** `BsrcWeights.lean`, `AllComplement.lean`,
`OddHalfDivisor.lean`, `Reflection.lean`, `MediumLedger.lean`, `C1C2Splice.lean`,
`OddLineCancellation.lean`, `RatioBoundary.lean`, `EulerLocal.lean`, `TwoVariableZ.lean`,
`PerronAlgebra.lean`, `IncrementalDirectedLedger.lean`, `CurrentStatusEffectivity.lean`,
`CompletePeriodEndpoint.lean`, `LambdaWeights.lean`, `EdgeCutoffLedger.lean`,
`AggregateThreshold.lean`, `AllQResummation.lean`, `ChartEquivalence.lean`,
`CurrentStatusEffectivityLongFibre.lean` are untouched and are *reused* (the new layer imports
`BsrcWeights`, `AllQResummation`, `EdgeCutoffLedger`, `CurrentStatusEffectivityLongFibre`).

---

## 2. THEOREM-BY-THEOREM EVIDENCE CLASS

All names live in `Erdos287.Effectivity`.

### 2.1 q-fibre algebra — KERNEL_PROVED
* `qFibre_reparam` — for odd squarefree `ℓ` and `d ≠ 0`: `d ∣ ℓ ∧ d < ℓ ↔ ∃! q, ℓ = d q, q > 1, q odd, q squarefree, gcd(d,q) = 1`.
* `qFibre_unique`, `qFibre_proper`, `qFibre_odd_squarefree`, `odd_squarefree_of_dvd`.
* `beta_qFibre_mul`, `beta_qFibre_mul_general` — `β(dq) = β(d)β(q)` under the exact fibre hypotheses.
* `beta_mul_not_general` — firewall: multiplicativity fails without coprimality (`d = q = 3`).

### 2.2 Lane recombination — KERNEL_PROVED
* `lane_sign_transfer` — `μ(2d) = −μ(d)` for odd `d`; `B0_two_mul` — `B0(2d) = B0(d)`.
* `lane_recombination`, `lane_recombination_z` — `σ_c μ(d) B(d) = μ(z) B(z)`, `z = c d`, `c ∈ {1,2}`, `σ₁ = 1`, `σ₂ = −1`.
* `lane_signs_survive` — the signs are *transferred into* `μ(z)`, not deleted.
* `lane_range_restricted_no_cancellation` — firewall: the same-`d` odd-lattice cancellation is **not** a source identity for the disjoint γ-entry ranges.

### 2.3 Multiplicity shells — KERNEL_PROVED
* `mem_multiplesIn`, `multiplesIn_card`, `NX_nonneg` — `N_X(m) = ⌊9X/10/m⌋ − ⌊7X/10/m⌋` counts exactly the multiples of `m` in `(7X/10, 9X/10]`.
* `NX_ge_iff_raw`, `NX_ge_iff` — normalised band form with `t = m/X`.
* `multAtLeast_iff` — **the engine**: for every `k ≥ 1`, `{t > 0 : N ≥ k}` is exactly
  `(0, 9/(10(c_k+k−1))] ∪ ⋃_{n=a_k}^{c_k−1} (7/(10n), 9/(10(n+k−1))]`, `a_k = ⌊7(k−1)/2⌋+1`, `c_k = ⌊7k/2⌋+1`.
* `bandsOf_one … bandsOf_seven` — the explicit bands for `k = 1,…,7`.
* `NX_eq_iff`, `ShellEq`, `shellEq_disjoint`, `multAtLeast_mono`, `multAtLeast_le`.
* `shellOne_bands` — the exactly-one-multiple owner is the union of exactly **seven** disjoint bands
  `(9/80,7/60] ∪ (9/70,7/50] ∪ (3/20,7/40] ∪ (9/50,9/40] ∪ (7/30,3/10] ∪ (7/20,9/20] ∪ (7/10,9/10]`,
  disjoint from `N = 0` and from `N ≥ 2` by construction.
* Multiplicities `2..5`: their exact geometry is the specialisation `bandsOf_two … bandsOf_five` of the same kernel-proved engine, with `NX_eq_iff` giving `N_X(m) = k ↔ t ∈ Ω_{=k}` and `shellEq_disjoint` giving disjointness from `N = 1`, from `N ≥ 6` and from each other.

### 2.4 Exact `N = 6` geometry — KERNEL_PROVED
* `shellSix_bands` — `Ω_{=6} = (9/310,7/240] ∪ (3/100,7/230] ∪ (9/290,7/220] ∪ (9/280,9/260] ∪ (7/200,9/250] ∪ (7/190,3/80] ∪ (7/180,9/230]` at the exact endpoint conventions (`A` excluded, `Z` included).
* `NX_eq_six_iff` — `N_X(m) = 6 ↔ m/X ∈ Ω_{=6}`.
* `shellSix_disjoint_lower`, `shellSix_disjoint_seven` — disjoint from shells `1..5` and from `N ≥ 7`.

### 2.5 Proper-γ source — KERNEL_PROVED DEFINITION
* `ProperGammaData`, `ProperQ`, `sourceWeight`, `properZSum`, `SGproper`, `SGproper_eq` — the source retains the top-two γ admission `e(z)`, the liveness marker, the continuous endpoint `I_X(z,q)`, the squarefree and coprimality conditions and all signs. **No closing estimate is attached.**
* `SGproper_drop_qfilter`, `SGproper_dead`, `SGproper_lane_weight`.
* `coprimality_marker_matters`, `liveness_marker_matters`, `firewall_SGproper` — the markers are not decoration.

### 2.6 Current survivor `N ≥ 7` — KERNEL_PROVED DEFINITION, analytic bound OPEN
* `OmegaSevenPlus`, `omegaSevenPlus_eq` — `(0,9/310] ∪ (7/240,3/100] ∪ (7/230,9/290] ∪ (7/220,9/280]`.
* `mem_omegaSevenPlus_iff`, `NX_ge_seven_iff` — the region is exactly `{N ≥ 7}`.
* `SGregion`, `SGregion_split`, `Rge7`, `Rge7_split`, `Rge7_dead`.
* `Rge7_not_bounded_here` — the survivor source is genuinely nonzero for admissible data: **no smallness proposition is inhabited anywhere.**

### 2.7 `m = q n` correction and the `m > z` firewall — KERNEL_PROVED
* `product_resummation` — `∑_{q ∣ m, z < m ≤ M} f(m) = ∑_{z < q n ≤ M} f(q n)`, lower cutoff retained.
* `fibre_range_exact`, `cutoff_subset`.
* `lower_cutoff_matters` — dropping `m > z` **changes** the source (explicit two-term witness).

### 2.8 Complementary `n` geometry — KERNEL_PROVED (reconstructed thresholds)
* `bandIndex_ge_22` / `bandIndex_le_21_absent` — indices `n ≤ 21` are geometrically absent (this reproduces the reported `n ≤ 21: absent`).
* `bandIndex_exceptional` — `n ∈ {22,23,24}` is the exceptional finite geometry, each index pinning one explicit rational band.
* `bandIndex_chain` — from `n = 25` on the bands merge and `t ≤ 9/310`.
* **Deviation recorded honestly:** the research run reported the split as `22 ≤ n ≤ 30` exceptional and `n ≥ 31` passing. In the coordinates formalised here (the band index of `Ω_{≥7}`) the reconstructed split is `22 ≤ n ≤ 24` exceptional and `n ≥ 25` chain-merged; only the reconstructed statement is banked. The `n ≤ 21` absence agrees with the report.
* `FibreArithmetic`, `geometry_not_arithmetic`, `arithmetic_not_geometry` — the arithmetic conditions (`n ∣ m`, `q = m/n > 200`, `q` odd squarefree, `(q,z) = 1`, `m > z`) are kept strictly separate from the geometry, in both directions.

### 2.9 Truncated divisor identity — KERNEL_PROVED
* `AzTruncated`, `AzComplete`, `AzExcluded`.
* `truncated_divisor_decomposition`, `truncated_divisor_identity` — `A_z(m) = B(zm)/B(z) − (excluded closed-owner divisor sums)`, reusing `allQ_divisor_identity` from `AllQResummation.lean` (§28).
* `truncated_eq_complete_iff`; `truncated_ne_complete` — firewall: `A_z(m) = B(zm)/B(z)` is false without the subtraction.

### 2.10 Odd convolution algebra — KERNEL_PROVED; series identity CONDITIONAL_ANALYTIC
* `gz`, `hzRaw`, `hz`, `sum_divisors_hzRaw`, `oddConvolution_identity` — the exact convolution `g_z = 1_odd * h_z`.
* `rhoOdd`, `abs_rhoOdd_le` (`|ρ_odd(x)| ≤ 1/2`), `oddCount_exact`.
* `oddError_bound`, `HzMoment`, `EzError`, `factorTwo_Ez` — `|E_z(x)| ≤ (1/2) H_{z,α} x^α` at the finite level, `1/2 < α < 1` admissible (only `α > 0` is needed).
* `OddSeriesClaim`, `oddSeries_hypothesis_used`, `oddSeries_sum_unique` — `∑_d h_z(d)/d = 1/B(z)` is a **hypothesis-level interface**, not a theorem: `CONDITIONAL_ANALYTIC`. No custom axiom was introduced.
* `H0Bound`, `C1Bound`, `C35Bound`, `divisorMoment_bounds_exact`, `divisorMomentCertificate_not_proved` — `H₀ < 88/5`, `C₁ < 5/4`, `C_{3/5} < 31/10` are `CERTIFICATE_BACKED` typed objects; only their exact rational values are kernel content.

### 2.11 Ownership ledger — KERNEL_PROVED ARITHMETIC (values are certificate-backed inputs)
* `ownerQ200 = 1.83e-8`, `ownerN1 = 2.4e-8`, `ownerN2to5 = 2.16e-8`, `ownerN6 = 7.77e-9`, `owner_values_exact`, `ownerN6_is_shellSixCharge`.
* `allocatedTotal_eq` — the four owners sum to exactly `7.167e-8`.
* `properGammaTarget = 7.204976032e-8`; `childRemaining_eq` — exact child remaining capacity `3.7976032e-10`.
* `parentAvailable_eq` — exact parent (`N ≥ 6`) allocation `8.14976032e-9`.
* All arithmetic is exact rational arithmetic (`ℚ`), never floating point.

### 2.12 Parent / child no-double-charge law — KERNEL_PROVED
* `MultiplicityChart` (`child`, `parent`), `chargesShellSix`, `survivorFloor`, `chartAllocated`, `chartRemaining`, `chart_remaining_values`, `chart_budget_exact`.
* `parent_child_owner_disjoint` — in each chart the surviving region is disjoint from the separately charged owners.
* `shell6_parent_recombine_legal` — `parentAvailable = childRemaining + ownerN6`; recombination is legal.
* `shell6_double_charge_illegal` — using the parent `N ≥ 6` allowance **and** charging shell `N = 6` strictly overspends the proper-γ target, while each chart separately closes it exactly.
* `chart_choice_exclusive` — exactly one chart may be used.

### 2.13 Global ledger firewall — UNCHANGED PENDING RECONCILIATION
* `global_ledger_unchanged` — the global certified subtotal `5.257263872e-7` and the global remaining capacity `3.603386128e-7` of §26/§30 are unchanged.
* `properGamma_internal_only` — the proper-γ target is strictly inside the global remaining capacity, so this internal reallocation cannot by itself close the global ledger.

### 2.14 Status / frontier — KERNEL_PROVED
* `Evidence` (`kernelProved`, `certificateBacked`, `conditionalAnalytic`, `retiredNonclosingMethod`, `openNode`, `notEntered`), `Evidence.isClosed`, `MultiplicityNode`, `multiplicityEvidence`, `multiplicityOpenNodes`.
* `properGammaMultiplicity_open_frontier` — no open node is tagged kernel-proved, certificate-backed or closed.
* `erdos287_open_multiplicity`, `survivor_Nge7_open`, `numerical_closures_are_certificates`, `exact_algebra_is_kernel_proved`, `retired_nonclosing_methods`, `identity_factory_status`, `longFibre_preserved`.

### 2.15 CERTIFICATE_BACKED (never kernel-proved here)
`q ≤ 200 : 1.83e-8`; `N = 1 : 2.4e-8`; `N = 2..5 : 2.16e-8`; `N = 6 : 7.77e-9`;
`H₀ < 88/5`, `C₁ < 5/4`, `C_{3/5} < 31/10`.
Each is represented by a typed certificate object; `shellCertificate_not_proved`,
`shellSix_certificate_not_proved` and `divisorMomentCertificate_not_proved` prove that
inhabiting such an object carries **no** analytic content. An external verifier replaying the
arithmetic does not upgrade these to `KERNEL_PROVED`.

### 2.16 RETIRED / NONCLOSING and OPEN
* Retired at the current wrapper scope: extending the absolute Stieltjes-variation norm uniformly into the complete many-multiple `t → 0` tail (`absoluteVariationTail`). No lower bound for the physical signed source is asserted anywhere; the firewall records only that this method does not deliver the required certified bound.
* Open: the weighted `K_s` closing recurrence (only the exact count identity is banked); the closing prefix bound for the restricted Möbius coefficient (the general identity landing is typed as a legal external, conditional input).
* Open: `N ≥ 7` signed source, `N ≥ 6` recombined parent, proper-γ full closure, `S_live`, `R_012`, signed floor, final splice, Erdős #287. Not entered: Maynard.

---

## 3. AXIOM DEPENDENCIES

`CurrentStatusEffectivityMultiplicity.lean` runs `#print axioms` on every principal new
theorem (§41.3). Every one reports only

```
propext, Classical.choice, Quot.sound
```

(or fewer — several status and ledger theorems depend on no axioms at all, and
`qFibre_unique` depends only on `propext`).

No `sorry`, `sorryAx`, `admit`, custom `axiom`, `native_decide`, `Lean.trustCompiler`,
`unsafe`, `@[implemented_by]` or `opaque` workaround occurs in any new file. All finite
verifications use ordinary kernel `decide` / `norm_num` / `omega`.

---

## 4. BUILD

* **Dedicated builds** — every new module was built individually and passes:
  `RequestProject.Erdos287.ProperGammaQFibre`, `…ProperGammaLaneRecombination`,
  `…ProperGammaMultiplicityGeometry`, `…ProperGammaShellSix`, `…ProperGammaSource`,
  `…ProperGammaCurrentSurvivor`, `…ProperGammaProductResummation`,
  `…ProperGammaOddConvolution`, `…ProperGammaTruncatedDivisor`,
  `…ProperGammaMultiplicityLedger`, `…CurrentStatusEffectivityMultiplicity`.
* **Full build** — `lake build`: PASS (see the STRICT FINAL OUTPUT below for the recorded
  result of the final run).
* Pre-existing lint warnings elsewhere in the repository are unchanged; the new files are
  warning-free.

---

## 5. STRICT FINAL OUTPUT

```
LONG-FIBRE BANK:                         PRESERVED
q-FIBRE REPARAMETRIZATION:               KERNEL-PROVED
LANE RECOMBINATION:                      KERNEL-PROVED
PROPER-GAMMA SOURCE:                     KERNEL-PROVED DEFINITION
MULTIPLICITY COUNT GEOMETRY:             KERNEL-PROVED
q<=200 NUMERICAL CLOSURE:                CERTIFICATE-BACKED
N=1 NUMERICAL CLOSURE:                   CERTIFICATE-BACKED
N=2..5 NUMERICAL CLOSURE:                CERTIFICATE-BACKED
N=6 GEOMETRY:                            KERNEL-PROVED
N=6 NUMERICAL CLOSURE:                   CERTIFICATE-BACKED
m=q*n PRODUCT CHANGE:                    KERNEL-PROVED
m>z LOWER-CUTOFF FIREWALL:               KERNEL-PROVED
TRUNCATED ALL-q IDENTITY:                KERNEL-PROVED
ODD-CONVOLUTION ALGEBRA:                 KERNEL-PROVED
FACTOR-TWO ERROR ALGEBRA:                KERNEL-PROVED (finite level)
CURRENT CHILD ALLOCATION 3.7976032e-10:  KERNEL-PROVED ARITHMETIC
N>=6 PARENT ALLOCATION 8.14976032e-9:    KERNEL-PROVED ARITHMETIC
PARENT/CHILD DOUBLE-CHARGE FIREWALL:     KERNEL-PROVED
CURRENT EXACT SURVIVOR N>=7:             KERNEL-PROVED DEFINITION
N>=7 ANALYTIC BOUND:                     OPEN
N>=6 RECOMBINED ANALYTIC BOUND:          OPEN
PROPER-GAMMA:                            STRICTLY REDUCED / OPEN
S_live:                                  OPEN
R_012:                                   OPEN
SIGNED FLOOR:                            OPEN
MAYNARD:                                 NOT ENTERED
FINAL SPLICE:                            OPEN
ERDŐS #287:                              OPEN
FULL LAKE BUILD:                         PASS
DEDICATED BUILD:                         PASS
AXIOM AUDIT:                             PASS
```

STOP.
