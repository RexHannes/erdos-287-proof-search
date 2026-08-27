# Erdős #287 — V14: exact Vaughan source / prime-modulus two-outer structural Leanification

**ERDŐS #287 REMAINS OPEN.**  Nothing in this run proves it.  In particular nothing here
proves `AFFINE287-PRIME-MODULUS-MU-TWOOUTER45`, smallness of the `k = 0` smooth-parity
packet, FCL, Gate 1A or Gate 1B closure, `WindowPairSupply` for all large `M`, or the Twin
Prime Conjecture.

## WORKSPACE / COMMIT

Resumed in place on the existing branch; no fresh checkout, append-only except for six
import lines in `RequestProject/Main.lean`.  No historical theorem statement was modified,
renamed, weakened or deleted.

**Workspace guard — all required files verified present before any mathematics:**

```
RequestProject/Erdos287/FixedCertificateSingletonParameters.lean   present
RequestProject/Erdos287/FixedCertificateSingletonFragment.lean     present
RequestProject/Erdos287/FixedCertificateSingletonCompiler.lean     present
RequestProject/Status/Erdos287SingletonV13Status.lean              present
RequestProject/Erdos287/FixedCertificateFordData.lean              present
RequestProject/Erdos287/FixedCertificateThreeError.lean            present
RequestProject/Erdos287/FixedCertificateSmoothParity.lean          present
RequestProject/Erdos287/FixedCertificateOrderCounterguard.lean     present
```

`ERDOS287_ARISTOTLE_WORKSPACE_MISMATCH` does **not** apply.

## FILES ADDED

```
RequestProject/Erdos287/FordGeneratedDepth.lean        (Part 2)
RequestProject/Erdos287/AffineVaughanIdentity.lean     (Parts 3, 4)
RequestProject/Erdos287/AffineVaughanPrimeOuter.lean   (Parts 5, 6, 7, 8)
RequestProject/Erdos287/AffineTwoOuterSource.lean      (Parts 9, 10, 11, 12)
RequestProject/Erdos287/AffineTwoOuterCompiler.lean    (Parts 13, 14, 15, 16)
RequestProject/Status/Erdos287VaughanV14Status.lean    (Parts 17, 19)
ERDOS287_VAUGHAN_V14_REPORT.md                         (this file)
```

`FordGeneratedDepth.lean` is one file more than the suggested plan: the Part 2 finite
arithmetic is independent of the Vaughan algebra and is kept separate rather than mixed
into `AffineVaughanIdentity.lean`.

## FILES EDITED

`RequestProject/Main.lean` — six import lines appended.  Nothing else.

## SOURCE MAP

| Brief | Lean object | File |
|---|---|---|
| Ford depth `N ≤ 112 / 76 / 40` | `general_ford_depth_le_112`, `fixed_certificate_depth_le_76`, `k0_depth_le_40` | `FordGeneratedDepth.lean` |
| Exact Vaughan identity | `vaughan_identity_abstract`, `vaughan_identity_exact` | `AffineVaughanIdentity.lean` |
| Pointwise `I1/I2/II` form | `I1`, `I2`, `II`, `vaughan_pointwise`, `vaughan_pointwise_of_lt` | `AffineVaughanIdentity.lean` |
| Affine specialisation `2mn ± 1` | `AffineSign`, `affineNat`, `affineNat_cast`, `vaughan_affine_pointwise` | `AffineVaughanIdentity.lean` |
| Prime / prime-power router | `IsPrimeOuter`, `IsProperPrimePowerOuter`, `vonMangoldt_support_iff` | `AffineVaughanPrimeOuter.lean` |
| Exponent kernel `5/6` | `primepower_exponent_five_sixths`, `primepower_exponent_saving` | `AffineVaughanPrimeOuter.lean` |
| Prime-power analytic bound | `PrimePowerOuterBound` (uninhabited) | `AffineVaughanPrimeOuter.lean` |
| Prime-outer source cell | `AffineVaughanPrimeCell` + elementary consequences | `AffineVaughanPrimeOuter.lean` |
| Cofactor fold `q = d r` | `lambdaU`, `lambdaU_eq_neg_truncMobius`, `lambdaU_prime` | `AffineVaughanPrimeOuter.lean` |
| Support no-go | `prime_support_obstruction_to_balanced_convolution`, `vaughan_cofactor_balanced_factorization_impossible` | `AffineVaughanPrimeOuter.lean` |
| Prime-modulus orientation | `affine_prime_modulus_congruence`, `affine_prime_modulus_residue`, `affine_prime_not_dvd_m/n` | `AffineTwoOuterSource.lean` |
| Two-outer quotient / packet | `cellQuotient`, `deltaMuOne`, `AffinePrimeModulusTwoOuterPacket` | `AffineTwoOuterSource.lean` |
| Determinant-one line | `affine_coprime_of_unit_shift`, `affine_line_forward`, `affine_line_complete`, `affine_det_one_line_param`, `affine_line_param_unique` | `AffineTwoOuterSource.lean` |
| Long-line exponent | `twoOuter_line_exponent_lower_bound`, `twoOuter_line_exponent_margin`, `twoOuter_line_exponent_endpoint` | `AffineTwoOuterSource.lean` |
| Open analytic interface | `AffinePrimeModulusMuTwoOuterInput` (uninhabited) | `AffineTwoOuterCompiler.lean` |
| Comparison firewall | `Affine287TwoOuterComparisonMatch` (never proved) | `AffineTwoOuterCompiler.lean` |
| Conditional compiler | `singletonTypeII_of_vaughan_twoOuter`, `smoothParity_of_vaughan_twoOuter`, `parentLeakage_of_vaughan_twoOuter` | `AffineTwoOuterCompiler.lean` |
| Gate/F3 firewall | `Affine287ToTwoOuterF3Adapter` (uninhabited) | `AffineTwoOuterCompiler.lean` |

Reused from the bank without re-proof: `nu0` / `nu0R = 16623/100000`, `sigmaOf`,
`AdmissibleEps`, `SingletonClass`, `FordSmoothFragmentCertificate`,
`canonical_singleton_typeII`, `singleton_real_power_window`,
`singleton_complement_depth_le_39`, `SingletonGeneratedTypeIIInput`,
`SingletonPacketReduction`, `K0CellIdentitySource`, `truncMobius`,
`sum_moebius_divisors_eq_zero`, `truncMobius_prime`,
`FixedCertificateSmoothParityPacket`, `smoothParity_of_singletonTypeII`,
`parentLeakage_of_singletonTypeII`.  `K0CellIdentitySource` remains external.

## NEW THEOREMS (all kernel-checked, sorry-free)

**Part 2 (PROVED_FINITE):** `fordGeneratedDepth_mono`, `general_ford_depth_le_112`,
`general_ford_depth_sharp`, `fixed_certificate_depth_le_76`,
`fixed_certificate_depth_le_76_of_factors`, `fixed_certificate_depth_sharp`,
`k0_depth_le_40`, `k0_depth_sharp`, `depth_constants_ordered`, `k0_complement_depth`.

**Part 3 (PROVED_ALGEBRAIC):** `trunc_add`, `truncGt_eq_sub`, `sub_apply'`,
`vaughan_identity_abstract`, `vaughan_identity_exact`, `conv_zeta_apply`, `mul_log_apply`,
`vaughan_pointwise`, `vaughan_pointwise_of_lt`.

**Part 4 (PROVED_ALGEBRAIC):** `AffineSign.val_eq_one_or`, `AffineSign.val_ne_zero`,
`affineNat_cast`, `affineNat_pos`, `affineNat_odd`, `vaughan_affine_pointwise`,
`vaughan_affine_pointwise_full`.

**Part 5 (PROVED_FINITE + exponent ledger):** `vonMangoldt_outer_partition`,
`not_isPrimeOuter_and_isProperPrimePowerOuter`, `vonMangoldt_ne_zero_of_isPrimeOuter`,
`vonMangoldt_ne_zero_of_isProperPrimePowerOuter`, `vonMangoldt_support_iff`,
`primepower_exponent_five_sixths`, `primepower_exponent_saving`,
`primePowerOuter_le_of_bound`.

**Part 6:** `AffineVaughanPrimeCell.value_pos`, `.prime_dvd_value`, `.cofactor_dvd_value`,
`.d_pos`, `.p_ne_two`, `.p_odd`, `.three_le_p`.

**Part 7 (PROVED_ALGEBRAIC):** `lambdaU_eq_neg_truncMobius`, `lambdaU_prime`.

**Part 8 (PROVED_FINITE / STRUCTURAL_NO_GO):**
`prime_support_obstruction_to_balanced_convolution`,
`vaughan_cofactor_balanced_factorization_impossible`,
`lambdaU_ne_balanced_convolution_at_prime`.

**Part 9 (PROVED_ALGEBRAIC):** `affine_prime_modulus_congruence`,
`affine_prime_modulus_residue`, `affine_prime_not_dvd_m`, `affine_prime_not_dvd_n`,
`cell_coprime`.

**Part 10:** `cellQuotient_mul_p`, `cellQuotient_eq_div`, `deltaMuOne_antidiagonal`,
`AffinePrimeModulusTwoOuterPacket.sum_def`, `.sum_empty`.

**Part 11 (PROVED_ALGEBRAIC):** `affine_coprime_of_unit_shift`, `affine_line_forward`,
`affine_line_complete`, `affine_det_one_line_param`, `affine_line_param_unique`.

**Part 12 (EXPONENT_KERNEL):** `twoOuter_line_exponent_lower_bound`,
`twoOuter_line_exponent_margin`, `twoOuter_line_exponent_endpoint`.

**Part 15 (PROVED_COMPILER):** `singletonTypeII_of_vaughan_twoOuter`,
`smoothParity_of_vaughan_twoOuter`, `parentLeakage_of_vaughan_twoOuter`,
`twoOuter_bound_transfer_of_adapter`.

## OPEN INTERFACES (stated, never inhabited)

`PrimePowerOuterBound` (CONDITIONAL_INTERFACE),
`AffinePrimeModulusMuTwoOuterInput` (OPEN_ANALYTIC),
`VaughanTypeIGeneratedKappaInput` (OPEN_ANALYTIC / CONDITIONAL_INTERFACE),
`Affine287ToTwoOuterF3Adapter` (CONDITIONAL_INTERFACE).

## SOURCE-BLOCKED

`Affine287TwoOuterComparisonMatch` (comparison-side decomposition),
`K0CellIdentitySource` (unchanged from V13),
`SingletonPacketReduction` (unchanged from V13).

## FAILED TARGETS

None.  Every target of the brief was either proved at the stated classification or, where
the brief itself required an interface, recorded as an uninhabited interface.  No target
was downgraded and no statement was found false.

One deviation worth flagging: the depth model of Part 2 (`2s + k·ell`) is a *definition*
chosen so that the published inputs `s ≤ 20`, `k ≤ 6`, `ell ≤ 12` give exactly `112`, and
`k = 0` gives exactly `40`.  The `76` constant is proved from the halved high-prime budget
`k·ell ≤ 36` (equivalently `k ≤ 3`, `ell ≤ 12`), which is an input hypothesis, not a
consequence.  Lean does not prove Ford–Maynard Lemma 7.17 and does not claim to.

## AXIOM / PLACEHOLDER AUDIT

`lake build` succeeds: **Build completed successfully (8111 jobs)**, no errors.

Repository-wide search of all `*.lean` sources for `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, `native_decide`, `@[implemented_by]`: **zero occurrences in Lean code**; the only
matches are documentation prose in comments.

`#print axioms` is emitted at build time for every principal new theorem by
`RequestProject/Status/Erdos287VaughanV14Status.lean`.  Every one reports a subset of
`[propext, Classical.choice, Quot.sound]`.

## FINAL LEDGER

```
FORD-GENERATED-DEPTH-N0-287                    PROVED_FINITE
  input bounds s ≤ 20, k ≤ 6, ell ≤ 12         PUBLISHED_EXTERNAL_INPUT
AFFINE287-VAUGHAN-IDENTITY                     PROVED_ALGEBRAIC
AFFINE287-VAUGHAN-SOURCE-ALGEBRA               PROVED_ALGEBRAIC
AFFINE287-VAUGHAN-PRIME-SOURCE                 PROVED_ALGEBRAIC
AFFINE287-VAUGHAN-PRIMEPOWER                   CONDITIONAL_INTERFACE
VAUGHAN-COFACTOR-TRUNCMOBIUS-IDENTITY287       PROVED_ALGEBRAIC
VAUGHAN-COFACTOR-WELLFACTORABLE-NOGO           PROVED_FINITE
AFFINE287-PRIME-MODULUS-SOURCE                 PROVED_ALGEBRAIC
AFFINE287-TWOOUTER-LINE-PARAMETRISATION        PROVED_ALGEBRAIC
AFFINE287-TWOOUTER-LINE-LENGTH45               PROVED_ALGEBRAIC
AFFINE287-PRIME-MODULUS-MU-TWOOUTER45          OPEN_ANALYTIC
AFFINE287-TWOOUTER-COMPARISON-MATCH45          SOURCE_BLOCKED
VAUGHAN-TYPEI-GENERATED-KAPPA45                OPEN_ANALYTIC / CONDITIONAL_INTERFACE
VAUGHAN-TWOOUTER-COMPILER                      PROVED_COMPILER
K0-CELL-IDENTITY                               SOURCE_BLOCKED
SMOOTH-PARITY                                  CONDITIONAL_INTERFACE / OPEN_ANALYTIC
FCL                                            OPEN_ANALYTIC
ERDOS287                                       OPEN_ANALYTIC
```

The sixteen hostile checks of Part 17 are answered one by one in the docstring of
`RequestProject/Status/Erdos287VaughanV14Status.lean`.
