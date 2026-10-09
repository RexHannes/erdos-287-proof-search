# ERDŐS #287 — EXISTING FORMAL BANK INDEX

**INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.**
**No public Erdős problem number is claimed. Public-problem-id provenance: `PENDING`.**

Checkpoint: `2026-09-08`, version `BOUNDED_CONDUCTOR_SYNC_v1`.

This index records the bank that existed **before** the bounded-conductor sync.
It is a discovery/inventory document: **nothing listed here was rewritten or deleted**
by the current run.  The EARLY_4490 bank remains a valid ancestor; only its role as the
*current root coordinate* is retagged `SUPERSEDED` in the new aggregator
(`Erdos287.Effectivity.early4490_preserved_as_ancestor`).

Evidence taxonomy used throughout (§1):

```
KERNEL_PROVED        entire proof reconstructed in the Lean kernel
CERTIFICATE_BACKED   backed by a checked finite certificate / data object
EXTERNAL_ANALYTIC    quoted external analytic input, not formally reconstructed
CONDITIONAL_ANALYTIC proved only under an explicitly stated analytic hypothesis
OPEN                 open
RETIRED_NONCLOSING   method retired because it cannot close its target
FALSE                refuted
SUPERSEDED           correct, but no longer the current root coordinate
NOT_ENTERED          not entered into the programme
```

Totals of the pre-existing bank (modules under `RequestProject/Erdos287/`, excluding the
17 modules added by the current sync): **159 modules, 1530 theorems/lemmas, 678
definitions/structures/inductives**.

---

## 1. Principal ancestor modules (theorem-level)

| Theorem | Module | Evidence | Reuse status in the bounded-conductor sync |
| --- | --- | --- | --- |
| `abel_summation_general` | `Early4490FiniteACompiler` | KERNEL_PROVED | **REUSED** — the discrete summation-by-parts engine of `compensated_summation_by_parts` |
| `finiteA_compiler`, `finiteA_compiler_untruncated`, `finiteA_partial_summation`, `Fcompiler_succ_sub` | `Early4490FiniteACompiler` | KERNEL_PROVED | preserved; pattern reused for `Qell_compiler` |
| `wCoef_eq_mu_B_div_B1`, `wCoef_eq_zero_of_not_squarefree`, `mem_aWindow`, `MtruncN_ne_zero`, `MtruncN_dvd`, `largePrime_mask_irrelevant`, `Pcompiler_eq_zero_of_gt` | `Early4490FiniteACompiler` | KERNEL_PROVED | preserved, unchanged |
| `compiler_not_fibre_annihilation` | `Early4490FiniteACompiler` | KERNEL_PROVED (firewall) | preserved; ancestor of `second_dfibre_double_count` |
| `bern2_values`, `bern3_values`, `bern2_reflect`, `bern3_reflect`, `psiSaw_reflect`, `psiSaw_endpoint`, `bern2Poly_eval`, `bern3Poly_eval`, `psiPoly_eval`, `bernoulli_derivative_ladder` | `Early4490BernoulliJet` | KERNEL_PROVED | **REUSED** — strict Bernoulli endpoint convention of the compensated SBP |
| `Phi3_eq`, `Phi3_sub_PhiPsi`, `Phi3_zero_jet`, `Phi3_additive_in_jet`, `jetR_mem`, `bernoulliJet_downstream_algebra` | `Early4490BernoulliJet` | KERNEL_PROVED | preserved |
| `bernoulliJetIdentity_not_proved` | `Early4490BernoulliJet` | CONDITIONAL_ANALYTIC (firewall) | preserved |
| `dftCoef_eq`, `finite_dft_inversion`, `sum_zmod_eq_sum_range`, `dftCoef_zero_eq_zeroMode`, `sum_range_bern2`, `sum_multiples_reindex`, `coprime_sum_mobius`, `mobius_id_divisors_squarefree`, `reflect_zero_mode`, `f1_zero_mode`, `f2_zero_mode`, `f3_zero_mode` | `Early4490FiniteDFT` | KERNEL_PROVED | **REUSED** as the q-DFT layer under `FixedConductorCharacterBound` |
| `f1_zeroMode_needs_q_gt_one`, `maskedCorrection_zero_mean`, `f2_zeroMode_mask_firewall` | `Early4490FiniteDFT` | KERNEL_PROVED (firewalls) | preserved |
| `rhoOdd_near_odd`, `sum_divisors_hz_odd`, `nearResonance_identity` | `Early4490NearResonance` | KERNEL_PROVED | preserved |
| `nearResonance_no_smallness` | `Early4490NearResonance` | KERNEL_PROVED (firewall) | preserved; pattern reused in `sbp_no_smallness_asserted` |
| `omegaEarly_eq`, `omegaEarly_no_pairs`, `Jjoint_linear_decomposition`, `J3src_eq`, `Jpsisrc_eq`, `J3src_eq_Jpsisrc_of_flat_jet` | `Early4490RationalJetSource` | KERNEL_PROVED | preserved as ancestor coordinate |
| `joint_split_charging_firewall`, `rationalJet_charts_are_alternatives` | `Early4490RationalJetSource` | KERNEL_PROVED (firewalls) | preserved |
| `earlyJoint_target_open` | `Early4490RationalJetSource` | OPEN | preserved; now recorded `early4490Leaf = OPEN` |
| `c3_ownership_arithmetic`, `slab_partition`, `slab_endpoints_exact`, `early4490_range_arithmetic`, `range_integer_consequence`, `target3_budget_arithmetic`, `targetPsi_budget_arithmetic`, `chart_budget_closes` | `Early4490RationalJetLedger` | KERNEL_PROVED | **REUSED** as the owner-ledger ancestor of `ConductorComplementLedger` |
| `properGamma_ledger_unchanged_by_early4490`, `rationalJet_alternative_chart_no_double_charge`, `numerical_certificates_not_theorems`, `range_data_are_certificates`, `replacement_certificates_not_proved`, `lateSubslab_certificate_not_proved` | `Early4490RationalJetLedger` | CERTIFICATE_BACKED / firewalls | preserved |
| `gammaPar_eq_a0_add_half_nu`, `four_nuPar_gt_gammaPar`, `gammaPar_pos`, `nuPar_pos`, `nuPar_lt_gammaPar`, `gammaR_pos`, `four_nuR_gt_gammaR`, `admission_threshold_pow`, `highPrimeCount_le_three`, `highPrime_four_impossible`, `gammaAdmission_inclusion_exclusion`, `admissionE_exceptional_case`, `admissionE_coeff_two_forced`, `admission_no_four_case`, `admissionE_no_high_primes`, `c3_source_typing`, `c3Allocation_value` | `ProperGammaAdmission` | KERNEL_PROVED | preserved; proper-gamma remains OPEN |
| `admC3_endpoint_firewall`, `c3Certificate_not_proved` | `ProperGammaAdmission` | firewall / CERTIFICATE_BACKED | preserved |
| `frontier_all_open`, `erdos287_not_claimed` | `CurrentStatusEffectivity` | KERNEL_PROVED | preserved and extended |
| `longFibre_open_frontier`, `erdos287_still_open`, `mediumK_reduced_not_closed`, `twoHigh_and_maynard_not_entered`, `v1000_edge_certified_input`, `longFibre_ledger_values` | `CurrentStatusEffectivityLongFibre` | KERNEL_PROVED | preserved and extended |
| `properGammaMultiplicity_open_frontier`, `erdos287_open_multiplicity`, `survivor_Nge7_open`, `numerical_closures_are_certificates`, `exact_algebra_is_kernel_proved`, `retired_nonclosing_methods`, `identity_factory_status`, `longFibre_preserved` | `CurrentStatusEffectivityMultiplicity` | KERNEL_PROVED | preserved; `Evidence` taxonomy **reused** and embedded into `EvidenceCurrent` |
| `retired_method_firewalls`, `early4490RationalJet_open_frontier`, `early4490_kernel_layer`, `banked_layers_preserved` | `CurrentStatusEffectivityEarly4490` | KERNEL_PROVED | **imported unchanged** by the new aggregator |

---

## 2. Full pre-existing module inventory

Counts are `theorems/lemmas` and `definitions/structures/inductives` per module.
Per-declaration evidence tags are carried in each module's own docstring header; the
default reuse status of every module below is **PRESERVED (ancestor, not rewritten)**.

| Module | Theorems | Definitions |
| --- | --- | --- |
| `AffineMuLogExponentLedger` | 5 | 1 |
| `AffineMuLogHardSource` | 9 | 7 |
| `AffineMuLogIdentity` | 8 | 1 |
| `AffineMuLogLine` | 10 | 0 |
| `AffineTwoOuterCompiler` | 4 | 5 |
| `AffineTwoOuterSource` | 18 | 4 |
| `AffineVaughanIdentity` | 16 | 8 |
| `AffineVaughanPrimeOuter` | 20 | 7 |
| `AggregateEulerLocal3221` | 8 | 7 |
| `AggregateThreshold` | 10 | 10 |
| `AllComplement` | 7 | 1 |
| `AllQResummation` | 6 | 3 |
| `BadCharacterCount3221` | 8 | 1 |
| `BadCharacterLogLedger3221` | 10 | 6 |
| `BadPrimes` | 2 | 1 |
| `BalancedSeven3221Compiler` | 3 | 1 |
| `BalancedSeven3221Grouping` | 17 | 17 |
| `BalancedSevenComparisonCompiler3221` | 8 | 4 |
| `BalancedSevenFinite` | 9 | 2 |
| `BalancedSevenFullQCompiler3221` | 6 | 3 |
| `BalancedSevenPolarization` | 10 | 3 |
| `BalancedSevenV19Compiler` | 8 | 1 |
| `BalancedSevenV20Compiler` | 11 | 2 |
| `BalancedSevenV21Compiler` | 14 | 6 |
| `Bank` | 0 | 0 |
| `BernoulliKernel` | 7 | 6 |
| `Blocker` | 12 | 2 |
| `BsrcWeights` | 16 | 4 |
| `C1C2Splice` | 5 | 4 |
| `CeilingCRT` | 21 | 5 |
| `Chain` | 6 | 5 |
| `CharacterGram3221` | 8 | 6 |
| `ChartEquivalence` | 9 | 10 |
| `ChenP2Audit` | 6 | 4 |
| `ClosureInputs` | 7 | 3 |
| `Cnum` | 17 | 0 |
| `CompletePeriodEndpoint` | 18 | 2 |
| `ConductorRouter3221` | 16 | 9 |
| `Counterexample` | 7 | 3 |
| `CurrentStatusEffectivity` | 2 | 9 |
| `CurrentStatusEffectivityEarly4490` | 4 | 6 |
| `CurrentStatusEffectivityLongFibre` | 6 | 4 |
| `CurrentStatusEffectivityMultiplicity` | 8 | 5 |
| `DIKuznetsov3221Interface` | 6 | 3 |
| `Defs` | 2 | 7 |
| `DirectedLedger` | 16 | 12 |
| `DoubleOrthogonalityFiveBox3221` | 13 | 1 |
| `EHNoWrap3221` | 13 | 2 |
| `Early4490BernoulliJet` | 17 | 13 |
| `Early4490FiniteACompiler` | 13 | 6 |
| `Early4490FiniteDFT` | 15 | 8 |
| `Early4490NearResonance` | 4 | 2 |
| `Early4490RationalJetLedger` | 14 | 25 |
| `Early4490RationalJetSource` | 9 | 5 |
| `EdgeCutoffLedger` | 9 | 8 |
| `EulerLocal` | 16 | 8 |
| `EulerUniformityLayer3221` | 7 | 3 |
| `Exponent3221Ledger` | 21 | 9 |
| `FactorialEndpoint3221Adapter` | 6 | 1 |
| `FactorialEulerLocal` | 7 | 2 |
| `FactorialEulerPolarization` | 17 | 6 |
| `FactorialPolarizationLinearity` | 4 | 4 |
| `Fiber` | 9 | 1 |
| `FiniteMasterReduction` | 14 | 4 |
| `FiniteRangeExtension` | 36 | 0 |
| `FiniteRemainder` | 3 | 1 |
| `FiveBoxCharacterFactorization3221` | 6 | 3 |
| `FixedCertificateFordData` | 17 | 6 |
| `FixedCertificateLeakageCompiler` | 4 | 9 |
| `FixedCertificateOrderCounterguard` | 14 | 2 |
| `FixedCertificateSingletonCompiler` | 7 | 5 |
| `FixedCertificateSingletonFragment` | 17 | 7 |
| `FixedCertificateSingletonParameters` | 20 | 3 |
| `FixedCertificateSmoothParity` | 11 | 2 |
| `FixedCertificateThreeError` | 5 | 0 |
| `FixedCertificateTransference` | 4 | 0 |
| `FloorInterface` | 5 | 8 |
| `Ford723BalancedSevenAdapter3221` | 4 | 3 |
| `FordGeneratedDepth` | 10 | 1 |
| `FullQStructuralPartition3221` | 21 | 13 |
| `GcdDescent` | 17 | 2 |
| `HardDyadicProviders3221` | 12 | 9 |
| `HighConductorCharacterGram3221` | 27 | 6 |
| `HighConductorSixthMoment3221` | 8 | 3 |
| `HighConductorVariance3221` | 11 | 6 |
| `HighProjectorCutoff3221` | 6 | 2 |
| `HighQuotientShiftedGram3221` | 6 | 9 |
| `IncrementalDirectedLedger` | 3 | 4 |
| `KernelAPBlocker` | 7 | 1 |
| `KummerDegeneracyRouters` | 8 | 5 |
| `KummerExponentLedger` | 9 | 0 |
| `KummerFiniteCompiler` | 3 | 0 |
| `KummerRootStabilizer` | 14 | 2 |
| `KummerWeilInterface` | 6 | 2 |
| `LambdaWeights` | 12 | 4 |
| `LogCofactorAsymptotic` | 4 | 1 |
| `MediumKSource` | 6 | 3 |
| `MediumLedger` | 6 | 7 |
| `MovingPhaseProvider3221` | 13 | 8 |
| `MuLogQCell3221` | 10 | 1 |
| `NonAdjacentHoles` | 13 | 2 |
| `NormalForm3221` | 11 | 6 |
| `OddHalfDivisor` | 11 | 3 |
| `OddLineCancellation` | 11 | 3 |
| `OffDiagonal3221` | 6 | 0 |
| `OldLocalScalarRetraction3221` | 4 | 2 |
| `OrderedSequenceBridge` | 10 | 2 |
| `OuterTwoPrimeBlock3221` | 12 | 4 |
| `PascadiParameterLedger` | 4 | 0 |
| `PerronAlgebra` | 8 | 3 |
| `PhysicalLogBudget3221` | 15 | 9 |
| `PhysicalLogPrefactorRepair3221` | 8 | 2 |
| `PlacedLCBeta` | 6 | 2 |
| `PrePoissonDensity3221` | 25 | 4 |
| `PrimeBoxL1Normalization3221` | 4 | 1 |
| `PrimeBoxNormalization3221` | 8 | 3 |
| `PrimeFree` | 2 | 0 |
| `PrincipalQCell3221` | 6 | 4 |
| `ProblemStatement` | 7 | 3 |
| `ProperGammaAdmission` | 19 | 15 |
| `ProperGammaCurrentSurvivor` | 9 | 5 |
| `ProperGammaLaneRecombination` | 8 | 2 |
| `ProperGammaMultiplicityGeometry` | 24 | 14 |
| `ProperGammaMultiplicityLedger` | 13 | 14 |
| `ProperGammaOddConvolution` | 13 | 11 |
| `ProperGammaProductResummation` | 13 | 5 |
| `ProperGammaQFibre` | 8 | 1 |
| `ProperGammaShellSix` | 7 | 2 |
| `ProperGammaSource` | 9 | 7 |
| `ProperGammaTruncatedDivisor` | 4 | 3 |
| `QPacketPartition3221` | 10 | 4 |
| `RatioBoundary` | 1 | 0 |
| `Reflection` | 10 | 0 |
| `RepeatedCores` | 8 | 7 |
| `RoughPrime` | 5 | 1 |
| `SFTAudit` | 9 | 5 |
| `SP2ClosureCompiler3221` | 14 | 3 |
| `SP2DirectSourceAdapter3221` | 9 | 2 |
| `SP2LiteralPhysicalSource3221` | 7 | 3 |
| `SP2PhysicalComparison3221` | 8 | 4 |
| `SP2PrimeBoxWeights3221` | 12 | 5 |
| `ShiuDivisorAverage3221` | 4 | 3 |
| `ShortShiftSieve3221` | 4 | 7 |
| `SmallConductorExceptional3221` | 5 | 4 |
| `SmallQSmallRAdapters3221` | 8 | 6 |
| `SophieBandCompiler` | 6 | 2 |
| `SophieOptimal` | 5 | 0 |
| `SourceAssistedDiagonal3221` | 12 | 2 |
| `SourceWeights` | 16 | 4 |
| `TopLayer` | 4 | 0 |
| `TwoHighProjector3221` | 19 | 18 |
| `TwoProjectorPhysicalClosure3221` | 10 | 2 |
| `TwoVariableZ` | 5 | 2 |
| `Uniform` | 7 | 2 |
| `Universal` | 7 | 2 |
| `V2BandSupplyChecks` | 6 | 1 |
| `V2SophieBand` | 5 | 1 |
| `V2SophieFinite` | 8 | 0 |
| `Window` | 2 | 0 |

---

## 3. Modules added by the bounded-conductor sync (not part of the ancestor bank)

`CompensatedMeasure`, `HyperbolaInterfaces`, `CompensatedSummationByParts`,
`AdjacentInterfaceFirewall`, `ResidueCollapse`, `InternalProductFibre`, `SmallEllCRT`,
`HalfOpenProgressionCompiler`, `SmallEllMeanCovariance`, `CompensationLoop`,
`BoundedConductorFrontier`, `RankThreeOperator`, `RankThreeProjection`,
`ConductorComplementLedger`, `AnnihilatorFamily`, `DensityCompensationRestoration`,
`CurrentStatusEffectivityBoundedConductor`.

See `ERDOS287_BOUNDED_CONDUCTOR_FORMAL_SYNC_REPORT.md` for their theorem/evidence table.
