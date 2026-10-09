# Erdős #287 — current asymptotic-tail consolidation: formal report

**Erdős #287 is still open. TAIL-287 is NOT BANKED.** The Opus V100 verdict is recorded as
**LOCAL-REPAIR**, as stated in the request. The live repair (Ordering B = V99 relative centering
+ V100 RBDH + V97/V98 coloured `E₁/E₂`, keeping the tiny base through the first Cauchy step)
appears in Lean **only conditionally**. No unconditional tail theorem is constructed.

> **Update: V99–V100R4 source-chain consolidation.** The new verdict is
> **`ERDOS287 SOURCE CHAIN FORMALLY CONSOLIDATED`**, at message-level source. See §9
> (`CHANGE SINCE PREVIOUS ANALYTIC INTERFACE BLOCKED`) through §12, and the files
> `ERDOS287_MINIMAL_ANALYTIC_INTERFACE.md` and `ERDOS287_MESSAGE_SOURCE_INTEGRATION_REPORT.md`.
> Sections 0–8 are the previous report, preserved unchanged as a historical record; the
> `ANALYTIC INTERFACE BLOCKED` verdict in §0 is superseded. The tail is still **not**
> banked. Status: `V100R4_AuthorCandidate`, `IndependentTailAuditPending`.

## 0. Final verdict

### `ERDOS287 ANALYTIC INTERFACE BLOCKED`

**First exact interface that cannot yet be reduced:** the Ordering-B `E₁` source dictionary.
This is the Maynard reduction that takes the literal relative main part

  `R_rel^main(X) = ∑_{j<ℓ} ∑_ξ Γ_ξ ∑_d ℓ_X(d) Δ^{f_ξ,c_ξ}_{α_j}(d, b_{ξ,d})`

(kernel-proved equal to `R_rel + R_rel^coprime`, `TensorSource.Rrel_eq_main_sub_coprimality`) to
sums of Type-II discrepancies `typeIIDiscrepancy` that satisfy **every** field of `E1Hypotheses`
(divisor-power coefficient bounds, `N`-range, `MN ≤ x`, modulus range, coprimality, smoothness,
Siegel–Walfisz condition). In Lean it is the field `OrderingBSourceDictionary.main` together with
`OrderingBSourceDictionary.e1_link`.

The kernel already proves the source-side steps leading into this reduction:
`DeltaRel_convolution`, `coefficient_placement`, `orderingB_routing`, `orderingB_pair_congr`.
The step itself is not reduced, for two reasons:

* the V97/V98/V100 texts are not in the repository (census §D), so the decomposition cannot be
  checked against its source;
* the reduction is a paper-level analytic argument, not a single estimate, so it cannot be cut
  down to a narrow provider without hiding source matching inside one.

It is therefore kept as a separately named `Candidate` hypothesis and is never folded into a
provider. The `E₂` dictionary (`e2_link`) and the RBDH link (`rbdh_link`) have the same status.
A second structural input, `SevenBlockTailFramework`, needs a 7-block CRT compiler prescription
and the main-term evaluation. Neither is in the repository.

Everything else requested is in place: the census, the exact source, RBDH algebra, the spectator
combinatorics, the Cauchy routing, near-diagonal counting, the exponent ledger, the seven-block
consumer, the recombination implication, the conditional tail theorem, the DAG, the regressions
and the audits.

## 1. Files changed

New (append-only). No existing file was modified; `audit.sh` §3 checks this against the root
commit for W3, W2.984, PostV87V90R, PostV71V87 and `ARISTOTLE_SUMMARY.md`.

* `RequestProject/Erdos287/CurrentTail.lean` (aggregator)
* `RequestProject/Erdos287/CurrentTail/`: `ExactSource`, `RelativeBDH`, `SpectatorNorm`,
  `NearDiagonal`, `OrderingBSource`, `E1Interface`, `E2Interface`, `ExponentLedger`,
  `AuxiliaryErrors`, `RemainderRecombination`, `SevenBlockConsumer`, `TailBoundary`,
  `EffectivityBoundary`, `Regressions`, `ClosureDAG`, `AxiomAudit` (`.lean`), and `audit.sh`
* `ERDOS287_CURRENT_REPOSITORY_CENSUS.md`, `ERDOS287_CURRENT_TAIL_FORMAL_REPORT.md`

Module-name mapping to the suggested list:

* "RelativeCentering" is part of `ExactSource.lean`.
* "RBDH family payment" is part of `SpectatorNorm.lean`.
* The quantitative `T_H` material is split: the provider is in `E2Interface.lean`, the
  arithmetic is in `ExponentLedger.lean`.

## 2. Results table

| Result (Lean name) | Status | Kernel proved? | External analytic input? | Independently audited? |
|---|---|---|---|---|
| `v99_relative_centering` | Exact | yes | no | identity as stated in request |
| `TensorSource.RSigmaP_eq_Rrel_add_Rpaid` | Exact | yes | no | — |
| `TensorSource.Rrel_indep_main` (zero frequency removed) | Exact | yes | no | — |
| `TensorSource.Rpaid_factor`, `Rpaid_bound` | Exact | yes | no (the bound takes the fluctuation as hypothesis) | — |
| `TensorSource.Rrel_eq_main_sub_coprimality`, `relative_term_eq_DeltaRel` | Exact | yes | no | — |
| `modEq_crt_iff`, `sum_units_ind_modEq` (CRT unit-class bijection) | Exact | yes | no | — |
| `rbdh_crt_identity` (V100 CRT identity) | Exact | yes | no | V100 RBDH: PASS (per request) |
| `variance_contraction`, `rbdh_variance_contraction` | Exact | yes | no | — |
| `crt_mapsTo_units`, `crt_injOn`, `rbdh_full_contraction` | Exact | yes | no | — |
| `card_factorization_le_tau`, `divisor_weight_transport`, `rbdh_pairs_le_weighted` | Exact | yes | no | — |
| `DeltaRel_eq_Delta_restrict`, `relativeSW_of_SW` | Exact | yes | no | — |
| `RBDH_of_BDH` (Relative-BDH from ordinary BDH) | KernelConditional | yes | `BDHStatement` (ordinary BDH; no relative content) | — |
| `card_fibre_le`, `fibre_regroup`, `spectator_norm_finite` | Exact | yes | no | — |
| `spectator_norm_of_moment` | KernelConditional | yes | `ReciprocalDivisorMoment` | — |
| `family_payment`, `fibre_weight_transport`, `family_payment_tau` | Exact | yes | no | — |
| `count_congr_le`, `count_congr_window_le`, `pairs_congr_window_le`, `pairs_congr_window_real` | Exact | yes | no | — |
| `nearDiagonal_to_reciprocalDensity` | Exact | yes | no (range comparison isolated as `NearDiagonalRangeComparison`) | — |
| `CharacterBeforeCauchy_retired`, `orderingA_loses_density`, `orderingA_loss_ge_two` | Exact (retirement evidence) | yes | no | Opus V100 finding (per request) |
| `orderingB_first_cauchy`, `orderingB_expand`, `orderingB_pair_congr`, `orderingB_pairs_subset`, `orderingB_routing` | Exact | yes | no | Ordering-B repair: **not yet audited** |
| `coefficient_placement`, `Delta_convolution`, `DeltaRel_convolution` (`E₁` source side) | Exact | yes | no | — |
| `MaynardE1Estimate` | ExternalAnalytic | — (never constructed) | yes | — |
| `fixedLocal_totient`, `fixedLocal_bound`, `crt_phase_split`, `crt_phase_split_real`, `dualLength_enlarged`, `kloostermanForm_split` (`E₂` source side) | Exact | yes | no | — |
| `PascadiE2Printed`, `QuantitativeTH` (`T_H^{7/128}`) | ExternalAnalytic (separate) | — | yes | — |
| `netSaving_chooseSigma`, `ledger_instance`, `logCost_absorbed`, `order_of_choice` | Exact | yes | no | ledger coefficients are a template (see §4) |
| `allErrors_complete`, `no_open_error`, `exactZero_iff`, `every_error_anchored` | Exact | yes | no | — |
| `RSigmaP_littleO_of_providers` | KernelConditional | yes | all listed providers + `OrderingBSourceDictionary` | — |
| `seven_block_margin_eq` (`μ²/2-μ-2ν = 199965200021/14`), `seven_block_margin`, `seven_block_margin_rat` | Exact | yes | no | — |
| `alpha_Gamma72` (`α(Γ_{7,2}) = 2`) | Exact | yes | no | — |
| `seven_block_moment_ineq`, `seven_block_three_occupied`, `seven_block_of_remainder`, `seven_block_of_littleO` | Exact (main-term dictionary as hypothesis) | yes | no | — |
| `seven_block_contact_false`, `seven_block_contact_false_of_remainder` | Exact (consumer) | yes | no | — |
| `tail_of_remainder_littleO` | KernelConditional | yes | `SevenBlockTailFramework` | — |
| **`Tail287_of_AnalyticProviders`** | **KernelConditional** | yes | yes (all providers + dictionary + framework) | **no** |
| Unconditional TAIL-287 | **not constructed** | — | — | — |
| `global_of_layers`, `tail_of_effectiveOnset` | Exact | yes | no | — |
| `reg1 … reg10` regression controls | Exact | yes | no | — |
| `dag_acyclic`, `orderingA_feeds_nothing`, `retired_feeds_nothing`, `global_preds`, `tail_not_direct_to_global` | Exact | yes | no | — |
| W3 checkpoint (`W3Publication.W3_of_provider`) | Banked (unchanged) | implication yes | `WidthThreeMomentProvider` | W3: PASS (per earlier reports) |
| W2.984 (`W2984Publication.W2984`) | Banked (unchanged) | implication yes | Chen providers + W3 framework | referee packet (unchanged) |

## 3. BANK / exact

These are kernel-proved and use no open input:

* **V99 source.** The centering identity, the literal remainders `RSigmaP`, `Rrel` and `Rpaid`
  with `R_Σ^P = R_rel + R_already_paid`, the exact zero-frequency removal and the exact
  coprimality insertion/removal.
* **RBDH algebra.** The CRT unit-class bijection, the CRT identity, variance contraction,
  injectivity of the CRT lift into units mod `fq`, coprime-factorization multiplicity `≤ τ(Q)`,
  divisor-weight transport, and relative SW from SW at modulus `fq`.
* **Spectator combinatorics.** Coordinate states, tensor states, labels and spectator modulus,
  together with the divisor-power preimage bound `3^K τ(F)^K`.
* **Cauchy routing.** The exact RBDH family payment inequality. It does no packetwise
  multiplication by `X^{2σ}`.
* **Near diagonal.** All deterministic counting under `n₁ ≡ n₂ (mod f)` (shape
  `2NH/f + 2N`, i.e. `N²/(f L^{C₀}) + N` at `H = N/L^{C₀}`) and the conversion to the
  reciprocal-density norm.
* **Ordering A / Ordering B.**
  * Ordering A: retirement status plus a counter-model. For one residue class in `[1, fK]`,
    Ordering A gives `K√f` against the truth `K`, a loss factor `√f`.
  * Ordering B: the structural routing, with the congruence kept explicit through the first
    Cauchy step.
* **`E₁/E₂` source side.** Coefficient placement, Type-II form, fixed-local split, CRT phase
  identity, Fourier-length enlargement, and the Kloosterman-form split.
* **Exponent ledger.** Rational arithmetic, the order of choice `δ_crit → σ → K → X`, and
  absorption of log costs.
* **Seven-block consumer.** `μ = 999999`, `ν = 1700001700000/7`, the margin
  `199965200021/14 > 0`, `α(Γ_{7,2}) = 2`. From these: moments within `ε ≤ 1` give three occupied
  blocks, and three occupied blocks contradict an exact word. That step goes through the trusted
  affine compiler + row-rigidity consumer `occupancy_contact_false`.
* **Effectivity firewall layers, closure DAG checks and 10 regression controls.**
* **Previously banked layers, preserved unchanged:** W3 checkpoint, W2.984 package, exact model,
  affine compiler, row rigidity.

## 4. CONDITIONAL FORMAL

These are kernel-proved implications from explicitly named inputs:

* `RBDH_of_BDH` ⟸ `BDHStatement`. This is ordinary BDH over moduli coprime to `f`, for arbitrary
  sequences; its conclusion mentions only ordinary discrepancies.
* `spectator_norm_of_moment` ⟸ `ReciprocalDivisorMoment`, the analytic estimate
  `∑_{F≤X} τ(F)^E/φ(F) ≤ C`. It is kept separate from the finite theorem.
* `RSigmaP_littleO_of_providers`, which proves `R_Σ^P = o(𝒩_X I)`. It assumes:
  * `MaynardE1Estimate`, `PascadiE2Printed`, `QuantitativeTH`, `BDHFamily`,
    `SpectatorMomentFamily`, `BaseSWProvider` and `AuxPieceProviders`;
  * the source dictionary `OrderingBSourceDictionary`, which is source matching (`Candidate`),
    not an analytic provider.

  No provider mentions `RSigmaP`, `Tail287Statement`, counterexamples or exact words; this is
  checked at build time by `#ct_assert_avoids`.
* `tail_of_remainder_littleO` ⟸ `SevenBlockTailFramework`.
* **`Tail287_of_AnalyticProviders`**: framework + dictionary + all providers ⟹
  `Tail287Statement`. The conclusion is an existential onset.

Auxiliary error ledger (`AuxiliaryErrors.lean`). Every error is named; there is no unnamed
"negligible" term.

| Error | Class (claimed) | Lean evidence |
|---|---|---|
| coprimality insertion/removal | ReciprocalDensityLogSaving | exact identity proved; size bound is an `AuxPieceProviders` field |
| large-divisor truncation | ReciprocalDensityLogSaving | provider only |
| near diagonal | ReciprocalDensityLogSaving | counting proved; range comparison isolated |
| smooth pruning (large-smooth deletion) | FixedPowerSaving | provider only |
| square-full pruning | FixedPowerSaving | provider only |
| Lemma-13.6-type remainder | ExternalProvider | provider only |
| zero-frequency / main term | **ExactZero** | `Rrel_indep_main` |
| boundary terms | FixedPowerSaving | provider only |
| base fluctuation (`R_already_paid`) | ExternalProvider | `Rpaid_bound` + `BaseSWProvider` |
| RBDH family | ReciprocalDensityLogSaving | `RBDH_of_BDH`, `family_payment_tau` |
| `E₁` bilinear | ExternalProvider | `MaynardE1Estimate` |
| `E₂` spectral | ExternalProvider | `PascadiE2Printed` + `QuantitativeTH` |

The "claimed class" column records the mechanism described in the request. Only the "Lean
evidence" column is a formal fact.

Exponent-ledger caveat:

* `7/128` is the only paper value in the ledger.
* The loss coefficients (`σ` for Fourier enlargement, `2σ` for packet population, linear `T_H`
  exponent) follow the bookkeeping listed in the request.
* The actual V97/V100 values of `δ_crit` and `c_H` are not in the repository; they are
  parameters.

## 5. PAPER-LEVEL ONLY (not formalised)

* The Ordering-B Maynard reduction (the `E₁`/`E₂` source dictionaries) and the RBDH link from
  the analytic providers to the ledger pieces.
* The proofs of Maynard's Type-II estimate, Pascadi's spectral estimate, the **quantitative
  `T_H^{7/128}` extension** (not assumed to follow from the printed `T_H = x^{o(1)}` statement;
  see `reg7_TH_printed_not_quantitative`), ordinary BDH, Siegel–Walfisz for tiny moduli, and the
  reciprocal divisor-moment bound.
* The auxiliary error estimates marked "provider only".
* The 7-block CRT compiler prescription and the main-term evaluation giving `(μ, ν)`
  (`SevenBlockTailFramework`, `SevenBlockMainTermDictionary`).
* The V97/V98 coloured `E₁/E₂` machinery, V100 RBDH (independently audited PASS according to the
  request) and the Opus V100 LOCAL-REPAIR verdict. None of these texts is in the repository.

## 6. RETIRED

* **V100 Ordering A** (`CharacterBeforeCauchy = RETIRED`). It feeds no DAG node
  (`orderingA_feeds_nothing`). The counter-model is `orderingA_loses_density`.
* **Fixed-residue-SW shortcut.** `reg2_fixedResidue_breaks_SW` is a counter-model: all
  discrepancies mod 3 vanish, but after restricting to odd `n` one of them is `1/2`. The correct
  route is SW at the lifted modulus `fq` (`relativeSW_of_SW`).
* **V96 invalid dilation.** The original V96 text is `UNFORMALISED_SOURCE`. A reconstructed
  generic control, `reg1_dilation_changes_discrepancy`, shows that dilation changes the
  discrepancy.
* **Superseded closure claims.** None is imported; the DAG marks no retired node as feeding
  anything.

## 7. OPEN

* The Ordering-B repair, until it passes independent referee audit (DAG node `orderingB` =
  `Candidate`). Also open: the `E₁`/`E₂` dictionaries and the seven-block framework.
* The effective onset (`EffectiveOnset`), the finite splice (`FiniteBank` + `IntermediateRange`)
  and global Erdős #287 (`Erdos287Global`). `global_of_layers` shows what is needed; it does not
  claim the splice.
* The dimension-floor obstruction of the current tiny-support / huge-first-moment design,
  recorded as `OpenIssue.dimensionFloor` (open optimisation issue).

## 8. Build and trust audit

* `lake build RequestProject.Erdos287.CurrentTail`: **success**.
* Full `lake build`: see §8.1.
* Checker: the environment provides **`leanchecker`**; `lean4checker` is not installed.
  * `lake env leanchecker RequestProject.Erdos287.CurrentTail`: **exit 0**, 231 s.
  * `lake env leanchecker --fresh RequestProject.Erdos287.CurrentTail`: see §8.1.
* `#ct_assert_std_axioms` runs at build time on 90 principal theorems (including
  `Tail287_of_AnalyticProviders`, `RSigmaP_littleO_of_providers`, `rbdh_crt_identity` and
  `seven_block_contact_false`). Every one depends only on `propext`, `Classical.choice` and
  `Quot.sound`. **There are no nonstandard dependencies.**
* `#ct_audit_providers`: no declaration concludes a provider, framework, dictionary or tail
  statement without a guarded hypothesis, and none takes a `False`/`IsEmpty` hypothesis. The only
  guarded-conclusion declarations are `Tail287_of_AnalyticProviders`, `tail_of_remainder_littleO`
  and `tail_of_effectiveOnset`, and each carries its inputs.
* `#ct_assert_avoids` checks 12 providers/frameworks against `RSigmaP`, `Tail287Statement`,
  `Erdos287Counterexample`, `ExactWord` and `IsLittleOTarget`. The BDH interfaces are also
  checked against `DeltaRel` and `Vrel`, so the provider is not a relative-BDH theorem.
* `#ct_assert_mentions`: the conditional tail theorem visibly carries all nine inputs.
* `audit.sh` covers the token scan (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`,
  `bv_decide`, `implemented_by`, `opaque`, `extern`, `ofReduceBool`, `False.elim`, `instance`), the
  check that no `…Unconditional` declaration or alias exists, the check that protected files are
  unchanged, the narrow build, the checker, and 6 negative controls that must fail.
* There is **no** `sorry`, `admit`, project `axiom`, `unsafe`, `native_decide`, fake provider
  instance or `False.elim` provider in the subtree. No assumption concludes TAIL-287.

### 8.1 Long-running checks (this session)

* Full `lake build`: **Build completed successfully (9020 jobs)**. The log contains no
  `declaration uses 'sorry'`.
* `lake env leanchecker RequestProject.Erdos287.CurrentTail`: exit 0 (231 s).
* `lake env leanchecker --fresh RequestProject.Erdos287.CurrentTail`: **exit 0** (2283 s).
* `audit.sh` steps 1–3 (token scan, no-unconditional/no-alias, protected files unchanged): pass.
* `audit.sh` step 6, negative controls, all rejected for the expected reason:
  1. `sorry` is rejected: non-standard axiom `sorryAx`.
  2. `native_decide` is rejected: `Lean.ofReduceBool`.
  3. A `False`-hypothesis fake `MaynardE1Estimate` is rejected by `#ct_audit_providers`.
  4. `Tail287Statement` cannot be closed.
  5. An Ordering A → tail edge is refuted by `decide`.
  6. A tail → global edge is refuted by `decide`.

---

## 9. CHANGE SINCE PREVIOUS `ANALYTIC INTERFACE BLOCKED`

Append-only. `RequestProject/Erdos287/CurrentTail/` is unchanged; `SourceChain/audit.sh` §3
checks this against the root commit. The new material is in `RequestProject/Erdos287/SourceChain/`
(aggregator `RequestProject/Erdos287/SourceChain.lean`). Source provenance: the message-level
source pack (OB.1–OB.10, AB.1/AB.2, AA.1, REC.1, FW.1–FW.6, RG.1, PH.1, TH.1–TH.3,
h-separation). The full V100R/V100R2/V100R4 papers, `COMPLETE_KERNEL_MEMBERSHIP.md` and the Opus
report were not in the repository.

| Previous open interface | New status | Lean theorem / provider |
|---|---|---|
| Ordering-B source dictionary | **split up**: kernel-proved algebra plus one per-packet source inequality on literal objects (`PAPER_VERIFIED_PARTIAL`) | `typeII_split`, `secondTerm_eq_DeltaRel`, `residueFibre_density`, `orderingB_physical_square`, `zeroMode_covariance_full`, `RrelMain_eq_sum_Sxi`, `cell_bound`, `RrelMain_bound`; remaining: `OrderingBPoissonReduction` |
| \(F_{AB}\) source/payment | **exact algebra kernel-proved**; per-cell payment reduced to numeric inputs | `rho_factor`, `rho_crt`, `poissonP_rho`, `PF_rho_scale`, `lattice_discrepancy`, `FAB_eq_sum_PF`, `FAB_split`, `FAB_kgt1_count`, `AB2_cauchy`, `k1_modulus_exponent`, `fabKgt1_cell_bound`; remaining: `|𝒫|≤V`, `τ/φ` moment, `Ψ̂` decay |
| nonclean \(F_{AA}\) | **exact sector partition kernel-proved**; `(n₁,n₂)=1` not added | `FAA_eq_sectors`, `clean_conditions`, `commonN_empty_of_not_rough`, `AA1_cauchy`, `aaShape_cell_bound`, `nearDiag_cell_bound`, `zeroMode_full_vanishes` |
| full scalar weight | **BANK_EXACT** (equality, single canonical convention `γ(𝐃)=1`) | `scalarWeight_eq_sectors`, `labelled_eq_canonical`, `canonical_gamma_one`, `parity_sign_routing` (R1) |
| low/high unique split | **BANK_EXACT** | `coprime_low_high`, `lowHigh_unique`, `abs_Gamma1_le_one`, `sectors_Gamma1_bounded` |
| range export | **kernel-conditional** on the three inequalities (constants not supplied); inequality 2 only from `θN ≤ 1/3+δ` (R3) | `Q1_absorb`, `PascadiRangeExport`, `PascadiRangeExport.ineq2_holds` |
| affine phase | **BANK_EXACT**: PH.1 proved exactly as stated, no source mismatch | `ph1_phase`, `ph1_ePhase`, `affine_phase_decomposition`, `fixedLocal_split_phase` |
| complete source membership | **source membership separated from the estimate**; the finite parts are kernel-proved; membership itself is `REFEREE_PENDING` #3/#4 | `SharpMembership` (separate from `PascadiSpectralY`), `hsep_membership`, `hsep_cost_subpower` |
| spectral estimate | **narrowed**: `QuantitativeTH` is now *derived* | provider `PascadiSpectralY` (`θexc ≤ 7/32`); `th_exponent_propagation`, `QuantitativeTH_of_spectralY` |
| final remainder | **kernel-conditional**, with the critical piece paid from the narrow provider | `rec1_recombination`, `RSigmaP_littleO_of_minimal`, `sharp_cell_bound`, `sharp_powerSaving`, `sharpPaid_of_spectralY`, `Tail287_of_NarrowProviders` |

### 9.1 Diff of providers

```
- MaynardE1Estimate            (no separate E₁ step on the message-level Ordering-B route)
- PascadiE2Printed             (superseded by PascadiSpectralY)
- QuantitativeTH               (derived: QuantitativeTH_of_spectralY, θexc ≤ 7/32)
- OrderingBSourceDictionary    (5 fields → kernel algebra + OrderingBPoissonReduction)
    main     → RrelMain_eq_sum_Sxi + cell_bound + RrelMain_bound + OrderingBPoissonReduction
    coprime  → Rrel_eq_main_sub_coprimality (exact) + CoprimalityPaid
    e1_link  → removed (F_AB / F_AA cells)
    e2_link  → sharpPaid_of_spectralY
    rbdh_link→ centeringPaid_of_RBDH
- AuxPieceProviders            (→ CoprimalityPaid, CenteringPaid, 8 named PiecePaid cells,
                                 eErrors_absent_at_one)
- BDHFamily, SpectatorMomentFamily (→ RBDH bound in centeringPaid_of_RBDH,
                                     SpectatorReciprocalNorm)
+ PascadiSpectralY             (narrow; bounded sequences only)
+ SharpMembership              (source membership; REFEREE_PENDING #3/#4)
+ OrderingBPoissonReduction    (source statement; PAPER_VERIFIED_PARTIAL)
+ SpectatorReciprocalNorm, CoprimalityPaid, CenteringPaid / RBDH bound,
  PiecePaid × 7 non-critical cells (each with a kernel-proved per-cell reduction)
= BaseSWProvider, SevenBlockTailFramework (unchanged)
```

### 9.2 Smallest remaining analytic provider set

1. Siegel–Walfisz for tiny moduli (`BaseSWProvider`, `REFEREE_PENDING` #1).
2. Divisor-weighted BDH over moduli coprime to `f` (the RBDH bound of `centeringPaid_of_RBDH`).
3. Reciprocal divisor moment (`SpectatorReciprocalNorm`).
4. Pascadi spectral `Y`-bound with `θexc ≤ 7/32` (`PascadiSpectralY`).
5. Fourier-side lattice discrepancy and `Ψ̂` decay (non-critical `F_AB` cells).
6. Divisor-in-progressions / rough-support counts (`CoprimalityPaid`, AA.1-shape cells).
7. V97 noncritical one/two-large (`REFEREE_PENDING` #2), entering only through 1 and the
   non-critical cells.

The source-level hypotheses `OrderingBPoissonReduction` and `SharpMembership` (with the
`PascadiRangeExport` constants) remain, together with the structural `SevenBlockTailFramework`.
Details are in `ERDOS287_MINIMAL_ANALYTIC_INTERFACE.md`.

## 10. Updated closure DAG (`SourceChain/ClosureDAG.lean`)

Nodes: 1 exact model (Exact), 2 finite bank (Banked), 3 W3 (Banked), 4 W2.984 (Banked),
5 seven-block consumer (Exact), 6 V99 centering (Exact), 7 RBDH algebra (Exact), 8 Ordering-B
source dictionary (KernelConditional), 9 auxiliary-error payment (KernelConditional),
10 `F_AB` (KernelConditional), 11 nonclean `F_AA` (KernelConditional), 12 clean `F_AA^♯`
(KernelConditional), 13 full scalar weight (Exact), 14 full range export (KernelConditional),
15 affine phase (Exact), 16 complete kernel source membership (RefereePending), 17 external
spectral estimate (ExternalAnalytic), 18 final remainder (KernelConditional), 19 conditional tail
(KernelConditional), 20 unconditional tail (**Open**), 21 effective onset (Open), 22 finite
splice (Open), 23 global #287 (Open). Also: Ordering A (Retired) and the metadata records
`V100R4_AuthorCandidate`, `IndependentTailAuditPending` (Metadata).

Kernel-checked by `decide`:

* `scDag_acyclic`: every edge strictly increases the rank.
* `scOrderingA_feeds_nothing`, `scOrderingA_no_path_to_tail`: retired Ordering A has no path
  to either tail.
* `scMetadata_feeds_nothing`, `scInert_feeds_nothing`: author/referee metadata instantiates no
  mathematical node.
* `scGlobal_preds`: global #287 has exactly the inputs effective onset and finite splice.
* `scTail_reaches_global`, `scSplice_reaches_global`: global #287 requires both the tail and the
  splice.
* `scConditionalTail_not_global_pred`: the conditional tail does not feed global #287 directly.
* `scSpectral_routing`: the spectral estimate feeds only the final remainder.
* `scExact_inputs_exact`: Exact nodes have only Exact/Banked inputs.
* `scTerminal_statuses`: the unconditional tail, onset, splice and global #287 are Open.

## 11. Trust audit (source chain)

* `#sc_assert_all_std_axioms` runs at build time over **every** theorem in
  `Erdos287.SourceChain` (481 constants after the actual-atom layer; 330 at the end of the
  source-chain stage). Each depends only on `propext`, `Classical.choice`
  and `Quot.sound`, so `sorryAx`, project axioms and `Lean.ofReduceBool` are excluded.
* `#ct_assert_std_axioms` prints the axioms of 69 principal theorems, including
  `Tail287_of_NarrowProviders`, `Tail287_of_MinimalAnalyticProviders`, `sharpPaid_of_spectralY`,
  `QuantitativeTH_of_spectralY`, `scalarWeight_eq_sectors`, `ph1_ePhase` and
  `zeroMode_covariance_full`.
* `#ct_assert_avoids`: `PascadiSpectralY`, `SharpMembership` and `PascadiRangeExport` mention
  none of `RSigmaP`, `Tail287Statement`, `Erdos287Counterexample`, `ExactWord`,
  `IsLittleOTarget` or `TailSourceFamily`. `OrderingBPoissonReduction`, `PiecePaid`,
  `CenteringPaid`, `CoprimalityPaid`, `SpectatorReciprocalNorm`, `PowerSavingCell` and
  `LogSavingCell` mention none of `RSigmaP`, `Tail287Statement`, counterexamples or exact words.
* `#ct_assert_mentions`: both new conditional tail theorems visibly carry all their inputs.
* `SourceChain/audit.sh` covers the token scan (`sorry`, `admit`, `axiom`, `unsafe`,
  `native_decide`, `bv_decide`, `implemented_by`, `opaque`, `extern`, `ofReduceBool`,
  `False.elim`, `instance`, `exact?`), no `…Unconditional` declaration or alias, protected files
  (including `CurrentTail/`) unchanged against the root commit, the narrow build,
  `leanchecker --fresh`, and 6 negative controls.

### 11.1 Checker results

* Full `lake build` (source-chain stage): **Build completed successfully (9036 jobs)**, 3682 s.
  After the actual-atom layer and the repairs: **Build completed successfully (9041 jobs)**,
  again with no `sorry` warnings.
  The log contains no `declaration uses 'sorry'`.
* `lake env leanchecker RequestProject.Erdos287.SourceChain.<M>` gives **exit 0**, about 20 s
  each, for every content module `M`: TypeIISplit, ZeroModeCovariance, PoissonRemainder,
  ScalarWeight, AffinePhase, FourierPoisson, CleanFAA, SpectralExponent, Separation,
  MinimalTail, PaymentCalculus, PieceDerivations, NarrowTail, ClosureDAG, ActualAtom, W4Route,
  CrossCoprime, ActualAtomW4Comparison, UpstreamRepairs.
* A single `leanchecker` run on the whole aggregate was stopped after about 50 min at about
  63 GB of memory. **`--fresh` was not completed** for the source chain in this session. The
  previous `--fresh` pass applies to `CurrentTail` only.
* `audit.sh` steps 1–3 pass. Negative controls 1–4 were rejected as expected (`sorryAx`,
  `Lean.ofReduceBool`, and two refuted DAG edges by `decide`). Controls 5–6 were interrupted
  by memory pressure from the concurrent checker and were not re-run.

## 12. Actual-atom → positive `W₄` layer and final-Astra-audit repairs

See `ERDOS287_ACTUAL_ATOM_W4_FORMAL_REPORT.md`. In summary:

* The canonical `CleanAtom`, the no-dilation phase, character separation mod `Af` with
  `T_H ≤ Af`, source → positive `W₄` (Cauchy + multiplicity), fixed-`A` domination, the
  Cauchy prefactor with regressions, and the audited Pascadi term `FC²+B₀CS²+FCHS` (with the
  old `FHS` rejected) are all kernel-proved.
* There are three separate narrow `W₄` providers. The packet exponents `391/256` (Astra) and
  `775/256` (V101) are kernel-proved, as is the conditional `Tail287_of_AtomProviders`.
* Repairs: `𝒟⁺(D)` support ⟹ `d < D`; V97 large-variable routing with the exact
  `TwoLargeEstimate`; pair coefficient `(200/59)(1+ε₀+τ)` with the safety margin `1/295`; the
  cross-coprime colouring identity together with its placement regression.
* Verdicts: actual-atom request **`ERDOS287 ACTUAL-ATOM INTERFACE BLOCKED`**; unconditional
  closure **`SUBSTANTIVE PROVIDER REMAINS`**. The blocker is physical-source construction,
  followed by `UpperSieveWellFactorable`, the seven-block framework and the deep analytic
  estimates.
