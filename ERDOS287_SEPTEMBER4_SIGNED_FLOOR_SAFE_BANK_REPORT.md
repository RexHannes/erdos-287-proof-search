# Erdős #287 — September-4 signed `B_src` floor safe bank

**Append-only run.**  No earlier theorem, certificate, status node or firewall was deleted,
rewritten, weakened, shadowed or reinterpreted.  **Erdős #287 is not claimed.**  No Maynard
theorem, no numerical Mertens theorem and no analytic estimate is asserted anywhere.

---

## 1. Files added

| File | Content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287September4PhysicalW.lean` | §1 the exact physical weight `W`, its support, endpoint/centre values, two-sided bounds, monotonicity, sup norm, total variation, `C_W = 4`, derivative |
| `RequestProject/CurrentProgramme/Erdos287September4CanonicalStateSign.lean` | §2 canonical-state sign invariance and one-prime threshold crossing |
| `RequestProject/CurrentProgramme/Erdos287September4T0T2DeepEvenCancellation.lean` | §3 the `r = 2u` reindexing, the exact `T⁰ − T²` decomposition, deep-even cancellation |
| `RequestProject/CurrentProgramme/Erdos287September4BsrcLocalMobiusCollapse.lean` | §4 local prime-factor identity, cube collapse, divisor-sum collapse, normalised `S₂` form, repair counterexample |
| `RequestProject/CurrentProgramme/Erdos287September4BoundaryDivisorLattice.lean` | §5 boundary datatype and record, interior consumption, interior-or-boundary, truncated-fibre firewall, exhaustiveness obligation |
| `RequestProject/CurrentProgramme/Erdos287September4SignedBsrcCompiler.lean` | §6 exact signed source `E_d`, test functions `V0,d`, `V2,d`, the derived factor `−4`, §7 secondary-pole interface and shoulder implication |
| `RequestProject/CurrentProgramme/Erdos287September4BoundaryCertificateChecker.lean` | §9 exact rational budget, §8 the certificate checker, §10 conditional compact-slab closure and the slab+tail join |
| `RequestProject/CurrentProgramme/Erdos287September4LargeLTailCompiler.lean` | §11 envelope monotonicity, kernel-proved endpoint decimal, tail compiler, §12 Mertens interface (uninhabited) |
| `RequestProject/Status/CurrentStatusErdos287September4SignedFloorBank.lean` | §14 status ledger, firewalls, row backings |
| `RequestProject/Status/AxiomAuditErdos287September4SignedFloorBank.lean` | §15 `#print axioms` on every principal declaration |
| `RequestProject/Main.lean` | now also imports the ten modules above (only additions) |

## 2. Principal theorems

**§1 Physical `W`** (`Erdos287.September4PhysicalW`)
`W_support_subset` (`support W ⊆ [7/10, 9/10]`), `W_support_subset_Ioo`, `W_seven_tenths`,
`W_nine_tenths`, `W_four_fifths` (`W(4/5) = 1`), `W_nonneg`, `W_le_one`,
`W_strictMonoOn_left` (increasing on `[7/10, 4/5]`), `W_symm`, `W_strictAntiOn_right`
(decreasing on `[4/5, 9/10]`), `W_isGreatest_one`, `W_sSup_range`, `W_iSup`,
`W_variation_left`, `W_variation_right`, `W_variation_Icc`, `W_variation_Iic`,
`W_variation_Ici`, `physicalW_variation` (`eVariationOn W univ = 2`),
`physicalW_CW_eq_four` (`C_W = 4`), `W_hasDerivAt` (`W' = −20 u v² e^{1−v}`).

**§2 Canonical state sign** `moebius_eq_neg_one_pow_omega`,
`canonicalStateSignInvariance45`, `canonicalStateSign_product`,
`thresholdCrossing_sign_flip`, `thresholdCrossing_sign_invariance`.

**§3 `T⁰ − T²`** `two_mul_dvd_iff_even`, `same_physical_n`, `kappa_reindex`,
`weight_reindex`, `Bsrc_even_collapse`, `evenPart_reindex`, `t0t2SourceDecomposition`,
`deepTerm_cancel`, `t0t2DeepEvenCancellation45`, `deepEven_is_not_complete_closure`.

**§4 Interior collapse** `localFactorIdentity`, `moebius_prod_primes`,
`cubeLocalMobiusCollapse`, `interiorLocalMobiusCollapse45`, `interiorCollapse_normalized`,
`interiorCollapse_S2_mu`, `interiorCollapse_S2_mu_of_prime`, `literal_S2_mu_form_fails`.

**§5 Boundary lattice** `BoundaryKind`, `SourceState`, `BoundaryRecord`, `Fibre`,
`IsInterior`, `fibreSum`, `interior_consumed`, `interior_or_boundary`,
`collapse_fails_on_truncated_fibre`, `boundary_cause_list_card`,
`PhysicalBoundaryCauseComplete`, `exhaustiveness_is_relative`.

**§6–§7 Signed compiler** `Ed`, `IntegralSupplyObligation`, `V0`, `V2`, `physicalWeight`,
`affineSigns`, `compareSign`, `factor_minus_four`, `signedContribution`, `R_signed`,
`signedBsrcSourceIdentity45`, `signedBsrcSourceIdentity45_expanded`, `SecondaryPoleInput`,
`poleShoulder`, `shoulder_of_residue_quarter`, `shoulder_of_secondaryPoleInput`.

**§8–§10 Checker and budget** `poleBudget`, `oscillatoryBudget`, `targetBudget`,
`budget_sum_lt_target`, `budget_values`, `signedFloor_budget_compiler`, `EventBox`,
`BoundaryCertificate`, `chainCovers`, `nonOverlapping`, `checkBox`, `checkCert`,
`chainCovers_sound`, `checker_coverage`, `BoundaryDominationInput`,
`list_contrib_le_total`, `boundaryCertificateChecker_sound`,
`CompactSlabSignedFloorBound`, `BoundaryCertificateValid`,
`boundaryCertificateValid_implies_compactSlab`, `slab_and_tail_join`,
`bankedCertificates`, `no_banked_certificate`, `structuralDemoCertificate`,
`structuralDemoCertificate_checks`, `structuralDemoCertificate_has_no_classes`.

**§11–§12 Tail** `envelope`, `envelope_hasDerivAt`, `envelope_deriv_neg`,
`envelope_strictAntiOn`, `exp_quarter_lower`, `exp_endpoint_lower`, `envelope_endpoint`,
`envelope_lt_of_ge`, `largeL_tail_envelope_bound`, `largeL_tail_compiler`,
`MertensEnvelopeInput`.

## 3. Exact source identities proved

1. `W(x) = exp(1 − 1/(1 − (10x−8)²))` on `|10x−8| < 1`, `0` elsewhere; `0 ≤ W ≤ 1`;
   `W(7/10) = W(9/10) = 0`; `W(4/5) = 1`; `sSup (range W) = 1`;
   `eVariationOn W univ = 2`; `C_W = 2·1 + 2 = 4`.
2. `κ_ε(d) = μ(d_low)·g_j = (−1)^{ω(d)} = μ(d)` for squarefree `d = d_low·d_high`,
   `ω(d_high) = j`, `g_j = (−1)^j`; and `κ_ε(d_low·p, j) = κ_ε(d_low, j+1)`.
3. `T⁰ − T² = Σ_{r odd} κ·Wt·B_src·1_{d ≤ Y(dr)} + Σ_{r even} κ·Wt·B_src·1_{d ≤ Y(dr) < 2d}`,
   with exact cancellation of every even `r` satisfying `2d ≤ Y(dr)`; the reindexing
   `r = 2u` keeps `n`, `κ`, `Wt`, and (under `B_src(2m) = B_src(m)`) `B_src`.
4. `Σ_{d ∣ q} μ(d) B_src(d) β(q/d) = ∏_{p ∣ q} (β_loc p − B_loc p)` for squarefree `q`;
   under `β_loc p − B_loc p = −S₂` this is `S₂^{ω(q)} μ(q)`.
5. `R_{B,signed} = −4 Σ_{d odd} (E_d[V0,d] − E_d[V2,d])`, the `−4` derived from
   `#{±1} · #{±1} · compareSign = 2·2·(−1)`.
6. `poleBudget + oscillatoryBudget = 14164610/10^15 + 985835/10^12 < 1/10^6`.
7. `9360 L(1+L)e^{−L/2}` strictly decreasing on `[4,∞)`; `envelope(62.5) < 10⁻⁶`.

### Repair found (§4)

The literally requested identity `Σ_{d∣q} μ(d) B_src(d) β(q/d) = S₂·μ(q)` is **false** for
`ω(q) ≥ 2`.  Counterexample (`literal_S2_mu_form_fails`, kernel-proved): `q = 15`,
`S₂ = 2`, `B_loc ≡ 0`, `β_loc ≡ −2`; the local normalisation `β_loc p − B_loc p = −S₂`
holds at both primes, and the divisor sum equals `4 = S₂²·μ(15)`, not `2 = S₂·μ(15)`.
The correct global form is `S₂^{ω(q)}·μ(q)` (`interiorCollapse_normalized`); the requested
shape holds exactly under the explicit extra hypothesis `S₂^{ω(q)} = S₂`
(`interiorCollapse_S2_mu`), in particular on a one-prime fibre
(`interiorCollapse_S2_mu_of_prime`).  Nothing was weakened: both forms are stated, and the
false one is recorded with its counterexample rather than silently repaired.

## 4. Conditional sockets (all uninhabited here)

* `September4SignedCompiler.SecondaryPoleInput` — the analytic residue `−1/4` (mathematical
  fields only: the family `F_d`, the rational residue, its limit characterisation; the
  desired floor conclusion is *not* a field).
* `September4Checker.BoundaryDominationInput` — the physical inputs the checker cannot
  decide: interior consumption inside each box, and domination of each listed class by its
  declared rational bound.
* `September4Checker.BoundaryCertificateValid` — checker verdict plus that domination input.
* `September4LargeLTail.MertensEnvelopeInput` — the explicit Mertens inequality.
* `September4SignedCompiler.IntegralSupplyObligation` — the analytic meaning of the supplied
  `∫V` (stated, never used or proved).
* `September4BoundaryLattice.PhysicalBoundaryCauseComplete` — physical exhaustiveness of the
  seven-cause list (stated, not proved).
* The September-3 AP analytic socket is untouched and remains uninhabited.

## 5. Boundary datatype

`BoundaryKind` (7 constructors, `Fintype`, `boundary_cause_list_card : card = 7`):
`gammaUpper`, `gammaDouble`, `twoHighShellLower`, `twoHighShellUpper`, `oneHighCollar`,
`repeatedHighTermination`, `canonicalThreshold`.
`SourceState` carries `dOdd`, `dSquarefree`, `highDepth`.
`BoundaryRecord` carries `q`, `d`, `kind`, `LLower`, `LUpper`, `coefficient`, `state`; the
omitted assignment is reconstructible from it (`rec.d.primeFactors = s`, proved inside
`interior_or_boundary`).

## 6. Checker design

Certificate = list of `EventBox`, each an exact rational `L`-interval plus a list of
`(BoundaryKind × ℚ)` entries (active class, directed upper bound), plus an explicit
`allowOverlap` flag.  Kernel-decided checks: box well-formedness, nonnegative bounds, per-box
total inside `poleBudget + oscillatoryBudget`, chain coverage of `[429/10, 125/2]`, and
non-overlap unless explicitly allowed.  Kernel-proved consequences: coverage soundness
(`chainCovers_sound`, `checker_coverage`) and the aggregate bound
(`boundaryCertificateChecker_sound`).  The generator is untrusted; its output is data only,
and every proposition the conclusion depends on is re-checked in Lean.

## 7. Actual numerical certificate data

**None.**  `bankedCertificates = []` (`no_banked_certificate`).  A single
`structuralDemoCertificate` exists solely to show the checker is not vacuous; it declares an
empty class list (`structuralDemoCertificate_has_no_classes`), carries no numerical boundary
information, and is deliberately not banked.

## 8. Exact rational budget arithmetic

```
poleBudget        = 14164610 / 10^15      ( = 1.4164610e-8, not rounded to 1.417e-8 )
oscillatoryBudget =   985835 / 10^12      ( = 9.85835e-7 )
poleBudget + oscillatoryBudget < 1 / 10^6            -- budget_sum_lt_target
|R0|/B < poleBudget ∧ |Rosc|/B < oscillatoryBudget ∧ |R| ≤ |R0| + |Rosc|
      →  |R|/B < 1e-6                                -- signedFloor_budget_compiler
```

## 9. Build

`lake build` succeeds; `RequestProject.Main` (which imports every new module) builds.

## 10. Axiom audit

`#print axioms` is run on all 92 principal new declarations in
`RequestProject/Status/AxiomAuditErdos287September4SignedFloorBank.lean`.  Every one reports
either “does not depend on any axioms” or a subset of
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, no `sorryAx`, no custom `axiom`, no
`unsafe`, no `native_decide`, no `implemented_by`, no `opaque`, no `skipKernelTC` occurs in
any new file.

## 11. Remaining open nodes

`boundaryExhaustiveness` (partial), `signedCompilerAnalyticLimit` (external),
`secondaryPoleAnalytic` (external), `boundaryNumericalCertificate` (not built),
`log42p9To62p5Floor` (conditional), `log62p5To3727Tail` (conditional as a floor claim; the
envelope itself is kernel-proved), `totBsrcSignedCanonicalFloorDirected45` (strictly
reduced), `mertensEnvelopeInput` (uninhabited), Maynard owner/constant/threshold (external /
not banked), numerical `E_T` (not banked), `E_T` and `E_L` (conditional open), global
effectivity (open), **Erdős #287 (open)**.

---

## Strict output

```
PHYSICAL W:                                   KERNEL-PROVED
W SUPPORT:                                    KERNEL-PROVED  (support W ⊆ [7/10, 9/10]; W(7/10)=W(9/10)=0, W(4/5)=1)
W SUP NORM:                                   KERNEL-PROVED  (IsGreatest (range W) 1; sSup = ⨆ = 1)
VAR(W):                                       KERNEL-PROVED  (Mathlib eVariationOn; = 2)
C_W=4:                                        KERNEL-PROVED
CANONICAL-STATE SIGN INVARIANCE:              KERNEL-PROVED
T0-T2 DEEP-EVEN CANCELLATION:                 KERNEL-PROVED
INTERIOR DIVISOR-LATTICE MÖBIUS COLLAPSE:     KERNEL-PROVED  (literal S₂·μ(q) form repaired to S₂^{ω(q)}·μ(q); counterexample banked)
BOUNDARY DATATYPE:                            BUILT
INTERIOR-OR-BOUNDARY EXHAUSTIVENESS:          PARTIAL  (dichotomy kernel-proved; physical cause-list completeness isolated as an obligation)
SIGNED B_src EXACT SOURCE:                    KERNEL-PROVED  (finite/truncated; analytic limit isolated)
SECONDARY POLE:                               EXTERNAL / NOT FORMALIZED  (shoulder implication KERNEL-PROVED)
EXACT POLE BUDGET:                            14164610 / 10^15
EXACT OSCILLATORY BUDGET:                     985835 / 10^12
BUDGET SUM < 1e-6:                            KERNEL-PROVED
BOUNDARY CERTIFICATE CHECKER:                 KERNEL-PROVED
ACTUAL BOUNDARY CERTIFICATE:                  NOT BUILT
LOG42P9-62P5:                                 CONDITIONAL
LOG62P5-3727:                                 KERNEL-PROVED envelope (monotonicity + endpoint); floor claim CONDITIONAL on envelope domination
TOT-BSRC-SIGNED-CANONICAL-FLOOR-DIRECTED45:   STRICTLY-REDUCED
MAYNARD ASSERTED:                             NO
MAYNARD SOCKET:                               UNINHABITED
NUMERICAL E_T:                                NOT BANKED
E_L:                                          OPEN / CONDITIONAL
GLOBAL EFFECTIVITY:                           OPEN
ERDOS287:                                     OPEN
LAKE BUILD:                                   PASS
SORRY / SORRYAX:                              NONE
NEW CUSTOM AXIOMS:                            NONE
OVERCLAIM AUDIT:                              PASS
FIRST EXACT REMAINING NODE:                   BOUNDARY NUMERICAL CERTIFICATE — no externally generated event-box data
                                              for 42.9 ≤ L ≤ 62.5 exists, and no inhabitant of
                                              BoundaryDominationInput has been supplied; until both are
                                              provided the compact-slab floor row stays CONDITIONAL.
STOP.
```
