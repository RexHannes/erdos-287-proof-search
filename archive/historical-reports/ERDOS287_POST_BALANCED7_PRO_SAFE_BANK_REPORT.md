# ERDŐS #287 — POST-BALANCED7 "PRO" SAFE BANK / CONDUCTOR-SPLIT & SMALL-PRIME-PREFIX PASS

Append-only continuation of `/workspace/request-project`.  No historical V15–V24 / SP-2 bank,
no historical status row, no historical report and no pass-1 module was modified.

Namespace deviation (same as the pass-1 report): the requested `TwinPrimeProject.*` namespace
does not exist in this repository.  The established convention `Erdos287.*` is used; this
pass lives in `Erdos287.PostBalanced7Pro` (Lean modules) and `Erdos287.PostBalanced7ProStatus`
(status ledger), all under the requested directory `RequestProject/CurrentProgramme/` and
`RequestProject/Status/`.

---

## 1. Files added

| File | Contents |
|---|---|
| `RequestProject/CurrentProgramme/SevenBoxPrimeWeights.lean` | §3 seven-box prime-supported weights `ω = 1_P(p)·V(p/Y)·p^{it}`, exact modulus, support |
| `RequestProject/CurrentProgramme/PrimeTupleMultiplicity.lean` | §4 exact labelled multiplicity `≤ k!` for prime tuples, `∑|a₃|² ≤ 6∏E`, `∑|b₄|² ≤ 24∏E`, complex-weight form |
| `RequestProject/CurrentProgramme/ConductorSplitLargeSieve.lean` | §5 character families as supplied data, literal `charSum`, exact conductor split, monotonicity, Möbius coprimality expansion, uninhabited all-character large-sieve socket |
| `RequestProject/CurrentProgramme/LowConductorSiegelWalfisz.lean` | §6 internal cutoff `(log X)^30`, cutoff firewall against `uCut = X^{1/3}`, uninhabited Siegel–Walfisz socket with explicit ineffectivity record, finite aggregation consumer |
| `RequestProject/CurrentProgramme/SmallQ34LSCompiler.lean` | §7 three-child `ε/3` bundle → `SmallQTargetBound`, and the proof that the residual really is the normalisation child |
| `RequestProject/CurrentProgramme/SmallPrimePrefix.lean` | §12–§15 `z₀ = X^{1/420}`, smooth/rough factorisation (existence **and** uniqueness), `Ω(d) ≥ 3` firewall, truncated-Möbius non-factorisation, literal residual sum, uninhabited Type-II socket |
| `RequestProject/CurrentProgramme/PostRepairOwnerCompiler.lean` | §10 refined owner map (`hardShortT`, `threeSmallPrimePrefix`), unique ownership, no double spending, conditional compiler |
| `RequestProject/CurrentProgramme/UniformFragmentationCompiler.lean` | §16 K0 uniform fragmentation reassembly compiler (`REDUCED / CONDITIONAL`, never activated) |
| `RequestProject/Status/CurrentStatusErdos287PostBalanced7Pro.lean` | §11 new append-only status ledger + integrity theorems |
| `RequestProject/Status/AxiomAuditErdos287PostBalanced7Pro.lean` | §19 `#print axioms` audit of every principal declaration of this pass |
| `RequestProject/Main.lean` | import lines only (inside the import block) |
| `ERDOS287_POST_BALANCED7_PRO_SAFE_BANK_REPORT.md` | this report |

---

## 2. Principal theorems proved (all kernel-checked, no `sorry`)

**§3–§4 seven-box weights and multiplicity**
`norm_omegaBox_eq_V`, `norm_omegaBox_le_one`, `omegaBox_support_is_primes`,
`prime_tuple_perm`, `card_prodFiber_le_factorial`, `representationMultiplicity_le_factorial`,
`representationMultiplicity3_le_six`, `representationMultiplicity4_le_twentyfour`,
`a3_sq_sum_le_six`, `b4_sq_sum_le_twentyfour`, `convWeightC_sq_sum_le`,
`seven_box_energy_bound`.

**§5 conductor split**
`condSum_nonneg`, `highCondSum_nonneg`, `fullCondSum_nonneg`, `condSum_add_highCondSum`
(exact split, no double counting), `condSplit_disjoint`, `condSum_le_fullCondSum`,
`condSum_mono`, `charSum_zero_coeff`, `fullCondSum_eq_zero_of_zero_coeff`,
`sum_moebius_divisors`, `coprime_indicator_eq`, `gcd_divisors_nonempty`,
`conductorLargeSieve_full_bound` (conditional), `conductorLargeSieve_not_automatic`.

**§6 tiny modulus**
`lowConductorCutoff_nonneg`, `lowConductorCutoff_mono`, `lowConductorCutoff_ne_uCut`,
`lowConductorCutoff_ne_uCut_fun`, `lowConductor_aggregate_bound` (conditional),
`lowConductorSiegelWalfisz_not_automatic`, `lowConductor_effectivity_firewall`.

**§7 SmallQ compiler**
`smallQ34LS_compiler`, `smallQ34LS_compiler_pointwise`, `smallQ34LSInputs_not_automatic`,
`smallQ34LS_residual_is_normalisation`.

**§12–§15 small-prime prefix**
`zZero_pos`, `zZero_pow`, `smoothPart_ne_zero`, `roughPart_ne_zero`,
`smoothPart_mul_roughPart`, `smoothPart_smooth`, `roughPart_rough`, `smoothPart_dvd`,
`coprime_smooth_rough`, `smoothRough_unique`, `prefix_dichotomy`,
`smoothPrefix_three_firewall`, `truncMoebius_two_two`, `truncMoebius_two_three`,
`truncMoebius_not_prefix_factorisable`, `rGeThreePrefix_zero_weight`, `rGeThreePrefix_split`,
`threeSmallPrimePrefix_not_automatic`.

**§10 post-repair owner map**
`postRepairOwnerMap_is_the_mandated_one`, `postRepairOwner_exists_unique`,
`postRepairOwner_is_a_refinement`, `postRepair_no_double_spending`,
`postRepair_accounts_disjoint`, `postRepair_smallQ_account`,
`postRepair_threePrefix_account`, `balancedSeven_postRepair_compiler`,
`postRepairInputs_not_inhabited_here`,
`postRepair_compiler_does_not_prove_balancedSeven`.

**§16 K0 fragmentation**
`k0_uniform_fragmentation_compiler`, `k0FragmentationInputs_not_inhabited_here`,
`k0_residual_is_three_prefix`, `k0_not_activated`.

**§11 status ledger**
`no_closed_rows`, `erdos287_open`, `balanced7_open`, `k0_is_reduced_not_closed`,
`first_downstream_residual_is_three_smallprime_prefix`,
`first_residual_is_smallq_34LS_normalisation`, `effectivity_firewall`, `ledger_is_honest`,
`downstream_not_activated`.

---

## 3. Uninhabited interfaces (never constructed)

* `BalancedSevenAllCharacterConductorLargeSieveInput` — all-character conductor-split large
  sieve (research estimate `≪ log^{16} X · (Q + N/D) · Σ|c|²`).
* `BalancedSevenLowConductorSiegelWalfiszInput` — classical Siegel–Walfisz, uniform in the
  affine shift, with an explicit `explicitThreshold = none` ineffectivity record.
* `ThreeSmallPrimePrefixTypeIIInput` — the `Ω(d) ≥ 3` small-prime-prefix Type-II estimate.
* `BalancedSevenSmallQ34LSInputs`, `BalancedSevenPostRepairInputs`,
  `K0UniformFragmentationInputs` — conditional bundles.

Each has an accompanying refutation theorem exhibiting explicit data that fail it, so none is
inhabited by `Classical.choice` or an artificial constructor.

---

## FINAL BLOCK

```
SMALLQ 34LS:
    RESEARCH CLOSURE CANDIDATE / FORMAL CONDITIONAL COMPILER ONLY
    first exact residual = AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45 (sourceOpen)

CONDUCTOR SPLIT:
    LEAN_PROVED exact finite algebra (cover / disjoint / monotone / reassembly)
    analytic large-sieve estimate: EXTERNAL / UNINHABITED

TINY MODULUS (SIEGEL-WALFISZ):
    ANALYTIC OPEN / UNINHABITED / EXPLICITLY INEFFECTIVE
    internal cutoff (log X)^30 proved distinct from physical uCut = X^{1/3}

SMALLR OWNER SUBTRACTION:
    LEAN_PROVED ALGEBRAIC/FINITE COMPILER (pass 1, unchanged)

HARD delta:
    1/21   (pass-1 rational/order ledger, unchanged; short-t analytic theorem external)

SMALL-PRIME PREFIX:
    z0 = X^(1/420)
    smooth/rough factorisation: EXISTENCE + UNIQUENESS LEAN_PROVED
    Omega(d) >= 3 firewall: LEAN_PROVED
    truncated Moebius does NOT factor through the prefix: LEAN_PROVED

FULL-q OWNER:
    LEAN_PROVED unique ownership / no double spending
    (6 owners, 9 cells; refinement of the pass-1 5-owner / 7-cell map)

BALANCED7:
    OPEN — NOT LEAN-PROVED
    latest research/paper closure candidate is metadata only,
    not independently re-audited

EFFECTIVE BALANCED7:
    OPEN (287-EFFECTIVE-POLYLOG-MODULUS-REPLACEMENT45: analyticOpen)

K0 UNIFORM FRAGMENTATION:
    REDUCED / CONDITIONAL — NOT ACTIVATED

FIRST EXACT DOWNSTREAM RESIDUAL:
    287-K0-SP2-THREE-SMALLPRIME-PREFIX-TYPEII45  (analyticOpen)

FCL:
    OPEN

ERDOS287:
    OPEN

LAKE BUILD:
    SUCCESS — full `lake build`, 8213 jobs, 0 errors.
    Pre-existing unrelated linter warning in
    RequestProject/Erdos287/FixedCertificateSmoothParity.lean:60 (unused simp argument),
    not introduced by this pass and not modified.

TRUST SCAN:
    ZERO occurrences of sorry / admit / axiom / opaque / unsafe / native_decide /
    @[implemented_by] in all new files.
    #print axioms on every principal declaration of this pass:
    only [propext, Classical.choice, Quot.sound].
```

## FINAL FIREWALL

```
Research audit metadata is not Lean proof.
The conductor-split 3+4 route is banked only as exact finite algebra plus an
uninhabited source socket; the analytic large sieve is not proved.
The remaining SmallQ obligation is coefficient/source normalization,
not exponent capacity.
The tiny-modulus child is explicitly ineffective and cannot discharge the
effective-modulus row.
The Omega(d) >= 3 small-prime-prefix Type-II estimate is the first exact
downstream residual; the K0 uniform fragmentation reassembly is REDUCED and
NOT activated.
Balanced7 remains OPEN until exact owner reassembly and a fresh hostile
audit pass.
Erdős #287 remains OPEN.
```
