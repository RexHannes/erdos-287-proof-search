# ERDŐS #287 EFFECTIVITY — GOLD BANK, LONG-FIBRE EXTENSION

Effectivity kernel bank only.  **Erdős #287 is NOT solved and NOT claimed.**

## FILES ADDED

* `RequestProject/Erdos287/CompletePeriodEndpoint.lean` (§24)
* `RequestProject/Erdos287/LambdaWeights.lean` (§25)
* `RequestProject/Erdos287/EdgeCutoffLedger.lean` (§26)
* `RequestProject/Erdos287/AggregateThreshold.lean` (§27)
* `RequestProject/Erdos287/AllQResummation.lean` (§28)
* `RequestProject/Erdos287/ChartEquivalence.lean` (§29)
* `RequestProject/Erdos287/CurrentStatusEffectivityLongFibre.lean` (§30)

## FILES MODIFIED

None.  All pre-existing modules (`BsrcWeights`, `AllComplement`, `OddHalfDivisor`,
`Reflection`, `MediumLedger`, `C1C2Splice`, `OddLineCancellation`, `RatioBoundary`,
`EulerLocal`, `TwoVariableZ`, `PerronAlgebra`, `IncrementalDirectedLedger`,
`CurrentStatusEffectivity`, …) are preserved byte-for-byte; the new status ledger is an
additional module that imports and extends `CurrentStatusEffectivity`.

## FULL `lake build`

**PASS** (8457 jobs, 0 errors).

## RESULT TABLE

| Item | Status |
|---|---|
| LAMBDA FINITE ALGEBRA | KERNEL-PROVED |
| EDGE REPLACEMENT SEMANTICS | KERNEL-PROVED |
| UPDATED SUBTOTAL (5.257263872e-7) | KERNEL-PROVED |
| UPDATED CAPACITY (3.603386128e-7) | KERNEL-PROVED |
| COMPLETE-PERIOD COVARIANCE | KERNEL-PROVED |
| COPRIME ENDPOINT ORTHOGONALITY | KERNEL-PROVED |
| REMAINING TARGET ARITHMETIC 69/5000 − 469/75000 = 283/37500 | KERNEL-PROVED |
| F/ED/DD/S TYPE | KERNEL-PROVED |
| ANALYTIC REMAINDER BOUND (C_rem < 283/37500) | OPEN |
| ALL-q RESUMMATION | KERNEL-PROVED (exact finite algebra) |
| CHART EQUIVALENCE | KERNEL-PROVED (source typing) |
| UNWEIGHTED PER-b C_joint ≤ 0.09 | RETIRED / FIREWALLED |
| MEDIUM-k | OPEN (strictly reduced) |
| TWO-HIGH | NOT ENTERED |
| SIGNED FLOOR | OPEN |
| MAYNARD | NOT ENTERED |
| ERDŐS #287 | OPEN |

## THEOREMS PROVED (new)

### §24 `CompletePeriodEndpoint.lean`

Definitions: `endpointPhi q c v = ((v+c) mod q)/q − (q−1)/(2q)`,
`endpointCovariance q1 q2 c = (1/lcm) Σ_{v mod lcm} φ_{q1}^{(c)}(v) φ_{q2}^{(c)}(v)`.

* `sum_range_cast`, `sum_range_cast_sq`, `mod_two_scale`, `sum_range_two_scale`,
  `sum_range_affine_perm`, `sum_range_mod_cast`, `sum_range_mod_mul_mod_aux`
* `sum_range_mod_mul_mod` — exact complete-period mixed second moment
* `sum_range_shift_one`, `sum_range_shift` — complete-period shift invariance
* `endpointPhi_sum_period` — mean zero over a period
* **`endpointCovariance_exact`** — `(1/L) Σ_{v mod L} φ_{q1}^{(c)} φ_{q2}^{(c)} = (g²−1)/(12 q1 q2)`
* `endpointCovariance_coprime_zero` — gcd = 1 ⟹ covariance 0
* `endpointCovariance_nonneg`, `endpointCovariance_pos_of_gcd_gt_one` — nonnegativity, and
  strict positivity exactly on the gcd > 1 strata
* `endpointCovariance_gcd_stratum` — dependence only on the gcd stratum and the product
* `endpointCovariance_lane_independent`, `endpointCovariance_odd`

The identity is proved by exact finite computation (two-scale range splitting, an affine
permutation of a complete residue system, Gauss sums).  No numerical testing is used.  It
holds for all positive moduli; oddness is recorded as a specialisation.

### §25 `LambdaWeights.lean`

`lambdaLocal p = (p−1)/(p−2)²`, `lambdaW b = ∏_{p ∣ b, p odd} lambdaLocal p`.

* `lambdaW_one`, `lambdaW_zero`, `lambdaW_prime`, `lambdaW_two_pow`, `lambdaW_fifteen`
* `lambdaW_mul` (coprime multiplicativity), `lambdaW_prod_primes` (finite prime-product)
* `lambdaLocal_pos`, `lambdaW_pos`, `lambdaW_ne_zero`
* `lambdaLocal_eq`, **`lambdaW_eq_B0_mul_beta`** — exact local Euler algebra `λ = B0 · β`
* `HlambdaFinite`, `HlambdaFinite_split`, `HlambdaFinite_pos` — finite exact product layer
* `HLambdaCertificate`, `Hlambda_conditional_bound` — analytic-tail hypothesis + conditional
* `Hlambda_not_asserted` — firewall: `H_λ(0) < 8/3` is **not** proved here

No infinite Euler product is asserted anywhere.

### §26 `EdgeCutoffLedger.lean`

* `certifiedSubtotalV1000 = 5257263872/10^16`, `remainingCapacityV1000 = 3603386128/10^16`
* **`ledger_difference_exact_v1000`** — `8.86065e-7 − 5.257263872e-7 = 3.603386128e-7`
* `remaining_capacity_v1000_gt`, `ledgerV1000_supersedes` (subtotal ↑, capacity ↓)
* `EdgeCutoffStatus` (previous cutoff 50, current cutoff 1000, both edge charges),
  `updatedSubtotal`, `doubleChargedSubtotal`, `v50ToV1000`
* `updatedSubtotal_eq` — replacement update law `old − oldEdge + newEdge`
* **`edge_double_charge_illegal`** — charging both is strictly larger; the two conventions
  agree only when the old edge charge is 0
* `edgeChargeV1000 = 722/10^12 = 7.22e-10`, `subtotal_update_v1000`,
  `certifiedSubtotalV1000_eq`
* `EdgeEstimateCertificate`, `edgeCertificate_v1000`, `edgeCertificate_not_proved`

The analytic correctness of the `V<1000` edge estimate is a **certificate object**, not an
axiom and not a theorem.

### §27 `AggregateThreshold.lean`

* `CAggTarget = 69/5000`, `CAggCritical = 1382165/10^8`, `CAggBound` (predicate only)
* `CAggTarget_lt_critical`, **`CAgg_below_critical_of_target`** (conditional),
  `CAggBound_not_proved` (firewall)
* `CEndPeriodUpper = 469/75000`, `CEndDiagUpper = 47/10000`, `CEndOffUpper = 17/10000`,
  `CRemTarget = 283/37500`
* **`aggregate_minus_endpoint`** — `69/5000 − 469/75000 = 283/37500`
* `endpoint_budget_positive`, `diag_off_not_period` (the diagonal + off-diagonal lines do not
  substitute for the period line: `47/10000 + 17/10000 > 469/75000`)
* `RemainderComponents` (F, ED, DD, S), `CRem = F + 2·ED + DD + S`, `CRem_eq`,
  `CRem_le_of_components`
* `RemainingCovarianceTargetMet` — **OPEN**, deliberately unproved;
  `remaining_target_not_proved` shows it is a genuine (non-tautological) goal
* `aggregate_closure_conditional` — arithmetic of the closure, conditional on both open inputs

### §28 `AllQResummation.lean`

`LongFibreQ b q = (q,b)=1 ∧ 31 < b·q`, `AgtDivisorSum b n = A_b^>(n)`,
`PgtPrefix b Y = P_b^>(Y)`.

* `B0_pos`, `B_ne_zero`
* **`allQ_divisor_identity`** — `Σ_{q ∣ n, (q,b)=1} β(q) = B(b n)/B(b)`
* `AgtDivisorSum_eq` — exact split into the long-fibre part and the finitely many small-`bq`
  terms
* **`allQ_resummation`** — `Σ_{n ≤ X} A_b^>(n) = Σ_{q ≤ X, …} β(q)·⌊X/q⌋`
* **`allQ_discrepancy_form`** — `= X·P_b^>(X) + Σ_{q ≤ X, …} β(q)(⌊X/q⌋ − X/q)`

Exact finite identities only; the smooth singular-series discrepancy estimate is OPEN.

### §29 `ChartEquivalence.lean`

* `LongFibreSourceId`, `ChartRepresentation`, `ChartCharge`, `ChartLegal`
* **`charts_same_source`**, `charts_distinct_representations`
* **`chart_double_charge_illegal`**, `chartLegal_single_chart`, `chartLegal_singleton`
* `EstimateId`, `BankStatus`, `RetirementReason`, `estimateStatus`, `retirementReason`,
  `bankedClosingEstimates`
* **`unweightedCjoint_retired`**, **`unweightedCjoint_not_banked`**,
  `bankedClosingEstimates_are_banked`, `retired_ne_banked`

### §30 `CurrentStatusEffectivityLongFibre.lean`

* `LongFibreNode`, `LongFibreStatus`, `longFibreStatus`, `longFibreOpenNodes`
* **`longFibre_open_frontier`** — no open node is recorded as proved / certified / conditional
* `erdos287_still_open`, `mediumK_reduced_not_closed`, `twoHigh_and_maynard_not_entered`,
  `v1000_edge_certified_input`, `longFibre_ledger_values`
* `#print axioms` for every new principal theorem

## PLACEHOLDER AUDIT

No `sorry`, `admit`, custom `axiom`, `unsafe`, `native_decide`, `implemented_by` or `opaque`
occurs in any new module.

## AXIOM AUDIT

Every new principal theorem depends only on the standard Lean/Mathlib foundations already
accepted by this project — `propext`, `Classical.choice`, `Quot.sound` — and several depend
on no axioms at all (`charts_same_source`, `chartLegal_single_chart`,
`bankedClosingEstimates_are_banked`, `longFibre_open_frontier`, `erdos287_still_open`).
The full printout is produced by `RequestProject/Erdos287/CurrentStatusEffectivityLongFibre.lean`
at build time.

## NOT BANKED (remain OPEN)

λ-weighted aggregate covariance bound; `C_agg ≤ 69/5000` as an achieved estimate;
finite-period remainder estimate; endpoint-derivative estimate; derivative-derivative
estimate; singular-series discrepancy theorem; medium-k closure; two-high closure;
signed-floor closure; Maynard; Erdős #287.
