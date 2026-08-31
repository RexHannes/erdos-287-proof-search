# ERDŐS 287 — COMMON-x / FRACTIONAL-LINEAR C0 SAFE BANK REPORT

Append-only delta, added **strictly after** `ERDOS287_HYBRID2_CRITICALRECT_SAFE_BANK`.
No previously banked module was edited; no previously proved theorem was weakened, replaced or
re-stated; no historical status module was deleted.

## FILES ADDED

* `RequestProject/CurrentProgramme/Erdos287CommonXArithmetic.lean` — §2 common-x conductor
  arithmetic, §3 centered `kappa` CRT arithmetic.
* `RequestProject/CurrentProgramme/Erdos287FractionalLinearC0.lean` — §5 opposite-row
  linearisation and uniqueness, §6 fractional-linear representation of `kappa`, §11 local
  change of variables.
* `RequestProject/CurrentProgramme/Erdos287CommonXCollisionFirewall.lean` — §4 centered
  graph-diagonal firewall, §7 common-divisor collision cancellation, §8 x-row separation
  witness.
* `RequestProject/Status/CurrentStatusErdos287CommonXFrontier.lean` — §8–§12 status layer and
  the new analytic-frontier ledger `Erdos287.CommonXFrontierStatus`.
* `RequestProject/Status/AxiomAuditErdos287CommonX.lean` — `#print axioms` for every new
  declaration.
* `ERDOS287_COMMONX_FRACTIONALLINEAR_SAFE_BANK_REPORT.md` — this report.

## FILES MODIFIED

* `RequestProject/Main.lean` — **five new `import` lines appended only**.  Nothing else in the
  repository was touched.  No import path of an existing module changed.

## UNCONDITIONAL THEOREMS

All of the following are kernel-checked with no analytic hypothesis and no source pin.

### §2 `Erdos287.CommonX` — common-x conductor arithmetic (`Q₁ = a₁x`, `Q₂ = a₂x`)

| name | statement |
|---|---|
| `commonX_gcd` | `gcd (a₁x) (a₂x) = x * gcd a₁ a₂` |
| `commonX_mul` | `(a₁x)(a₂x) = a₁a₂x²` |
| `commonX_lcm` | `lcm (a₁x) (a₂x) = x * lcm a₁ a₂` |
| `commonX_gcd_coprime` | `(a₁,a₂)=1 → gcd (a₁x) (a₂x) = x` |
| `commonX_lcm_coprime` | `(a₁,a₂)=1 → lcm (a₁x) (a₂x) = a₁a₂x` |
| `commonX_dvd_left` | `x·gcd a₁ a₂ ∣ a₁x` |
| `commonX_dvd_right` | `x·gcd a₁ a₂ ∣ a₂x` |
| `commonX_dvd_gcd` | `x ∣ gcd Q₁ Q₂` |
| `commonX_gcd_mul_lcm` | `gcd Q₁ Q₂ · lcm Q₁ Q₂ = a₁a₂x²` |

These are the exact `Nat` formulations supported by Mathlib.  **No asymptotic or range claim is
encoded.**

### §3 `Erdos287.CommonX` — centered `kappa` CRT arithmetic (in `ℤ`, congruences as literal divisibilities)

| name | statement |
|---|---|
| `kappa_crt_exists` | `IsCoprime d qLong → ∃ kappa, d ∣ kappa−1 ∧ qLong ∣ kappa−r` |
| `kappa_mod_small` | `d ∣ kappa−1 → kappa % d = 1 % d` |
| `kappa_mod_long` | `qLong ∣ kappa−r`, `qLong ∣ r(1−dη)−1` → `qLong ∣ kappa(1−dη)−1` |
| `kappa_unit_long` | `qLong ∣ kappa(1−dη)−1 → IsCoprime kappa qLong` |
| `kappa_sub_one_coprime_long` | `IsCoprime d qLong`, `IsCoprime η qLong`, `qLong ∣ kappa(1−dη)−1` → `IsCoprime (kappa−1) qLong` |
| `kappa_sub_one_gcd_long_eq_one` | same, in the form `gcd (kappa−1) qLong = 1` |
| `gcd_kappa_sub_one_fullConductor` | `Q = d·qLong`, `kappa−1 = d·s`, `IsCoprime s qLong` → `gcd (kappa−1) Q = \|d\|` |
| `gcd_kappa_sub_one_fullConductor_of_crt` | both gcd rows at once; here `IsCoprime s qLong` is *derived*, not assumed |

The second gcd equality is **not** overstated: its literal hypotheses (`d ∣ kappa−1` exhibited by
the cofactor `s`, and `IsCoprime s qLong`) are visible in the statement.

### §4 `Erdos287.CommonX` — centered graph-diagonal firewall

| name | statement |
|---|---|
| `graph_diagonal_forces_full_gcd` | `IsCoprime b Q`, `Q ∣ (kappa−1)b` → `Q ∣ kappa−1` |
| `gcd_eq_natAbs_of_dvd` | `Q ∣ a → gcd a Q = \|Q\|` |
| `graph_literal_diagonal_impossible` | `IsCoprime b Q`, `gcd (kappa−1) Q = d`, `d < \|Q\|`, `N = b`, `Q ∣ N − kappa·b` → `False` |
| `graph_diagonal_impossible_of_centered` | packaged form using `CenteredKappa` |

`CenteredKappa kappa b Q d := 1 < Q ∧ IsCoprime b Q ∧ gcd (kappa−1) Q = d ∧ d < |Q|`
(a definition, not a claim).

### §5–§6 `Erdos287.FractionalLinear` — opposite-row algebra

| name | statement |
|---|---|
| `fractionalLinear_to_linear` | `(A0 − dC0h')h = C0h'b`, `N = b + dh` → `dC0Nh' = A0(N−b)` (any `CommRing`) |
| `oppositeRow_linearized` | the same, bracketed as a linear equation in `h'` |
| `oppositeRow_unique_residue` | `IsUnit (dC0N)` → `h' = A0(N−b)·(dC0N)⁻¹` |
| `oppositeRow_unique_residue_of_source` | composition of the two |
| `oppositeRow_unique_residue_zmod` | the `ZMod x` instance |
| `kappa_fractionalLinear_of_source` | `IsUnit b`, `IsUnit (A0−dC0h')`, source relation, `kappa·b = b + dh` → `kappa = A0·(A0−dC0h')⁻¹` |
| `kappa_fractionalLinear_of_source_zmod` | the `ZMod x` instance |
| `denominator_ne_zero_of_unit` | `IsUnit y → y ≠ 0` |

Cancellation by `b` genuinely needs `IsUnit b`; that hypothesis is exposed explicitly, as
requested.  The analytic origin of `A0`, `C0`, `N` is **not** part of any hypothesis, so these
statements are reusable pure algebra.

### §7 `Erdos287.CommonX` — common-divisor collision firewall

| name | statement |
|---|---|
| `commonDivisor_residue_compatible` | `g ∣ x`, `g ∣ x'`, `g ∣ k₁−k₂` → `g ∣ k₁b − k₂b` |
| `commonDivisor_residue_cancel_unit` | `IsCoprime b g`, `g ∣ k₁b − k₂b` → `g ∣ k₁−k₂` |
| `commonDivisor_residue_iff_unit` | the equivalence under `IsCoprime b g` |

**No multiplicity bound for these collisions is formalised** — none is proved.

### §8 x-row separation (mathematical content, not bookkeeping)

| name | statement |
|---|---|
| `centered_kappa_satisfiable` | `CenteredKappa 3 1 6 2` |
| `xRowDiagonal_not_excluded` | a configuration where the centered conditions hold (so `N = b` is impossible) **and** `x₁ = x₂` |

So `graph diagonal impossible ⇏ x-row diagonal impossible`, and the ledger cannot encode that
implication by accident.

### §11 local change of variables `h' ↦ y = A0 − c·h'` (`c` = `dC0`)

| name | statement |
|---|---|
| `affine_leftInverse`, `affine_rightInverse` | the explicit two-sided inverse `y ↦ (A0−y)c⁻¹` |
| `affine_bijective` | `IsUnit c → Bijective (h' ↦ A0 − c h')` |
| `affine_pole_iff` | `A0 − c h' = 0 ↔ h' = A0c⁻¹` (the unique pole) |
| `sum_affine_reindex` | `∑_{h'} f(A0 − c h') = ∑_y f(y)` on a finite ring |
| `sum_affine_reindex_nonzero` | pole-deleted version: `∑_{h' : A0−ch' ≠ 0} f(A0−ch') = ∑_{y ≠ 0} f(y)`; over `ZMod p` with `p` prime the right-hand index set is exactly `(ZMod p)ˣ` |

This is the finite-sum identity that puts the fractional-linear phase into **Kloosterman shape**.
The Weil bound is **not** formalised and is not used: the Kloosterman identification is recorded
here in the report and as a `notFormalised` ledger row, never as an admitted theorem.

## CONDITIONAL / STATUS-ONLY DECLARATIONS

Namespace `Erdos287.CommonXFrontierStatus` (a ledger; the labels are deliberately distinct from
`provedUnconditional`):

`CommonXNode`, `CommonXLabel`, `stage`, `commonXLedger`, `DiagonalKind`, `DiagonalStatus`,
`diagonalLedger`, and the ledger theorems

`omegaNormalization_is_formal_first_residual`,
`doubleTypeII_is_research_first_analytic_residual`,
`c0_transverse_bdiagonal_all_reduced_open`, `erdos287_open`, `transverse_status_rows`,
`bdiagonal_status_rows`, `typeI_typeII_rows_are_ledger_records`,
`typeI_closure_does_not_close_c0`,
`commonX_arithmetic_pass_does_not_imply_c0_closure`,
`fractionalLinear_pass_does_not_imply_kloosterman_estimate`,
`local_kloosterman_arithmetic_does_not_imply_spectral_closure`, `no_false_promotions`,
`diagonal_ledger_rows`, `status_does_not_encode_xRow_exclusion`,
`graphDiagonal_row_is_backed_by_a_theorem`, `xRowDiagonal_row_is_backed_by_a_witness`,
`hybrid2_ledger_still_preserved`, `caseB_ledger_still_preserved`.

Ledger content:

```
FORMAL FIRST SOURCE RESIDUAL   : SharedGcdOmegaHNormalizationSourcePin        (sourcePin)
RESEARCH FIRST ANALYTIC RESIDUAL:
        CommonXFractionalLinearDoubleTypeIIKloosterman45                      (analyticOpen)
C0                             : researchStrictlyReducedOpen
TRANSVERSE                     : researchStrictlyReducedOpen
b-DIAGONAL                     : researchStrictlyReducedOpen
ERDOS287                       : OPEN
```

Type-I / Type-II dependency firewall (§9): `commonXTypeIResearchClosed` carries the label
`ledgerRecordResearchClosed` and `commonXTypeIIAnalyticOpen` carries `ledgerRecordAnalyticOpen`.
Both are **ledger records of the research record, not proofs of any analytic inequality**; the
theorem `typeI_typeII_rows_are_ledger_records` proves that neither is `provedUnconditional`, and
`typeI_closure_does_not_close_c0` proves the Type-I record does not close C0.

The three demanded non-implications are proved as ledger theorems:

```
common-x arithmetic PASS              ⇏  C0 closure
fractional-linear linearisation PASS  ⇏  Double-Type-II Kloosterman estimate
local Weil/Kloosterman arithmetic     ⇏  level-averaged spectral closure
```

§12 status rows (no new analytic proof, existing b-diagonal algebra untouched):

```
TRANSVERSE : signless-carrier dominated, analytically open;
             E = e/a₁ path touches the Ω_H source pin      (row: sourcePin)
             R = r₂/c₂ path analytically open              (row: ledgerRecordAnalyticOpen)
b-DIAGONAL : analytic/compiler open; exponent margins not formally instantiated because the
             numerical vertex dictionary is absent          (row: notFormalised)
```

## NOT FORMALISED

* Double-Type-II Kloosterman saving;
* level-averaged Kuznetsov estimate / level-averaged spectral closure;
* Weil bound for Kloosterman sums;
* transverse analytic closure;
* b-diagonal analytic closure and its numerical vertex dictionary;
* Ω_H source normalization.

None of these is admitted, assumed as an axiom, or encoded as a Lean theorem.

## AXIOM AUDIT

`#print axioms` was run on all 58 new principal declarations
(`RequestProject/Status/AxiomAuditErdos287CommonX.lean`).  Every one depends only on a subset of

```
propext, Classical.choice, Quot.sound
```

and several depend on no axioms at all (e.g. `denominator_ne_zero_of_unit` and most ledger rows).
No new custom axiom was introduced anywhere.

## UNSAFE TOKEN AUDIT

Textual scan of the five new Lean files for `sorry`, `axiom`, `unsafe`, `native_decide`,
`opaque`, `implemented_by`: **no occurrence as a code construct**.  The only textual hit is the
docstring sentence in the audit module that lists the forbidden tokens.  Decidable ledger facts
are discharged with `decide +kernel`.

## FULL BUILD

`lake build` on the default repository target: **PASS** — 8284 jobs, **0 errors**.
No pre-existing module was edited to make the build pass; no import path changed.

## FORMAL FIRST RESIDUAL

`SharedGcdOmegaHNormalizationSourcePin`

## RESEARCH FIRST ANALYTIC RESIDUAL

`CommonXFractionalLinearDoubleTypeIIKloosterman45`

## ERDOS287

`OPEN`

STOP.
