# ERDŐS #287 — BALANCED7 COMPARISON / AGGREGATE EULER SAFE BANK (V23)

Append-only continuation of the existing repository.  **V20, V21, V22 and SP-2 are
preserved unchanged**; `ARISTOTLE_SUMMARY.md` was not touched.  The next consistent version
identifier after the existing `V15 … V22` plus `SP-2` layers is **V23**, and that is the
label used throughout (Lean namespaces `Erdos287.V23*`, status module
`RequestProject/Status/Erdos287V23Status.lean`).

---

## A.  Inputs and the controlling audit

Three inputs were named: the current SP-2 safe bank, the Pro comparison-closure candidate,
and the subsequent independent audit.  The audit controls wherever they conflict.

```
OPUS NANC:  CASE F — SOURCE-MISSING.
```

Independently verified (and therefore banked as exact Lean algebra):

```
mu*log / log-r identity        : PASS
affine character q-cell        : PASS
1/zeta(1+w) = w + O(w^2)       : PASS   (recorded; not re-derived here)
basic nonunit routing          : PASS
```

**Not** independently verified (and therefore banked only as uninhabited interfaces):

```
literal SP-2 one-sign source
uniform H_P(w) contour estimate
dyadic-q / full-q exhaustiveness
independent physical 2B(P)
small-conductor physical source
exceptional source
no-double-spending
```

Because the verdict is CASE F, **nothing is recorded as research-closed on the strength of
the Pro run**: the Pro candidate and the independent audit are two *separate* status
fields, proved distinct in Lean (`statuses_are_not_conflated`).

---

## B.  Files added

Lean modules under `RequestProject/Erdos287/`:

| File | Content |
|---|---|
| `OldLocalScalarRetraction3221.lean` | the historical `2q/φ(q)` dictionary, and its refutation |
| `SP2PhysicalComparison3221.lean` | the literal one-sign physical comparison object |
| `MuLogQCell3221.lean` | `Λ = μ ∗ log` in `q`-cell form, `a_s(q)`, non-unit routing, character orthogonality |
| `PrincipalQCell3221.lean` | `M_phys_principal`, `M_fac_principal`, their equality, noncircularity firewall |
| `AggregateEulerLocal3221.lean` | the `w = 0` Euler local-factor algebra and `H_P(0) = 2B(P)` |
| `QPacketPartition3221.lean` | the dyadic `q`-packet ownership compiler |
| `SmallConductorExceptional3221.lean` | small-conductor and exceptional interfaces, effectivity firewall |
| `BalancedSevenComparisonCompiler3221.lean` | sign bookkeeping and the two conditional compilers |

Status modules under `RequestProject/Status/`:

* `Erdos287V23Status.lean`
* `AxiomAuditErdos287V23.lean`

Report: this file.

**File modified:** `RequestProject/Main.lean` — ten import lines appended, nothing else.

---

## C.  What is proved (exact / kernel-checked)

### C.1  Retraction of the old pointwise local scalar

* `oldPointwiseLocalScalar q = 2q/φ(q)`, with `= 3` at `q = 3` and `= 5/2` at `q = 5`;
* `old_pointwise_local_scalar_not_constant`;
* `oldPointwiseLocalScalarDictionary_refuted` — the historical claim "the aggregate constant
  is realised cell-by-cell as `2q/φ(q)`" is false **for every** value of that constant.
  This is the exact sense of *wrong geometry*: the aggregate limit `2B(P)` does not depend
  on `q`, the pointwise scalar does.
* `oldScalar_fixed_modulus_is_fine` — the surviving use of the shape `q/φ(q)` as a
  *single-modulus sieve density* (in `ShortShiftSieve3221`, `ShiuDivisorAverage3221`) is
  untouched.

Historical files are **not deleted**.

### C.2  The direct SP-2 physical comparison object

`SP2BalancedSevenPhysicalComparison C s` is literally

```
    −20 · ∑_{pvec ∈ cell} Ω(pvec) · [ Λ(2P + s) − 2B(P) ],     P = ∏_i pvec_i,
```

with `Λ` Mathlib's `ArithmeticFunction.vonMangoldt` and `2P + s` the V14 sign-firewalled
`affineNat s 1 P`.  The coefficient is tied back to the SP-2 depth sum
(`sp2AlternatingCoefficient_eq_depthSum`, from the banked `∑_{j≤3}(−1)^j C(7,j) = −20`).
Proved: `sp2PhysicalComparison_arg`, `_split`, `_eq_zero_of_pointwise_match`, `_bound`
(`|comparison| ≤ 20 ε ∑|Ω|`), `_not_automatically_zero`, `_congr`, `_sensitive_to_B`.

The object is defined **only** from the physical data (cell, `Ω`, `B`); it is not defined
from the factorial `q`-cell, and the two definitions remain independent.

### C.3  `μ · log` `q`-cell algebra

* `muLog_qCell_identity` — reused, not re-postulated, from the repository's existing
  `AffineMuLogIdentity` bank (itself derived from Mathlib's
  `moebius_mul_log_eq_vonMangoldt`);
* `muLog_affine_qCell` — the affine specialisation at `N = 2P + s`;
* `aCoeff s q = −s · 2⁻¹ (mod q)`, `aCoeff_spec` (`q ∣ 2P+s ↔ P ≡ a_s(q)`, odd `q`),
  `aCoeff_isUnit`;
* `qCell_nonunit_impossible` — even moduli carry no affine cell at all;
* `qCell_orthogonality`, `qCell_indicator`, `affine_qCell_indicator` — the finite
  character-orthogonality `q`-cell, available from Mathlib's
  `DirichletCharacter.sum_char_inv_mul_char_eq`, so **no external interface was needed**
  for this step.

### C.4  Principal `q`-cell

`M_phys_principal` (physical: mass on the single admissible unit-sector class) and
`M_fac_principal` (factorial route: the bare principal coefficient) are defined separately;
`principal_qCell_eq_physical_qCell` proves them equal for odd `q`, and
`affine_qCell_unique_class` proves the supporting class is unique.

### C.5  Aggregate Euler local algebra at `w = 0`

```
    off P :  (1 − 1/(p−1))/(1 − 1/p) = p(p−2)/(p−1)²        aggregateEuler_localFactor_offP
    on  P :             1/(1 − 1/p) = p/(p−1)               aggregateEuler_localFactor_onP
    ratio :        (on p)/(off p)   = (p−1)/(p−2)           aggregateEuler_localRatio
    H_P(0) = 2·S₂·∏_{p∣P,p>2}(p−1)/(p−2) = 2·B(P)           aggregateEuler_H0_eq_twoB
```

`S₂` is carried as a **parameter** (an infinite Euler product is not formalised), and `B(P)`
is defined from it by the displayed finite product.  The analytic passage
`F_P(w) = H_P(w)/ζ(1+w)` is *not* asserted.

### C.6  Dyadic `q`-packet ownership

`qPacketOwner q = ⌊log₂ q⌋`, packets `[2^k, 2^{k+1})`; proved: membership, uniqueness of the
owner, pairwise disjointness, the exact cover of `[1, 2^K)`, and the exact reassembly
`∑_{k<K} ∑_{q ∈ packet k} M q = ∑_{q ∈ [1,2^K)} M q`.  `qPacket_reassembly_needs_all_packets`
records that a proper sub-range does **not** reassemble the total.

### C.7  Effectivity firewall

`BalancedSevenStatusRecord` separates `asymptoticClosed` from `effectiveClosed`;
`asymptoticBalancedSeven_not_effectiveAutomatically` proves that a well-formed record whose
exceptional-character treatment is ineffective is **not** effectively closed, and
`ineffective_supplies_no_threshold` proves it supplies **no** explicit `M₀`.

### C.8  Sign bookkeeping and the conditional compilers

* `twoSign_total` : one sign `= 2B`, both signs `= 4B`; `oneSign_is_not_twoSign` shows the
  second sign is a genuinely separate supply.
* `comparison_pointwise_of_inputs`, `comparison_bound_of_inputs`,
  `balancedSevenComparison_of_inputs` — the comparison compiler, concluding the
  repository's own comparison object `MuLogComparisonAtCutoff` at the shared cutoff with
  `hard = −20 ∑ Ω Λ(2P+s)`, `model = −40 ∑ Ω B(P)`, `err = 20 · budget · ∑|Ω|`.
* `balancedSevenAsymptotic_of_closure_and_comparison` — SP-2 analytic closure plus
  comparison closure gives the Balanced7 packet input (asymptotic branch only).

**No inhabitant of any input package is constructed.**

---

## D.  Interfaces created and left uninhabited

| Interface | Status |
|---|---|
| `SP2PhysicalTwoBIndependent287Input` | EXTERNAL / SOURCE-MISSING / UNINHABITED |
| `AggregateEulerPrincipal287Input` | EXTERNAL / UNINHABITED |
| `AggregateEulerUniformity287Input` | EXTERNAL / SOURCE-MISSING / UNINHABITED |
| `BalancedSevenQPartitionInput` | EXTERNAL / SOURCE-MISSING / UNINHABITED |
| `BalancedSevenQPacketExhaustiveness287Input` | EXTERNAL / SOURCE-MISSING / UNINHABITED |
| `SmallConductorNegligible287Input` | EXTERNAL / UNINHABITED (Siegel–Walfisz metadata) |
| `ExceptionalCharacterNegligible287Input` | EXTERNAL / UNINHABITED, carries `ineffective` |

Each is refutable by explicit data (`*_not_automatic` / `*_is_a_restriction`), so none can
be discharged by generalities.

---

## E.  Required final block

```
OLD 2q/phi(q) DICTIONARY:
    RETRACTED / WRONG GEOMETRY.  Not merely labelled: refuted in Lean for every value of
    the aggregate constant (oldPointwiseLocalScalarDictionary_refuted).  Historical files
    preserved; the single-modulus sieve use of q/phi(q) is untouched.

SP2 PHYSICAL SOURCE:
    SP2BalancedSevenPhysicalComparison defined literally as
    -20 * sum_pvec Omega(pvec) [Lambda(2P+s) - 2B(P)], from the direct SP-2 source layer
    only.  Independent of the factorial q-cell.  Finite algebra PROVED.  The literal
    one-sign source identification itself remains SOURCE-MISSING.

PRINCIPAL q-CELL:
    M_phys_principal and M_fac_principal defined separately;
    principal_qCell_eq_physical_qCell PROVED for odd q (pure principal-projection algebra).
    Firewall PROVED: principal_qCell_eq_does_not_prove_full_twoB.

q-PARTITION:
    Dyadic ownership PROVED (owner, uniqueness, disjointness, cover, exact reassembly).
    Full-q / physical exhaustiveness NOT proved: BalancedSevenQPartitionInput and
    BalancedSevenQPacketExhaustiveness287Input are uninhabited.

AGGREGATE EULER LOCAL ALGEBRA:
    PROVED at w = 0: p(p-2)/(p-1)^2 off P, p/(p-1) on P, ratio (p-1)/(p-2), and
    H_P(0) = 2*S2*prod_{p|P,p>2}(p-1)/(p-2) = 2B(P) with S2 a parameter.

AGGREGATE EULER ANALYTIC INPUT:
    AggregateEulerPrincipal287Input and AggregateEulerUniformity287Input:
    EXTERNAL / UNINHABITED.  The uniform H_P(w) contour estimate is the audit's
    first residual.

SMALLCOND INPUT:
    SmallConductorNegligible287Input: EXTERNAL / UNINHABITED.  Metadata cites
    Siegel-Walfisz / uniform PNT in AP.  Not proved in Lean.

EXCEPTIONAL INPUT:
    ExceptionalCharacterNegligible287Input: EXTERNAL / UNINHABITED, kept strictly separate
    from the ordinary small conductors, with the ineffectivity flag in its type so it
    travels downstream.

EFFECTIVITY:
    BalancedSevenAsymptotic and BalancedSevenEffective are separate ledger entries.
    asymptoticBalancedSeven_not_effectiveAutomatically PROVED; ineffective exceptional
    input supplies no explicit M0 and therefore no effective WindowPairSupply threshold.

COMPARISON COMPILER:
    balancedSevenComparison_of_inputs PROVED as an implication only, concluding
    AFFINE287-MULOG-COMPARISON-LOWCOND-MATCH45 (the repository's MuLogComparisonAtCutoff)
    from BalancedSevenComparisonInputs.  Six of its fields are uninhabited external/source
    interfaces.  No inhabitant constructed.

BALANCED7 ASYMPTOTIC STATUS:
    CONDITIONAL COMPILER + EXTERNAL INPUTS.  Not closed.  Independent source audit:
    CASE F - SOURCE-MISSING, so BalancedSevenIndependentlyAudited = OPEN.
    ProComparisonCandidate = CLOSED-CANDIDATE and BalancedSevenResearchCandidate =
    CLOSED-CANDIDATE are recorded as separate, non-conflated fields.

BALANCED7 EFFECTIVE STATUS:
    OPEN.  Not derivable from the asymptotic branch.

FIRST DOWNSTREAM RESIDUAL:
    FIRST AUDIT RESIDUALS (in order):
        1. AggregateEulerUniformity287Input
        2. BalancedSevenQPacketExhaustiveness287Input
    287-FIXED-GSTAR-REMAINING-PACKET-CENSUS45 is NOT promoted to the controlling research
    residual (census_not_promoted).

ERDOS287:
    OPEN

LAKE BUILD:
    SUCCESS - 8181 jobs, 0 errors.  The V23 modules emit 0 warnings; the only warning a
    from-source rebuild reports is a pre-existing linter note in an older module
    (FixedCertificateSmoothParity).

TRUST SCAN:
    ZERO occurrences of sorry / admit / axiom / opaque / unsafe / native_decide /
    @[implemented_by] in code across all new V23 files (the words appear only inside the
    audit docstring).  #print axioms on every principal new declaration returns only
    [propext, Classical.choice, Quot.sound]; several return the smaller
    [propext, Quot.sound].
```

---

## F.  Final firewall

Research-level external audit status is **not** silently relabelled as a kernel proof: the
Pro closure candidate, the independent audit outcome and the Lean execution status are
three separate records, and the audit's verdict (`CASE F — SOURCE-MISSING`) is the one that
governs.  Ineffective asymptotics do **not** supply an effective `WindowPairSupply`
threshold.  Nothing in V23 proves Balanced7, and nothing proves Erdős #287.

```
BALANCED7 PRO CLOSURE CANDIDATE : YES
BALANCED7 INDEPENDENT SOURCE AUDIT : PENDING (CASE F — SOURCE-MISSING)
EFFECTIVE BALANCED7 : OPEN
ERDOS287 : OPEN
```
