# ERDŐS #287 — SP-2 DIRECT BALANCED7 SOURCE REPAIR / ANALYTIC CLOSURE SAFE BANK REPORT

`BALANCED7-SP2-DIRECT-PACKET45` / `BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45`

Append-only continuation of V20 + V21 + V22.  Nothing earlier was deleted or rewritten;
`ARISTOTLE_SUMMARY.md` was not modified.

---

## A. Source forensics — what the repository actually contains

A direct search for the Ford canonical split (`G_*(m;n)`, `H_*(n) = ∑_{m ∣ n} G_*(m;n)`)
returns **no** Lean object.  What the repository *does* carry, in
`RequestProject/Erdos287/FixedCertificateSmoothParity.lean`, is the fixed smooth-parity
certificate:

```
Erdos287.SmoothParity.truncMobius n T = ∑_{d ∣ n, d ≤ T} μ(d)
Erdos287.SmoothParity.FixedCertificateSmoothParityPacket sector Hs cut f E
```

whose `cell_identity` field is exactly the `k = 0`, `J = ∅` cell obligation.  Together
with the V21 finding that there is no physical `ω_i(p)` anywhere, this shows the
Ford-(7.23) coefficient family banked in V22 is **not** the literal Balanced7 source
dictionary.

Consequence, recorded as machine status data
(`Erdos287.SP2Status.fm723_adapter_retracted`):

```
BALANCED7-OMEGA-FM723-SOURCE-ADAPTER45 : RETRACTED / NOT THE LITERAL SOURCE
BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45 : SOURCE_OPEN / CONTROLLING
```

The V22 adapter file is preserved unchanged.

---

## B. The SP-2 fixed-certificate packet

File: `RequestProject/Erdos287/SP2DirectSourceAdapter3221.lean` (namespace
`Erdos287.SP2Source`).

`SP2FixedCertificateData` carries the packet metadata

```
k = 0,   J = ∅,   Ω(n) = 7,   r = 3,   s = ±1,   λ = fixed smooth prime-box cell,
```

and `SP2PacketNormalization` states the finite conditions.  Unlike the analytic
interfaces, this metadata is *consistent*: `sp2_packet_metadata_inhabited` exhibits a
datum satisfying it.

`sp2_fixedCertificate_divisorSum` states, **conditionally on the packet's `cell_identity`
field**, that `H_*(n) = ∑_{d ∣ n, d ≤ cut n} μ(d)`.  The field itself is not discharged:
the source identity remains `SOURCE_OPEN`.

---

## C. The divisor depth `r = 3`

Proved (real-exponent arithmetic, no analysis assumed):

* `sp2_threeSeventh_lt_half : 3/7 < 1/2` and `sp2_half_lt_fourSeventh : 1/2 < 4/7`;
* `balancedSeven_threeFactor_below_cutoff` — a divisor of size `≤ Y³` satisfies
  `d ≤ n^{3/7}` whenever `Y⁷ ≤ n` and `Y ≥ 1`, so it survives the `n^{1/2−ε}` truncation;
* `balancedSeven_fourFactor_above_cutoff` — a divisor of size `≥ Y⁴` satisfies
  `n^{1/2} < d` whenever `Y ≥ 256` and `n ≤ 128 Y⁷` (the dyadic bound for a product of
  seven primes in `[Y, 2Y)`), so it is killed by the truncation.

Together these pin the divisor depth of the SP-2 packet at exactly `r = 3`.

Finite bookkeeping (kernel-decidable):

* `sp2_balancedSeven_subsetSizes` — `#{S ⊆ Fin 7 : |S| ≤ 3} = 64`;
* `sp2_divisorLattice_split` — `64 + 64 = 128`;
* `sp2_balancedSeven_coefficient_eq_neg20` — `∑_{j=0}^{3} (−1)^j C(7,j) = 1 − 7 + 21 − 35 = −20`.

---

## D. The literal prime-box weights `V_{i,λ}` — the actual repair

File: `RequestProject/Erdos287/SP2PrimeBoxWeights3221.lean` (namespace
`Erdos287.SP2PrimeBox`).

```
sp2Omega C i p  =  1  if p ∈ λ_i,  else 0
```

Because this is a literal normalised prime indicator, the pointwise coefficient law is a
**theorem**:

* `sp2Omega_norm_le_one : ‖ω_i(p)‖ ≤ 1`,
* `sp2Omega_eq_one_of_mem`, `sp2Omega_eq_zero_of_not_mem`,
* `sp2Omega_l1_eq_card : ∑_{p ∈ λ_i} ‖ω_i(p)‖ = #λ_i` — no hidden inflation, so the only
  thing left to estimate is the prime count.

This is the substantive difference from V22: the pointwise bound is no longer an assumed
interface field.  It is **not** derived from the abstract factorial polarisation theorem —
the circular provenance route V21 flagged is not used.

What remains open is only the *identification*
`BalancedSevenOmegaSP2DirectSourceAdapter3221` (physical slot `=` `V_{i,λ}`), which is
uninhabited (`sp2Adapter_not_automatic`), and the external prime count.

`sp2_primeBoxL1_of_adapter : adapter + prime count ⇒ BalancedSevenPrimeBoxNormalization3221 Dat 1 C1 Y`.

Ownership firewall re-derived for SP-2: `sp2_outerInner_disjoint`, `sp2_outerInner_cover`,
`sp2_no_primeDensity_doubleSpend`, `sp2_block_cardinalities` (2 outer + 5 inner = 7).

---

## E. The SP-2 closure arithmetic

File: `RequestProject/Erdos287/SP2ClosureCompiler3221.lean` (namespace
`Erdos287.SP2Closure`).

`sp2B0 = 1`, i.e. the single shared cutoff `D = log X` (`sp2_cutoff_eq_log`), and hence,
through the *repaired safe* `(D+1)²` bad-character count and the V22 ledger,

```
C_var(1) = 5                                    (sp2_cvar_eq_five)
netLogExponent(5, 0) = −(2+5)/2 + 0 = −7/2      (sp2_netLogExponent_eq_neg_seven_halves)
−7/2 < −1                                       (sp2_netLogExponent_lt_neg_one)
```

so *if* the physical log-prefactor audit returns `C_ext = 0`, the Balanced7 error is
`o(X/log X)`.  The contingency is made explicit both ways:

* `sp2_closure_margin` — the route still closes for every `C_ext < 5/2`;
* `sp2_closure_fails_without_audit` — it does **not** close if `C_ext ≥ 5/2`.

`PhysicalLogPrefactorSP23221` (the claim `C_ext = 0`) is a `structure`, uninhabited
(`sp2PhysicalLogPrefactor_not_automatic`): `SOURCE_OPEN`.

`SP2AnalyticClosure3221Inputs` bundles the SP-2 dictionary, the prime count, the sieve and
Shiu interfaces, the outer `L²` input, the `B0 = 1` shared-cutoff firewall, the prefactor
audit and the numeric budget layer.  `sp2_closes_logVar` yields the log-variance interface
plus the strict closure inequality.  `sp2_supplies_primeBoxL1` records that the package
supplies the `L¹` normalisation only because it assumes its two antecedents.

---

## F. Balanced7 compiler and provenance

`balancedSeven_of_SP2_analytic_and_comparison` routes

```
SP-2 analytic closure package + first-Cauchy prefactor certificate
  + same-cutoff physical comparison   ⇒   BalancedSevenPacketInput
```

through the existing `Erdos287.V19Compiler.balancedSeven_of_highCondLogVar`.  The
comparison antecedent is independent and uninhabited, so **BALANCED7 remains OPEN**.

Provenance and anti-circularity:

* `sp2_adapter_is_independent_of_ford723` — explicit data where the SP-2 identification
  holds while a Ford dictionary fails, the formal side of the FM723 retraction;
* `sp2Closure_not_automatic`, `sp2Closure_cannot_construct_comparison`,
  `sp2_does_not_prove_balancedSeven`.

---

## G. Dual status and the new frontier

```
SP-2 route, externally audited analytic reading : CLOSED (claim of the external audit)
SP-2 route, Lean status                          : CONDITIONAL COMPILER, inputs OPEN
```

Only the second is certified here.  With the two-projector package's own source pins now
either discharged (pointwise law) or made explicitly conditional, the residual order
becomes (`Erdos287.SP2Status.residualRank`):

1. `COMPARISON-SMALLCOND-EXCEPTIONAL-SPLICE45 : SOURCE_OPEN`  ← first exact residual
2. `BALANCED7-OMEGA-SP2-DIRECT-SOURCE-ADAPTER45 : SOURCE_OPEN`
3. `3221-PHYSICAL-LOG-PREFAC45 : SOURCE_OPEN`
4. `3221-HIGHPROJECTOR-CUTOFF-COMPAT45 : SOURCE_OPEN`

---

## REQUIRED FINAL BLOCK

```
FILES ADDED:
RequestProject/Erdos287/SP2DirectSourceAdapter3221.lean
RequestProject/Erdos287/SP2PrimeBoxWeights3221.lean
RequestProject/Erdos287/SP2ClosureCompiler3221.lean
RequestProject/Status/Erdos287SP2Status.lean
RequestProject/Status/AxiomAuditErdos287SP2.lean
ERDOS287_SP2_DIRECT_BALANCED7_SAFE_BANK_REPORT.md

FILES MODIFIED:
RequestProject/Main.lean   (import lines appended only)

V20 / V21 / V22 PRESERVED:
YES

FM723 SOURCE ADAPTER:
RETRACTED / NOT THE LITERAL SOURCE — file preserved, status data only

SP-2 DIRECT SOURCE ADAPTER:
SOURCE_OPEN / CONTROLLING / UNINHABITED

SP-2 FIXED CERTIFICATE DIVISOR SUM:
CONDITIONAL ON THE SMOOTH-PARITY cell_identity FIELD (SOURCE_OPEN)

DIVISOR DEPTH r = 3:
PROVED (balancedSeven_threeFactor_below_cutoff / balancedSeven_fourFactor_above_cutoff)

SUBSET SIZES / ALTERNATING COEFFICIENT:
FINITE PASS — 64 of 128 divisors; ∑_{j≤3} (−1)^j C(7,j) = −20

PRIMEBOX POINTWISE LAW |omega_i(p)| ≤ 1:
PROVED for the literal SP-2 weight V_{i,λ} (not inferred from factorial polarization)

PRIMEBOX L1 NORMALIZATION:
CONDITIONAL — needs only the external prime count

BAD-CHARACTER SAFE COUNT:
FINITE PASS — #Bad ≤ (D+1)^2

CUTOFF:
B0 = 1, D = log X, single shared cutoff

PHYSICAL LOG PREFACTOR (C_ext = 0):
SOURCE_OPEN / UNINHABITED

SHIU INTERFACE:
EXTERNAL ANALYTIC INTERFACE / UNINHABITED

SHORT-t SIEVE INTERFACE:
EXTERNAL ANALYTIC INTERFACE / UNINHABITED

OUTER TWO-PRIME L2:
EXTERNAL ANALYTIC INTERFACE / UNINHABITED

C_var(1):
5

NET LOG EXPONENT:
−(2 + C_var)/2 + C_ext = −7/2 < −1  (kernel-checked, contingent on C_ext = 0)

TWO-PROJECTOR CLOSURE:
CONDITIONAL

3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45:
OPEN / CONDITIONAL

SIXTH MOMENT:
OPEN STRONGER SUFFICIENT FALLBACK

COMPARISON:
SOURCE_OPEN

BALANCED7:
OPEN

ERDOS287:
OPEN

FIRST EXACT RESIDUAL:
COMPARISON-SMALLCOND-EXCEPTIONAL-SPLICE45 : SOURCE_OPEN

LAKE BUILD:
SUCCESS — 8171 jobs, 0 errors; SP-2 modules emit 0 warnings

TRUST SCAN:
ZERO occurrences of sorry / admit / axiom / opaque / unsafe / native_decide /
@[implemented_by] in all new SP-2 files; #print axioms on every principal declaration
returns only [propext, Classical.choice, Quot.sound]

PUBLIC-MAIN SYNC:
RequestProject/Main.lean extended with the SP-2 imports only; full build clean
```

### FINAL FIREWALL

```
No source-open or external analytic interface was inhabited merely to make
the compiler execute.

No statement in the SP-2 bank proves Erdős #287.

No statement in the SP-2 bank proves Balanced7 unless the explicit analytic/source
antecedents — the SP-2 source identification, the prime count, the sieve and Shiu
inputs, the C_ext = 0 audit and the comparison splice — are separately supplied.
```
