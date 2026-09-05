# ERDŐS #287 — REGULAR-PERRON SOURCE FRONTIER / EXHAUSTIVE K0-SP2 REASSEMBLY / FCL→WINDOWPAIR CONDITIONAL BRIDGE

**Append-only safe bank.**  No existing file was deleted, renamed, weakened or
rewritten.  The only change to an existing file is the appending of ten `import`
lines at the end of the import block of `RequestProject/Main.lean`.

---

## STRICT FINAL REPORT

```
LAKE BUILD:                        PASS
NEW JOB COUNT:                     10   (8352 → 8362 jobs)

SORRYAX:                           NONE
CUSTOM AXIOMS:                     NONE
UNSAFE:                            NONE
OPAQUE / native_decide /
  implemented_by / admit:          NONE

K0-SP2 SOURCE PARTITION:           KERNEL-PROVED
UNIFORM FRAGMENTATION SOURCE
  COMPILER:                        KERNEL-PROVED SOURCE/COMBINATORIAL
                                   (previously banked; re-checked, unchanged)
REPEATED-BALANCED7 DEPTH-3
  ARITHMETIC:                      KERNEL-PROVED
REGULAR PERRON PARENT INTERFACE:   DEFINED
REGULAR PERRON ANALYTIC INPUT:     UNINHABITED
TEMPLATE REASSEMBLY IDENTITY:      KERNEL-PROVED
FCL→WINDOWPAIR:                    KERNEL-PROVED CONDITIONAL
EFFECTIVE WINDOWPAIR:              UNINHABITED
ERDOS287:                          OPEN

PROOF-CLAIM CERTIFIED:             NO

FIRST OPEN ANALYTIC NODE:
  287-K0-SP2-REGULAR-PERRON-SMOOTH-MOBIUS-CORRELATION45
```

Every principal new theorem reports exactly

```
[propext, Classical.choice, Quot.sound]
```

(or "does not depend on any axioms"), as recorded by
`RequestProject/Status/AxiomAuditErdos287RegularPerronSourceFrontier.lean`.

---

## Files added

| file | content |
|---|---|
| `RequestProject/CurrentProgramme/Erdos287K0SP2SourceObject.lean` | §1 the exact K0-SP2 source object |
| `RequestProject/CurrentProgramme/Erdos287K0SP2FourClassPartition.lean` | §2 the exhaustive four-way partition |
| `RequestProject/CurrentProgramme/Erdos287RepeatedBalanced7FiniteArithmetic.lean` | §3 the depth-3 divisor identity and coefficient table |
| `RequestProject/CurrentProgramme/Erdos287RegularPerronParent.lean` | §4 parent interface, §5 Perron reconstruction firewall |
| `RequestProject/CurrentProgramme/Erdos287RegularTemplateReassembly.lean` | §6 template reassembly and the triangle-inequality firewall |
| `RequestProject/CurrentProgramme/Erdos287Balanced7ScopeAndCauchyFirewall.lean` | §7 owner-scope firewall, §8 first-Cauchy firewall |
| `RequestProject/CurrentProgramme/Erdos287FCLErrorStrengthFirewall.lean` | §9 fixed relative saving vs arbitrary log saving |
| `RequestProject/CurrentProgramme/Erdos287FCLWindowPairBridge.lean` | §10 the conditional bridge, §11 the effectivity firewall |
| `RequestProject/Status/CurrentStatusErdos287RegularPerronSourceFrontier.lean` | §12 the new authoritative status layer |
| `RequestProject/Status/AxiomAuditErdos287RegularPerronSourceFrontier.lean` | §13 the axiom audit |

File changed (append-only): `RequestProject/Main.lean` (ten new `import` lines).

---

## §1  The exact K0-SP2 source object

`Erdos287.K0SP2Source`.

* `greatestPrimeFactor n = P⁺(n)` with `le_greatestPrimeFactor`,
  `greatestPrimeFactor_prime`.
* `K0SP2Params` carries `X` and the two exponents as rationals `σ* = snum/sden`,
  `γ* = gnum/gden`; the smoothness and truncation conditions are written in the
  equivalent **integer-power** form, so the predicates are decidable and
  `sourceSet` is a genuine `Finset`:
  `S_X = { n : X/2 < n ≤ X, P⁺(n)^sden ≤ n^snum }`.
* `MgammaCoeff n = ∑_{e ∣ n, e^gden ≤ n^gnum} μ(e)`.
* `sourceExpr`, `sectorExpr` — the two-sign source
  `∑_{s=±1} ∑_{n ∈ S_X} W(n) D_s(n) M_γ(n)` with `W`, `D` kept as explicit
  complex-valued **parameters** (no analytic property assumed).
* Finite identities proved: `sourceExpr_two_sign`, `sectorExpr_union`,
  `sectorExpr_empty`, `sourceExpr_four_sectors`.

## §2  Four-way source partition

`k0SP2_fourClass_partition_exact` bundles, for every `P : K0SP2Params` and every
largeness cutoff `L`:

* the six pairwise disjointness statements;
* `classRepeatedB7 ∪ classLargePP L ∪ classDistinctB7 L ∪ classRegular L = sourceSet`;
* `no_row_two_owners`.

Owners are applied in the fixed priority order A ▸ B ▸ C, and the regular
complement is defined by **exact set difference**
`R = S_X \ (A ∪ B ∪ C)`, so exhaustiveness is a finite-set theorem.
`k0SP2_source_four_sector_reassembly` is the corresponding exact source identity
(before any triangle inequality).

The analytic negligibility of the A and B sectors, and the ownership of C by the
banked full-`q` physical theorem, are **paper/external inputs** and are not
encoded as theorems.

## §3  Repeated-Balanced7 finite arithmetic

`Erdos287.RepeatedBalanced7`.

* `moebius_prod_primes`, `squarefree_prod_primes`,
  `moebius_eq_neg_one_pow_omega`.
* `depthMoebius n k = ∑_{e ∣ n, ω(e) ≤ k} μ(e)`.
* `depthMoebius_eq_subset_sum` — the divisor-lattice transfer for squarefree `n`
  (a genuine `Finset.sum_nbij'` between the divisors of `n` and the subsets of
  its prime support).
* `depthMoebius_eq_alternating` — `M^{(k)}(n) = ∑_{j ≤ k} (−1)^j C(r, j)`.
* `depthMoebius_three_eq_Hrepeat`, `depthMoebius_three_eq_neg_choose`:
  `M^{(3)}(P) = Hrepeat r = −C(r−1, 3)` for `r ≥ 1` (reusing the previously
  banked `Erdos287.RepeatedPrime.Hrepeat`).
* `depthMoebius_three_table`: `r = 7 → −20`, `6 → −10`, `5 → −4`, `4 → −1`,
  `1 ≤ r ≤ 3 → 0`.

**Correction recorded.**  The requested row "`r ≤ 3 → 0`" is true only for
`r ≥ 1`.  The `r = 0` case is the empty row `n = 1`, where
`M^{(3)}(1) = μ(1) = 1`; this is banked explicitly as `depthMoebius_three_one`.
The table therefore reads `1 ≤ r ≤ 3 → 0`.

The `X^{6/7}` asymptotic count is **not** formalised: it is carried as the named
external input `RepeatedBalanced7CountInput`, which is left uninhabited.

## §4  Regular Perron parent — definition only

`RegularPerronCoefficients` is an abstract coefficient structure with explicit
reconstruction fields (`vanish_off_reg`, `euler_on_reg`), standing for
`F_z^{reg}(n) = 1_R(n) n^{γ*z} ∏_{p∣n}(1 − p^{−z})` without requiring complex
exponentiation.  `correlation_eq_filter` is the support identity.

`RegularPerronSmoothMobiusCorrelationInput` states the exact remaining analytic
object as an explicit fixed-budget sufficient inequality and is
**LEFT UNINHABITED** (`regularPerronInput_not_inhabited_here`).

## §5  Perron reconstruction firewall

Three separate interfaces `PerronMainInput`, `PerronBoundaryInput`,
`PerronTruncationInput`, and a `PerronReconstruction` bundle whose
`decomposition` field is a **hypothesis**.  Only the finite algebraic
consequences are theorems: `perron_reconstruction_identity`,
`perron_reconstruction_triangle`.  No contour estimate is formalised.

## §6  Template reassembly

`TemplateFamily` carries an `X`-independent index `Fin card` and the pointwise
identity `∑_π F_{z,π}(n) = F_z^{reg}(n)`.
`template_correlation_reassembly` proves `∑_π C_{s,π} = C_s^{reg}` for **every**
finite row set (hence at every scale, with the same index family);
`template_correlation_reassembly_two_sign` is the two-sign form.

Firewall: `abs_sum_lt_sum_abs_counterexample` exhibits `‖∑‖ = 0 < 2 = ∑‖·‖`, and
`triangle_only_after_parent` records the *only* legitimate direction.
`Cfrag = 0` is banked as finite, `X`-independent metadata only.

## §7  Balanced7 owner scope firewall

`SourceScope` separates `directBalanced7` from `regularPerron`
(`scope_separation`).  A regular row reaches the direct owner **only** through
`Balanced7BoxAdapter`, which literally supplies the seven singleton prime-box
fields (`directBalanced7_of_adapter`).  The generic identification
`GenericRegularTemplateToBalanced7Adapter` is proved **uninhabited**
(`genericAdapter_uninhabited`).  `same_shape → owner` is refuted:
`same_shape_does_not_determine_row` (510510 vs 570570, both `ω = 7`) and
`shape_only_boxes_impossible`.

## §8  First-Cauchy firewall

`CauchyStatus` separates `preCauchySigned` from `postCauchySquared`.
`LinearSmallPrefixFactorisation` records structurally that the proposed regular
parent factorisation is **linear** in the small-prefix Möbius/Perron
coefficient.  The algebraic sign-consumption identities are proved
(`sign_consumed_by_modulus`, `cancellation_lost_after_cauchy`).  The claim that
the post-Cauchy object is analytically insufficient is recorded as
`ClaimStatus.researchMetadata`, **not** as a kernel theorem
(`postCauchyInsufficiency_is_metadata`).

## §9  FCL error-strength firewall

`ArbitraryLogSaving` (all `A`) and `FixedRelativeSaving δ` are separated, and
`fixedRelativeSaving_not_arbitraryLogSaving` shows they differ.
`finiteCompiler_consumes_only_fixed_relative_saving` re-exports the banked
finite FCL compiler with hypotheses `E ≤ δ·B` and `3δ < 1 + C_c` only — no
all-`A` hypothesis appears anywhere in the statement.  The analytic
relative-smallness premise is **not constructed**
(`fixedRelativeSaving_premise_not_supplied`).

## §10  Conditional FCL → WindowPair bridge

`SupportedWeight` — a fixed nonnegative weight supported in `[7/10, 9/10]`.

`PositiveFCLPrimeMassWitness M` — the conditional input at the scale `X = M/2`:
a prime `q` with `7M ≤ 20q ≤ 9M` (the integer form of
`q ∈ [(7/10)X, (9/10)X]`), a sign `s`, and `2q + s = r^a` with `r` prime,
`a ≥ 1` (the form of `Λ(2q+s) > 0`).

**`windowPairSupply_of_positiveFCLMass`** — for `M ≥ 20`, the witness yields the
literal `Erdos287.WindowPairSupply M`.  Every field is discharged:

```
PLUS  case:  x = 2q,     p_u = q, a_u = 1,  p_v = r, a_v = a;
MINUS case:  x = 2q − 1, p_u = r, a_u = a,  p_v = q, a_v = 1;
```

primality of both bases; positivity of both exponents; both divisibilities;
both windows `≤ 9`; both `CVal` inequalities; `M ≤ 2x`; `x + 1 ≤ M`.

The theorem is **CONDITIONAL**: the positivity input is a hypothesis and is not
constructed.  Non-vacuity is checked at `M = 20` (`witnessTwenty`, `q = 7`,
`2q − 1 = 13`).

## §11  Effectivity firewall

`AsymptoticWindowPairSupply` uses an existential **real** threshold;
`EffectiveWindowPairSupply` (previously banked) carries a `Nat` threshold as
data, and `Bounded` (`M₀ ≤ 4·10⁹`) is a separate predicate.
`asymptotic_does_not_give_bounded_effective` shows the conversion is unavailable
without supplying the constants.  Building the effective object would require a
*uniform* witness for all `M ≥ M₀`
(`effectiveWindowPairSupply_needs_uniform_witness`), which is **not supplied**.
`EffectiveWindowPairSupply` remains **UNINHABITED**.

## §12  Updated authoritative frontier

`RequestProject/Status/CurrentStatusErdos287RegularPerronSourceFrontier.lean`
appends the layer `regularPerronSourceFrontier`, strictly later than
`dualLevelSimultaneousCritical`
(`regularPerronSourceFrontier_is_later`); the earlier layer is retained and
re-checked (`historical_layers_retained`), never deleted.  Rows as in the strict
final report above; `no_row_is_a_proof_claim` records that no ledger value is a
proof of #287.

---

## Explicit non-claims

* Erdős #287 is **not** proved, and nothing here asserts it.
* No external analytic estimate is inhabited.
* No arbitrary-`L^{-A}` theorem is formalised.
* Metadata status values carry **no** mathematical force.
